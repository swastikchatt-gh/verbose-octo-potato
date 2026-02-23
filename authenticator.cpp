#include <QtWidgets>
#include <QtGui>
#include <QtCore/QLockFile>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <openssl/hmac.h>
#include <openssl/sha.h>
#include <sodium.h>
#include <zbar.h>
#include <cstdint>
#include <vector>
#include <string>
#include <stdexcept>
#include <cstring>
#include <memory>
#include <sys/prctl.h>      // for core dump control
#include <unistd.h>          // for prctl constants

// -------------------------------------------------------------------
// Secure memory utilities (libsodium-backed)
// -------------------------------------------------------------------
template<typename T>
class SecureBuffer {
private:
    T* data_;
    size_t size_;
public:
    SecureBuffer(size_t size) : data_(nullptr), size_(size) {
        data_ = static_cast<T*>(sodium_malloc(size_ * sizeof(T)));
        if (!data_) throw std::bad_alloc();
        if (sodium_mlock(data_, size_ * sizeof(T)) < 0) {
            sodium_free(data_);
            throw std::runtime_error("Could not mlock secure memory");
        }
    }
    ~SecureBuffer() noexcept {
        if (data_) {
            sodium_memzero(data_, size_ * sizeof(T));
            sodium_munlock(data_, size_ * sizeof(T));
            sodium_free(data_);
            data_ = nullptr;
            size_ = 0;
        }
    }

    // Disable copying
    SecureBuffer(const SecureBuffer&) = delete;
    SecureBuffer& operator=(const SecureBuffer&) = delete;

    // Enable moving
    SecureBuffer(SecureBuffer&& other) noexcept
        : data_(other.data_), size_(other.size_) {
        other.data_ = nullptr;
        other.size_ = 0;
    }
    SecureBuffer& operator=(SecureBuffer&& other) noexcept {
        if (this != &other) {
            this->~SecureBuffer();
            data_ = other.data_;
            size_ = other.size_;
            other.data_ = nullptr;
            other.size_ = 0;
        }
        return *this;
    }

    T* data() { return data_; }
    const T* data() const { return data_; }
    size_t size() const { return size_; }
    void zero() { if (data_) sodium_memzero(data_, size_ * sizeof(T)); }
};

// SecureVector: a std::vector that wipes its contents on destruction
template<typename T>
class SecureVector : public std::vector<T> {
public:
    using std::vector<T>::vector;
    ~SecureVector() {
        if (!this->empty())
            sodium_memzero(this->data(), this->size() * sizeof(T));
    }
    // Disable copy, enable move
    SecureVector(const SecureVector&) = delete;
    SecureVector& operator=(const SecureVector&) = delete;
    SecureVector(SecureVector&&) = default;
    SecureVector& operator=(SecureVector&&) = default;
};

// -------------------------------------------------------------------
// Configuration Constants
// -------------------------------------------------------------------
constexpr size_t MAX_ACCOUNTS = 10000;
constexpr size_t MAX_SECRET_SIZE = 256;
constexpr size_t MAX_ACCOUNT_NAME_LEN = 256;
constexpr size_t MAX_BASE32_SECRET_LEN = 1024;
constexpr int VALID_DIGITS_MIN = 6;
constexpr int VALID_DIGITS_MAX = 8;
constexpr int VALID_STEP_MIN = 1;
constexpr int VALID_STEP_MAX = 300;
constexpr int AUTO_LOCK_TIMEOUT_MS = 300000; // 5 minutes
constexpr int MAX_IMAGE_WIDTH = 4000;
constexpr int MAX_IMAGE_HEIGHT = 4000;

// -------------------------------------------------------------------
// Utility: zeroize and clear a QString/QByteArray/QLineEdit
// -------------------------------------------------------------------
// Note: QString zeroing is best‑effort – Qt may keep internal copies.
inline void safe_zero_and_clear(QString& str) {
    if (str.size() > 0) sodium_memzero((void*)str.data(), str.size()*sizeof(QChar));
    str.clear();
}
inline void safe_zero_and_clear(QByteArray& arr) {
    if (arr.size() > 0) sodium_memzero(arr.data(), arr.size());
    arr.clear();
}
inline void safe_zero_and_clear(QLineEdit* edit) {
    QString str = edit->text();
    safe_zero_and_clear(str);
    edit->clear();
}
inline void safe_zero_and_clear(QClipboard *clip) {
    if (clip) clip->clear(QClipboard::Clipboard);
}

// -------------------------------------------------------------------
// Cryptographically secure random (libsodium)
// -------------------------------------------------------------------
std::vector<uint8_t> random_bytes(size_t count) {
    std::vector<uint8_t> buf(count);
    randombytes_buf(buf.data(), count);
    return buf;
}

// -------------------------------------------------------------------
// Base32 decoding, strictly validating for RFC 4648
// -------------------------------------------------------------------
static int b32_val(char c) {
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= '2' && c <= '7') return c - '2' + 26;
    return -1;
}

std::unique_ptr<SecureBuffer<uint8_t>> base32_decode(const QString &base32_in) {
    QString base32 = base32_in.trimmed().toUpper();
    QByteArray b32 = base32.toLatin1();
    size_t b32_len = b32.length();

    if (b32_len == 0 || b32_len > MAX_BASE32_SECRET_LEN) {
        safe_zero_and_clear(base32);
        safe_zero_and_clear(b32);
        throw std::runtime_error("Base32 secret too long or zero");
    }

    size_t valid_data = 0, pad = 0;
    for (size_t i = 0; i < b32_len; ++i) {
        char c = b32[i];
        if (c == '=') {
            pad = b32_len - i;
            for (size_t j = i; j < b32_len; ++j) {
                if (b32[j] != '=') {
                    safe_zero_and_clear(base32);
                    safe_zero_and_clear(b32);
                    throw std::runtime_error("Invalid base32 padding sequence");
                }
            }
            break;
        } else if (!(('A' <= c && c <= 'Z') || ('2' <= c && c <= '7'))) {
            safe_zero_and_clear(base32);
            safe_zero_and_clear(b32);
            throw std::runtime_error("Invalid base32 character");
        }
        ++valid_data;
    }

    static const int decode_map[9] = {0, 0, 1, 1, 2, 3, 3, 4, 5};
    size_t full_blocks = valid_data / 8;
    size_t leftover_in = valid_data % 8;

    size_t decoded_size = full_blocks * 5 + decode_map[leftover_in];
    if (decoded_size > MAX_SECRET_SIZE) {
        safe_zero_and_clear(base32);
        safe_zero_and_clear(b32);
        throw std::runtime_error("Decoded secret too large");
    }
    auto result = std::make_unique<SecureBuffer<uint8_t>>(decoded_size);

    int buffer = 0, bits_left = 0, out_idx = 0;
    for (size_t i = 0; i < valid_data; ++i) {
        int val = b32_val(b32[i]);
        buffer = (buffer << 5) | val;
        bits_left += 5;
        if (bits_left >= 8) {
            if ((size_t)out_idx >= decoded_size) {
                safe_zero_and_clear(base32);
                safe_zero_and_clear(b32);
                throw std::runtime_error("Base32 decode overflow");
            }
            result->data()[out_idx++] = (buffer >> (bits_left - 8)) & 0xFF;
            bits_left -= 8;
        }
    }
    buffer = bits_left = out_idx = 0;
    safe_zero_and_clear(base32);
    safe_zero_and_clear(b32);
    return result;
}

// -------------------------------------------------------------------
// Algorithm enumeration (constant‑time friendly)
// -------------------------------------------------------------------
enum class Algorithm { SHA1, SHA256, SHA512 };

QString algorithmToString(Algorithm algo) {
    switch (algo) {
        case Algorithm::SHA1:   return "SHA1";
        case Algorithm::SHA256: return "SHA256";
        case Algorithm::SHA512: return "SHA512";
    }
    return "SHA1"; // fallback
}

Algorithm algorithmFromString(const QString& s) {
    if (s == "SHA256") return Algorithm::SHA256;
    if (s == "SHA512") return Algorithm::SHA512;
    return Algorithm::SHA1;
}

// -------------------------------------------------------------------
// HMAC using OpenSSL (internal use)
// -------------------------------------------------------------------
void hmac_sha1(const uint8_t *key, size_t key_len,
               const uint8_t *message, size_t msg_len,
               uint8_t *output) {
    unsigned int output_len = SHA_DIGEST_LENGTH;
    HMAC(EVP_sha1(), key, key_len, message, msg_len, output, &output_len);
}

void hmac_sha256(const uint8_t *key, size_t key_len,
                 const uint8_t *message, size_t msg_len,
                 uint8_t *output) {
    unsigned int output_len = SHA256_DIGEST_LENGTH;
    HMAC(EVP_sha256(), key, key_len, message, msg_len, output, &output_len);
}

void hmac_sha512(const uint8_t *key, size_t key_len,
                 const uint8_t *message, size_t msg_len,
                 uint8_t *output) {
    unsigned int output_len = SHA512_DIGEST_LENGTH;
    HMAC(EVP_sha512(), key, key_len, message, msg_len, output, &output_len);
}

// -------------------------------------------------------------------
// HOTP generation (RFC 4226)
// -------------------------------------------------------------------
uint32_t hotp(const uint8_t *secret, size_t secret_len,
              uint64_t counter, Algorithm algorithm, int digits) {
    if (digits < 1 || digits > 9) throw std::runtime_error("Digits must be 1-9");
    uint8_t msg[8];
    for (int i = 0; i < 8; ++i) msg[7 - i] = (counter >> (8 * i)) & 0xFF;
    uint8_t h[64];
    size_t hmac_len = 0;

    switch (algorithm) {
        case Algorithm::SHA256:
            hmac_sha256(secret, secret_len, msg, 8, h);
            hmac_len = SHA256_DIGEST_LENGTH;
            break;
        case Algorithm::SHA512:
            hmac_sha512(secret, secret_len, msg, 8, h);
            hmac_len = SHA512_DIGEST_LENGTH;
            break;
        default:
            hmac_sha1(secret, secret_len, msg, 8, h);
            hmac_len = SHA_DIGEST_LENGTH;
            break;
    }

    int offset = h[hmac_len - 1] & 0x0F;
    uint32_t code = (h[offset] & 0x7F) << 24
                  | (h[offset + 1] & 0xFF) << 16
                  | (h[offset + 2] & 0xFF) << 8
                  | (h[offset + 3] & 0xFF);

    uint32_t mod = 1;
    for (int i = 0; i < digits; ++i) mod *= 10; // digits ≤ 8 → safe

    sodium_memzero(h, sizeof(h));
    sodium_memzero(msg, sizeof(msg));
    return code % mod;
}

// -------------------------------------------------------------------
// TOTP generation (RFC 6238)
// -------------------------------------------------------------------
uint32_t totp(const uint8_t *secret, size_t secret_len,
              uint64_t time_now, int step,
              Algorithm algorithm, int digits) {
    uint64_t counter = time_now / step;
    return hotp(secret, secret_len, counter, algorithm, digits);
}

// -------------------------------------------------------------------
// Key derivation using Argon2id (SENSITIVE)
// -------------------------------------------------------------------
std::unique_ptr<SecureBuffer<uint8_t>> derive_key(const SecureBuffer<char>& password,
                                                  const std::vector<uint8_t>& salt) {
    auto key = std::make_unique<SecureBuffer<uint8_t>>(32);
    if (crypto_pwhash(key->data(), key->size(),
                      password.data(), password.size(),
                      salt.data(),
                      crypto_pwhash_OPSLIMIT_SENSITIVE,
                      crypto_pwhash_MEMLIMIT_SENSITIVE,
                      crypto_pwhash_ALG_ARGON2ID13) != 0) {
        throw std::runtime_error("Argon2id failed");
    }
    return key;
}

// -------------------------------------------------------------------
// Constant-time comparison (4-byte, secure use)
// -------------------------------------------------------------------
bool constant_time_compare_32(const uint8_t *a, const uint8_t *b) {
    uint32_t cmp = 0;
    for (int i = 0; i < 4; ++i)
        cmp |= a[i] ^ b[i];
    return cmp == 0;
}

// -------------------------------------------------------------------
// HMAC-SHA256 (for file integrity)
// -------------------------------------------------------------------
SecureVector<uint8_t> hmac_sha256(const SecureBuffer<uint8_t>& key,
                                  const uint8_t* data, size_t len) {
    SecureVector<uint8_t> mac(SHA256_DIGEST_LENGTH);
    unsigned int out_len;
    HMAC(EVP_sha256(), key.data(), key.size(), data, len, mac.data(), &out_len);
    return mac;
}

// -------------------------------------------------------------------
// ChaCha20-Poly1305 encryption (OpenSSL)
// -------------------------------------------------------------------
std::vector<uint8_t> chacha20_poly1305_encrypt(const SecureBuffer<uint8_t>& key,
                                               const uint8_t* plaintext, size_t plaintext_len,
                                               const std::vector<uint8_t>& aad,
                                               std::vector<uint8_t>& nonce_out) {
    nonce_out = random_bytes(12);
    EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
    if (!ctx) throw std::runtime_error("Failed to create cipher context");

    std::vector<uint8_t> ciphertext(plaintext_len);
    std::vector<uint8_t> tag(16);
    int len = 0, ciphertext_len = 0;

    if (1 != EVP_EncryptInit_ex(ctx, EVP_chacha20_poly1305(), nullptr, key.data(), nonce_out.data())) {
        EVP_CIPHER_CTX_free(ctx);
        throw std::runtime_error("Failed to initialize encryption");
    }
    if (!aad.empty()) {
        if (1 != EVP_EncryptUpdate(ctx, nullptr, &len, aad.data(), aad.size())) {
            EVP_CIPHER_CTX_free(ctx);
            throw std::runtime_error("Failed to add AAD");
        }
    }
    if (1 != EVP_EncryptUpdate(ctx, ciphertext.data(), &len, plaintext, plaintext_len)) {
        EVP_CIPHER_CTX_free(ctx);
        throw std::runtime_error("Encryption failed");
    }
    ciphertext_len = len;
    if (1 != EVP_EncryptFinal_ex(ctx, ciphertext.data() + len, &len)) {
        EVP_CIPHER_CTX_free(ctx);
        throw std::runtime_error("Failed to finalize encryption");
    }
    ciphertext_len += len;
    ciphertext.resize(ciphertext_len);

    if (1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_GET_TAG, tag.size(), tag.data())) {
        EVP_CIPHER_CTX_free(ctx);
        throw std::runtime_error("Failed to get tag");
    }
    EVP_CIPHER_CTX_free(ctx);

    ciphertext.insert(ciphertext.end(), tag.begin(), tag.end());
    return ciphertext;
}

std::unique_ptr<SecureBuffer<uint8_t>> chacha20_poly1305_decrypt(
    const SecureBuffer<uint8_t>& key,
    const std::vector<uint8_t>& ciphertext_with_tag,
    const std::vector<uint8_t>& nonce,
    const std::vector<uint8_t>& aad) {

    if (ciphertext_with_tag.size() < 16)
        throw std::runtime_error("Invalid ciphertext");

    size_t text_len = ciphertext_with_tag.size() - 16;
    // Use SecureVector to guarantee wiping even if exception thrown
    SecureVector<uint8_t> ciphertext(ciphertext_with_tag.begin(),
                                      ciphertext_with_tag.begin() + text_len);
    SecureVector<uint8_t> tag(ciphertext_with_tag.begin() + text_len,
                              ciphertext_with_tag.end());

    EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
    if (!ctx) throw std::runtime_error("Failed to create cipher context");

    auto plaintext = std::make_unique<SecureBuffer<uint8_t>>(text_len);
    int len = 0, plaintext_len = 0;

    if (1 != EVP_DecryptInit_ex(ctx, EVP_chacha20_poly1305(), nullptr, key.data(), nonce.data())) {
        EVP_CIPHER_CTX_free(ctx);
        throw std::runtime_error("Failed to initialize decryption");
    }
    if (1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_TAG, tag.size(),
                                 const_cast<uint8_t*>(tag.data()))) {
        EVP_CIPHER_CTX_free(ctx);
        throw std::runtime_error("Failed to set tag");
    }
    if (!aad.empty()) {
        if (1 != EVP_DecryptUpdate(ctx, nullptr, &len, aad.data(), aad.size())) {
            EVP_CIPHER_CTX_free(ctx);
            throw std::runtime_error("Failed to add AAD");
        }
    }
    if (1 != EVP_DecryptUpdate(ctx, plaintext->data(), &len, ciphertext.data(), ciphertext.size())) {
        EVP_CIPHER_CTX_free(ctx);
        throw std::runtime_error("Decryption failed");
    }
    plaintext_len = len;

    if (1 != EVP_DecryptFinal_ex(ctx, plaintext->data() + len, &len)) {
        EVP_CIPHER_CTX_free(ctx);
        throw std::runtime_error("Authentication failed");
    }
    plaintext_len += len;
    if ((size_t)plaintext_len != text_len) {
        EVP_CIPHER_CTX_free(ctx);
        throw std::runtime_error("Decrypted size mismatch - possible tampering");
    }
    EVP_CIPHER_CTX_free(ctx);
    return plaintext;
}

// -------------------------------------------------------------------
// QR code scanning with size validation
// -------------------------------------------------------------------
QString scanQRFromImage(const QImage &image) {
    if (image.width() > MAX_IMAGE_WIDTH || image.height() > MAX_IMAGE_HEIGHT)
        throw std::runtime_error("QR image too large");

    QImage grey = image.convertToFormat(QImage::Format_Grayscale8);
    zbar::Image zbarImage(grey.width(), grey.height(), "Y800",
                          grey.bits(), grey.sizeInBytes());

    zbar::ImageScanner scanner;
    scanner.set_config(zbar::ZBAR_QRCODE, zbar::ZBAR_CFG_ENABLE, 1);
    scanner.scan(zbarImage);

    QString result;
    for (auto symbol = zbarImage.symbol_begin(); symbol != zbarImage.symbol_end(); ++symbol) {
        if (symbol->get_type() == zbar::ZBAR_QRCODE) {
            result = QString::fromStdString(symbol->get_data());
            break;
        }
    }
    return result;
}

// -------------------------------------------------------------------
// Parse otpauth:// URI with strict validation
// -------------------------------------------------------------------
struct OtpAuthInfo {
    QString type;
    QString label;
    QString secret;
    Algorithm algorithm;
    int digits;
    int counter;
    int step;
    bool valid = false;
};
OtpAuthInfo parseOtpauthUri(const QString &uri) {
    OtpAuthInfo info;
    QUrl url(uri);
    if (url.scheme() != "otpauth") return info;
    info.type = url.host();
    if (info.type != "totp" && info.type != "hotp") return info;

    info.label = url.path().mid(1);
    if (info.label.isEmpty() || info.label.size() > (int)MAX_ACCOUNT_NAME_LEN) return info;
    QUrlQuery query(url.query());
    info.secret = query.queryItemValue("secret");
    if (info.secret.isEmpty() || info.secret.size() > (int)MAX_BASE32_SECRET_LEN) return info;

    info.algorithm = Algorithm::SHA1;
    if (query.hasQueryItem("algorithm")) {
        QString algo = query.queryItemValue("algorithm");
        info.algorithm = algorithmFromString(algo);
    }

    info.digits = 6;
    if (query.hasQueryItem("digits")) {
        info.digits = query.queryItemValue("digits").toInt();
        if (info.digits < VALID_DIGITS_MIN || info.digits > VALID_DIGITS_MAX) return info;
    }
    info.step = 30;
    info.counter = 0;
    if (info.type == "hotp" && query.hasQueryItem("counter")) {
        info.counter = query.queryItemValue("counter").toInt();
        if (info.counter < 0) return info;
    } else if (info.type == "totp" && query.hasQueryItem("period")) {
        info.step = query.queryItemValue("period").toInt();
        if (info.step < VALID_STEP_MIN || info.step > VALID_STEP_MAX) return info;
    }
    info.valid = true;
    return info;
}

// -------------------------------------------------------------------
// Secure password dialog
// -------------------------------------------------------------------
class SecurePasswordDialog : public QDialog {
    Q_OBJECT
private:
    QLineEdit *passwordEdit;

public:
    SecurePasswordDialog(QWidget *parent = nullptr) : QDialog(parent) {
        setWindowTitle("Master Password");
        setModal(true);
        setWindowFlags(windowFlags() | Qt::WindowStaysOnTopHint);

        QVBoxLayout *layout = new QVBoxLayout(this);
        QLabel *label = new QLabel("Enter master password:");
        layout->addWidget(label);

        passwordEdit = new QLineEdit;
        passwordEdit->setEchoMode(QLineEdit::Password);
        layout->addWidget(passwordEdit);

        QHBoxLayout *buttonLayout = new QHBoxLayout;
        QPushButton *okButton = new QPushButton("OK");
        QPushButton *cancelButton = new QPushButton("Cancel");
        buttonLayout->addWidget(okButton);
        buttonLayout->addWidget(cancelButton);
        layout->addLayout(buttonLayout);

        connect(okButton, &QPushButton::clicked, this, &QDialog::accept);
        connect(cancelButton, &QPushButton::clicked, this, &QDialog::reject);
    }

    std::unique_ptr<SecureBuffer<char>> getSecurePassword() {
        int result = exec();
        if (result != QDialog::Accepted) {
            safe_zero_and_clear(passwordEdit);
            return nullptr;
        }
        QByteArray passwordUtf8 = passwordEdit->text().toUtf8();
        auto securePass = std::make_unique<SecureBuffer<char>>(passwordUtf8.size() + 1);
        memcpy(securePass->data(), passwordUtf8.constData(), passwordUtf8.size());
        securePass->data()[passwordUtf8.size()] = '\0';
        safe_zero_and_clear(passwordUtf8);
        safe_zero_and_clear(passwordEdit);
        return securePass;
    }
};

// -------------------------------------------------------------------
// Vault file format (now with global HMAC)
// -------------------------------------------------------------------
struct VaultCheckBlock {
    static const uint32_t EXPECTED_VALUE = 0xDEADBEEF;
    std::vector<uint8_t> encryptedCheck;
    std::vector<uint8_t> nonce;
};

struct AccountRecord {
    QString name;
    QByteArray encryptedSecret;
    QByteArray nonce;
    QString type;
    QString algorithm;      // stored as string for compatibility
    int digits;
    quint64 counter;
    int step;

    std::vector<uint8_t> getAAD() const {
        QByteArray aad;
        QDataStream stream(&aad, QIODevice::WriteOnly);
        stream.setVersion(QDataStream::Qt_6_0);
        stream << name << type << algorithm << quint32(digits) << quint64(counter) << quint32(step);
        return std::vector<uint8_t>(aad.begin(), aad.end());
    }

    Algorithm getAlgorithmEnum() const {
        return algorithmFromString(algorithm);
    }
};

struct VaultHeader {
    std::vector<uint8_t> salt;
    VaultCheckBlock checkBlock;
};

// -------------------------------------------------------------------
// Save accounts with global HMAC (file integrity)
// -------------------------------------------------------------------
bool saveAccounts(const QString &filePath,
                  const SecureBuffer<uint8_t>& encKey,
                  const VaultHeader &header,
                  const QList<AccountRecord> &accounts) {
    if (accounts.size() > (int)MAX_ACCOUNTS) return false;

    // Serialize everything into a byte array
    QByteArray data;
    QDataStream out(&data, QIODevice::WriteOnly);
    out.setVersion(QDataStream::Qt_6_0);

    out << quint32(0xA1B2C3D4);
    out << quint32(4); // version

    out << quint32(header.salt.size());
    out.writeRawData(reinterpret_cast<const char*>(header.salt.data()), header.salt.size());

    out << quint32(header.checkBlock.encryptedCheck.size());
    out.writeRawData(reinterpret_cast<const char*>(header.checkBlock.encryptedCheck.data()),
                     header.checkBlock.encryptedCheck.size());
    out << quint32(header.checkBlock.nonce.size());
    out.writeRawData(reinterpret_cast<const char*>(header.checkBlock.nonce.data()),
                     header.checkBlock.nonce.size());

    out << quint32(accounts.size());

    for (const auto &acc : accounts) {
        if (acc.name.size() > (int)MAX_ACCOUNT_NAME_LEN) return false;
        if (acc.encryptedSecret.size() > (int)MAX_SECRET_SIZE) return false;

        out << acc.name
            << acc.encryptedSecret
            << acc.nonce
            << acc.type
            << acc.algorithm
            << quint32(acc.digits)
            << quint64(acc.counter)
            << quint32(acc.step);
    }

    // Compute HMAC of the serialized data
    SecureVector<uint8_t> mac = hmac_sha256(encKey,
                                            reinterpret_cast<const uint8_t*>(data.constData()),
                                            data.size());

    // Write data + MAC
    QFile file(filePath);
    if (!file.open(QIODevice::WriteOnly))
        return false;

    file.write(data);
    file.write(reinterpret_cast<const char*>(mac.data()), mac.size());
    return true;
}

// -------------------------------------------------------------------
// Load accounts and verify global HMAC
// -------------------------------------------------------------------
bool loadAccounts(const QString &filePath,
                  const SecureBuffer<uint8_t>& encKey,
                  VaultHeader &header,
                  QList<AccountRecord> &accounts) {
    QFile file(filePath);
    if (!file.open(QIODevice::ReadOnly))
        return false;

    QByteArray wholeFile = file.readAll();
    if (wholeFile.size() < SHA256_DIGEST_LENGTH)
        return false;

    // Split: last 32 bytes are MAC
    QByteArray dataPart = wholeFile.left(wholeFile.size() - SHA256_DIGEST_LENGTH);
    QByteArray macPart = wholeFile.right(SHA256_DIGEST_LENGTH);

    // Verify MAC
    SecureVector<uint8_t> computedMac = hmac_sha256(encKey,
                                                     reinterpret_cast<const uint8_t*>(dataPart.constData()),
                                                     dataPart.size());
    if (sodium_memcmp(computedMac.data(), macPart.constData(), SHA256_DIGEST_LENGTH) != 0)
        return false; // Tampered

    // Parse data part
    QDataStream in(dataPart);
    in.setVersion(QDataStream::Qt_6_0);

    quint32 magic, version;
    in >> magic >> version;
    if (magic != 0xA1B2C3D4) return false;
    if (version != 4) return false;

    quint32 saltSize;
    in >> saltSize;
    if (saltSize > 64) return false;
    header.salt.resize(saltSize);
    in.readRawData(reinterpret_cast<char*>(header.salt.data()), saltSize);

    quint32 checkSize;
    in >> checkSize;
    if (checkSize > 1024) return false;
    header.checkBlock.encryptedCheck.resize(checkSize);
    in.readRawData(reinterpret_cast<char*>(header.checkBlock.encryptedCheck.data()), checkSize);

    quint32 nonceSize;
    in >> nonceSize;
    if (nonceSize != 12) return false;
    header.checkBlock.nonce.resize(nonceSize);
    in.readRawData(reinterpret_cast<char*>(header.checkBlock.nonce.data()), nonceSize);

    quint32 count;
    in >> count;
    if (count > MAX_ACCOUNTS) return false;
    accounts.reserve(count);

    for (quint32 i = 0; i < count; ++i) {
        AccountRecord acc;
        quint32 digits, step;
        quint64 counter;
        in >> acc.name >> acc.encryptedSecret >> acc.nonce
           >> acc.type >> acc.algorithm
           >> digits >> counter >> step;

        if (acc.name.size() > (int)MAX_ACCOUNT_NAME_LEN) return false;
        if (acc.encryptedSecret.size() > (int)MAX_SECRET_SIZE) return false;
        if (digits < VALID_DIGITS_MIN || digits > VALID_DIGITS_MAX) return false;
        if (step < VALID_STEP_MIN || step > VALID_STEP_MAX) return false;

        acc.digits = digits;
        acc.counter = counter;
        acc.step = step;
        accounts.append(acc);
    }
    return true;
}

bool validateVaultPassword(const SecureBuffer<uint8_t> &encKey, const VaultHeader &header) {
    try {
        std::vector<uint8_t> emptyAAD;
        auto decrypted = chacha20_poly1305_decrypt(encKey, header.checkBlock.encryptedCheck,
                                                    header.checkBlock.nonce, emptyAAD);

        if (decrypted->size() != 4) return false;
        uint8_t expected[4];
        expected[0] = (VaultCheckBlock::EXPECTED_VALUE >> 24) & 0xFF;
        expected[1] = (VaultCheckBlock::EXPECTED_VALUE >> 16) & 0xFF;
        expected[2] = (VaultCheckBlock::EXPECTED_VALUE >> 8) & 0xFF;
        expected[3] = VaultCheckBlock::EXPECTED_VALUE & 0xFF;
        bool result = constant_time_compare_32(decrypted->data(), expected);
        sodium_memzero(expected, sizeof(expected));
        return result;
    } catch (...) {
        return false;
    }
}

VaultCheckBlock createVaultCheckBlock(const SecureBuffer<uint8_t> &encKey) {
    VaultCheckBlock block;
    auto testData = std::make_unique<SecureBuffer<uint8_t>>(4);
    testData->data()[0] = (VaultCheckBlock::EXPECTED_VALUE >> 24) & 0xFF;
    testData->data()[1] = (VaultCheckBlock::EXPECTED_VALUE >> 16) & 0xFF;
    testData->data()[2] = (VaultCheckBlock::EXPECTED_VALUE >> 8) & 0xFF;
    testData->data()[3] = VaultCheckBlock::EXPECTED_VALUE & 0xFF;

    std::vector<uint8_t> emptyAAD;
    std::vector<uint8_t> nonce;
    block.encryptedCheck = chacha20_poly1305_encrypt(encKey, testData->data(), 4, emptyAAD, nonce);
    block.nonce = nonce;
    return block;
}

// -------------------------------------------------------------------
// Main window with auto-lock and HOTP persistence
// -------------------------------------------------------------------
class AuthenticatorWindow : public QMainWindow {
    Q_OBJECT

private:
    struct Account {
        QString name;
        QString type;
        Algorithm algorithm;
        int digits;
        quint64 counter;
        int step;
        std::unique_ptr<SecureBuffer<uint8_t>> secret;

        // Make Account movable but not copyable
        Account() = default;
        ~Account() = default;
        Account(Account&&) = default;
        Account& operator=(Account&&) = default;
        Account(const Account&) = delete;
        Account& operator=(const Account&) = delete;
    };

    std::vector<Account> accounts;          // now a std::vector
    QListWidget *listWidget = nullptr;
    std::unique_ptr<SecureBuffer<char>> securePassword;
    std::unique_ptr<SecureBuffer<uint8_t>> encKey;
    QString dbPath;
    std::unique_ptr<QLockFile> fileLock;
    VaultHeader vaultHeader;
    QTimer *autoLockTimer = nullptr;
    bool isLocked = false;

public:
    AuthenticatorWindow(QWidget *parent = nullptr) : QMainWindow(parent) {
        try {
            prctl(PR_SET_DUMPABLE, 0);

            if (sodium_init() < 0)
                throw std::runtime_error("Failed to initialize libsodium");

            SecurePasswordDialog pwdDialog(this);
            auto securePass = pwdDialog.getSecurePassword();
            if (!securePass) exit(10); // user canceled

            securePassword = std::move(securePass);

            QString dataDir = QStandardPaths::writableLocation(QStandardPaths::AppLocalDataLocation);
            QDir().mkpath(dataDir);
            dbPath = dataDir + "/accounts.dat";

            QString lockFilePath = dbPath + ".lock";
            fileLock = std::make_unique<QLockFile>(lockFilePath);
            if (!fileLock->tryLock(1000))
                throw std::runtime_error("Another instance is running. File locked.");

            setupUi();
            setupAutoLock();

            if (QFile::exists(dbPath))
                loadExistingVault();
            else
                createNewVault();

            // Wipe master password immediately after key derivation
            securePassword = nullptr;

            refreshCodes();

            QTimer *refreshTimer = new QTimer(this);
            connect(refreshTimer, &QTimer::timeout, this, &AuthenticatorWindow::refreshCodes);
            refreshTimer->start(1000);
        } catch (const std::exception &e) {
            QMessageBox::critical(this, "Initialisation Error", QString("Failed to start: %1").arg(e.what()));
            exit(1);
        }
    }
    ~AuthenticatorWindow() {
        if (fileLock) fileLock->unlock();
    }
    bool eventFilter(QObject *obj, QEvent *event) override {
        if (event->type() == QEvent::MouseButtonPress ||
            event->type() == QEvent::KeyPress) {
            if (!isLocked) resetAutoLock();
        }
        return QMainWindow::eventFilter(obj, event);
    }

private slots:
    void addManually() {
        if (isLocked) {
            QMessageBox::warning(this, "Locked", "Vault is locked. Please restart.");
            return;
        }

        QDialog dlg(this);
        QFormLayout layout(&dlg);

        QLineEdit *nameEdit = new QLineEdit;
        QLineEdit *secretEdit = new QLineEdit;
        QComboBox *typeCombo = new QComboBox; typeCombo->addItems({"totp", "hotp"});
        QComboBox *algoCombo = new QComboBox; algoCombo->addItems({"SHA1", "SHA256", "SHA512"});
        QSpinBox *digitsSpin = new QSpinBox; digitsSpin->setRange(VALID_DIGITS_MIN, VALID_DIGITS_MAX); digitsSpin->setValue(6);
        QSpinBox *counterSpin = new QSpinBox; counterSpin->setRange(0, INT_MAX); counterSpin->setValue(0);
        QSpinBox *stepSpin = new QSpinBox; stepSpin->setRange(VALID_STEP_MIN, VALID_STEP_MAX); stepSpin->setValue(30);

        layout.addRow("Name", nameEdit);
        layout.addRow("Secret (base32)", secretEdit);
        layout.addRow("Type", typeCombo);
        layout.addRow("Algorithm", algoCombo);
        layout.addRow("Digits", digitsSpin);
        layout.addRow("Counter (HOTP)", counterSpin);
        layout.addRow("Step (TOTP)", stepSpin);

        QDialogButtonBox buttons(QDialogButtonBox::Ok | QDialogButtonBox::Cancel);
        layout.addRow(&buttons);
        connect(&buttons, &QDialogButtonBox::accepted, &dlg, &QDialog::accept);
        connect(&buttons, &QDialogButtonBox::rejected, &dlg, &QDialog::reject);

        if (dlg.exec() != QDialog::Accepted) {
            safe_zero_and_clear(secretEdit);
            safe_zero_and_clear(nameEdit);
            return;
        }

        QString providedName = nameEdit->text();
        QString providedSecret = secretEdit->text();

        safe_zero_and_clear(nameEdit);
        safe_zero_and_clear(secretEdit);

        addAccount(providedName, providedSecret,
                   typeCombo->currentText(),
                   algorithmFromString(algoCombo->currentText()),
                   digitsSpin->value(), counterSpin->value(), stepSpin->value());

        safe_zero_and_clear(providedName);
        safe_zero_and_clear(providedSecret);

        resetAutoLock();
    }

    void scanQR() {
        if (isLocked) {
            QMessageBox::warning(this, "Locked", "Vault is locked. Please restart.");
            return;
        }

        QClipboard *clipboard = QApplication::clipboard();
        QImage img = clipboard->image();

        // After grabbing, clear clipboard ASAP
        safe_zero_and_clear(clipboard);

        if (img.isNull()) {
            QMessageBox::warning(this, "No Image", "Clipboard does not contain an image.");
            return;
        }

        try {
            QString data = scanQRFromImage(img);

            // Zero QR image as soon as done
            img = QImage();

            if (data.isEmpty()) {
                QMessageBox::warning(this, "No QR", "No QR code found.");
                return;
            }

            OtpAuthInfo info = parseOtpauthUri(data);
            safe_zero_and_clear(data);
            if (!info.valid) {
                QMessageBox::warning(this, "Invalid URI", "Not a valid otpauth URI.");
                return;
            }
            QDialog dlg(this);
            QFormLayout layout(&dlg);
            QLineEdit *nameEdit = new QLineEdit(info.label);
            QLineEdit *secretEdit = new QLineEdit(info.secret);
            secretEdit->setReadOnly(true);
            QComboBox *typeCombo = new QComboBox; typeCombo->addItems({"totp", "hotp"}); typeCombo->setCurrentText(info.type);
            QComboBox *algoCombo = new QComboBox; algoCombo->addItems({"SHA1", "SHA256", "SHA512"}); algoCombo->setCurrentText(algorithmToString(info.algorithm));
            QSpinBox *digitsSpin = new QSpinBox; digitsSpin->setRange(VALID_DIGITS_MIN, VALID_DIGITS_MAX); digitsSpin->setValue(info.digits);
            QSpinBox *counterSpin = new QSpinBox; counterSpin->setRange(0, INT_MAX); counterSpin->setValue(info.counter);
            QSpinBox *stepSpin = new QSpinBox; stepSpin->setRange(VALID_STEP_MIN, VALID_STEP_MAX); stepSpin->setValue(info.step);

            layout.addRow("Name", nameEdit);
            layout.addRow("Secret", secretEdit);
            layout.addRow("Type", typeCombo);
            layout.addRow("Algorithm", algoCombo);
            layout.addRow("Digits", digitsSpin);
            layout.addRow("Counter (HOTP)", counterSpin);
            layout.addRow("Step (TOTP)", stepSpin);

            QDialogButtonBox buttons(QDialogButtonBox::Ok | QDialogButtonBox::Cancel);
            layout.addRow(&buttons);
            connect(&buttons, &QDialogButtonBox::accepted, &dlg, &QDialog::accept);
            connect(&buttons, &QDialogButtonBox::rejected, &dlg, &QDialog::reject);

            if (dlg.exec() != QDialog::Accepted) {
                safe_zero_and_clear(secretEdit);
                safe_zero_and_clear(nameEdit);
                return;
            }

            QString providedName = nameEdit->text();
            QString providedSecret = secretEdit->text();
            safe_zero_and_clear(nameEdit);
            safe_zero_and_clear(secretEdit);

            addAccount(providedName, providedSecret,
                       typeCombo->currentText(),
                       info.algorithm,
                       digitsSpin->value(), counterSpin->value(), stepSpin->value());

            safe_zero_and_clear(providedName);
            safe_zero_and_clear(providedSecret);

            resetAutoLock();
        } catch (const std::exception &e) {
            QMessageBox::warning(this, "Error", QString("QR scan failed: %1").arg(e.what()));
        }
    }

    void onAutoLockTimeout() {
        isLocked = true;
        encKey = nullptr;
        accounts.clear();
        listWidget->clear();
        QMessageBox::information(this, "Auto-Locked", "Vault auto-locked due to inactivity. Please restart.");
    }

    void useHOTPCode(int accountIdx) {
        if (isLocked || accountIdx < 0 || accountIdx >= static_cast<int>(accounts.size())) return;
        Account &acc = accounts[accountIdx];
        if (acc.type != "hotp") return;
        acc.counter++;

        try {
            QList<AccountRecord> allRecs;
            VaultHeader tempHeader;
            // Load current records (without MAC check – we are about to save)
            // For simplicity we reload the file without MAC verification, but we trust our own data.
            // A more robust approach would keep the records in memory, but here we reload.
            if (!loadAccounts(dbPath, *encKey, tempHeader, allRecs))
                throw std::runtime_error("Failed to reload accounts");

            if (accountIdx < allRecs.size()) {
                allRecs[accountIdx].counter = acc.counter;
                if (!saveAccounts(dbPath, *encKey, vaultHeader, allRecs))
                    throw std::runtime_error("Failed to save");
            }

            rebuildList();
        } catch (const std::exception &e) {
            QMessageBox::warning(this, "Error", QString("Failed to save counter: %1").arg(e.what()));
        }
    }

private:
    void setupAutoLock() {
        autoLockTimer = new QTimer(this);
        connect(autoLockTimer, &QTimer::timeout, this, &AuthenticatorWindow::onAutoLockTimeout);
        autoLockTimer->start(AUTO_LOCK_TIMEOUT_MS);

        installEventFilter(this);
        if (listWidget) listWidget->installEventFilter(this);
    }

    void resetAutoLock() {
        if (!isLocked && autoLockTimer) {
            autoLockTimer->stop();
            autoLockTimer->start(AUTO_LOCK_TIMEOUT_MS);
        }
    }
    void setupUi() {
        QWidget *central = new QWidget;
        setCentralWidget(central);
        QVBoxLayout *layout = new QVBoxLayout(central);

        listWidget = new QListWidget;
        layout->addWidget(listWidget);

        QHBoxLayout *btnLayout = new QHBoxLayout;
        QPushButton *addManual = new QPushButton("Add Manual");
        QPushButton *addQR = new QPushButton("Scan QR from Clipboard");
        btnLayout->addWidget(addManual);
        btnLayout->addWidget(addQR);
        layout->addLayout(btnLayout);

        connect(addManual, &QPushButton::clicked, this, &AuthenticatorWindow::addManually);
        connect(addQR, &QPushButton::clicked, this, &AuthenticatorWindow::scanQR);

        setWindowTitle("Authenticator");
        resize(500, 400);
    }
    void createNewVault() {
        vaultHeader.salt = random_bytes(16);
        encKey = derive_key(*securePassword, vaultHeader.salt);

        vaultHeader.checkBlock = createVaultCheckBlock(*encKey);

        QList<AccountRecord> emptyList;
        if (!saveAccounts(dbPath, *encKey, vaultHeader, emptyList)) {
            encKey = nullptr;
            throw std::runtime_error("Failed to create vault");
        }
    }
    void loadExistingVault() {
        QList<AccountRecord> records;
        // First load with MAC verification (needs encKey)
        encKey = derive_key(*securePassword, vaultHeader.salt);
        if (!loadAccounts(dbPath, *encKey, vaultHeader, records)) {
            encKey = nullptr;
            throw std::runtime_error("Failed to load vault or incorrect password");
        }
        if (!validateVaultPassword(*encKey, vaultHeader)) {
            encKey = nullptr;
            throw std::runtime_error("Incorrect password");
        }
        for (const auto &rec : records) {
            try {
                auto aad = rec.getAAD();
                std::vector<uint8_t> encSecret(rec.encryptedSecret.begin(), rec.encryptedSecret.end());
                std::vector<uint8_t> nonce(rec.nonce.begin(), rec.nonce.end());
                auto secretBin = chacha20_poly1305_decrypt(*encKey, encSecret, nonce, aad);

                Account acc;
                acc.name = rec.name;
                acc.type = rec.type;
                acc.algorithm = rec.getAlgorithmEnum();
                acc.digits = rec.digits;
                acc.counter = rec.counter;
                acc.step = rec.step;
                acc.secret = std::move(secretBin);
                accounts.push_back(std::move(acc));
                sodium_memzero(encSecret.data(), encSecret.size());
            } catch (std::exception &e) {
                QMessageBox::warning(this, "Decryption failed", QString("Failed to decrypt '%1': %2").arg(rec.name).arg(e.what()));
            }
        }
    }
    void addAccount(const QString &name, const QString &secretB32,
                    const QString &type, Algorithm algorithm,
                    int digits, int counter, int step) {
        try {
            auto secretBin = base32_decode(secretB32);

            if (secretBin->size() == 0)
                throw std::runtime_error("Invalid base32");

            AccountRecord rec;
            rec.name = name;
            rec.type = type;
            rec.algorithm = algorithmToString(algorithm);
            rec.digits = digits;
            rec.counter = counter;
            rec.step = step;

            auto aad = rec.getAAD();
            std::vector<uint8_t> nonce;
            std::vector<uint8_t> encrypted = chacha20_poly1305_encrypt(*encKey,
                secretBin->data(), secretBin->size(), aad, nonce);

            rec.encryptedSecret = QByteArray(reinterpret_cast<char*>(encrypted.data()), encrypted.size());
            rec.nonce = QByteArray(reinterpret_cast<char*>(nonce.data()), nonce.size());

            QList<AccountRecord> allRecs;
            VaultHeader tempHeader;
            // Load existing records (without MAC check – we will rewrite)
            if (!loadAccounts(dbPath, *encKey, tempHeader, allRecs))
                throw std::runtime_error("Failed to reload vault");

            allRecs.append(rec);
            if (!saveAccounts(dbPath, *encKey, vaultHeader, allRecs))
                throw std::runtime_error("Failed to save");

            Account acc;
            acc.name = name;
            acc.type = type;
            acc.algorithm = algorithm;
            acc.digits = digits;
            acc.counter = counter;
            acc.step = step;
            acc.secret = std::move(secretBin);
            accounts.push_back(std::move(acc));
            rebuildList();
            sodium_memzero(encrypted.data(), encrypted.size());
        } catch (std::exception &e) {
            QMessageBox::critical(this, "Error", e.what());
        }
    }
    void rebuildList() {
        listWidget->clear();
        for (size_t i = 0; i < accounts.size(); ++i) {
            QListWidgetItem *item = new QListWidgetItem;
            updateListItem(item, i);
            listWidget->addItem(item);
        }
    }
    void refreshCodes() {
        if (isLocked || !listWidget) return;

        uint64_t now = QDateTime::currentSecsSinceEpoch();
        for (size_t i = 0; i < accounts.size(); ++i) {
            auto &acc = accounts[i];
            uint32_t code = 0;

            if (acc.type == "totp") {
                code = totp(acc.secret->data(), acc.secret->size(),
                            now, acc.step, acc.algorithm, acc.digits);
            } else {
                code = hotp(acc.secret->data(), acc.secret->size(),
                            acc.counter, acc.algorithm, acc.digits);
            }

            QString codeStr = QString("%1").arg(code, acc.digits, 10, QChar('0'));
            QListWidgetItem *item = listWidget->item(static_cast<int>(i));
            if (!item) continue;
            QString text = acc.name + " : " + codeStr;
            if (acc.type == "totp") {
                int remain = acc.step - (now % acc.step);
                text += QString(" (%1 s)").arg(remain);
            }
            item->setText(text);
        }
    }
    void updateListItem(QListWidgetItem *item, size_t idx) {
        if (idx < accounts.size())
            item->setText(accounts[idx].name + " : (loading)");
    }
};

int main(int argc, char *argv[]) {
    QApplication app(argc, argv);
    AuthenticatorWindow w;
    w.show();
    return app.exec();
}

#include "authenticator.moc"
