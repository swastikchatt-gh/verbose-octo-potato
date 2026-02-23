# verbose-octo-potato
An advanced authenticator with argon2id, ChaCha20-Poly1305. Built using OpenSSL, Qt6 and Sodium for Linux (Ubuntu 24.04 LTS or higher)
To build it, you may use 
cd verbose-octo-potato
mkdir -p target
cd target
cmake ..
make -j$(nproc)
To clone the repo, use 
https://github.com/swastikchatt-gh/verbose-octo-potato.git
The build dependencies include
build-essential, CMake, OpenSSL, Qt6 Base, Sodium
To download them, please use
sudo apt update
sudo apt install -y libsodium-dev qt6-base-dev libssl-dev cmake build-essential
I hope everyone likes this project.
This project is licensed under SLIC. 
