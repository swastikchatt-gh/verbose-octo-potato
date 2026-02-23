cmake_minimum_required(VERSION 3.16)
project(Authenticator)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_AUTOMOC ON)

find_package(Qt6 REQUIRED COMPONENTS Core Widgets Gui)

# Find OpenSSL
find_package(OpenSSL REQUIRED)

if(NOT OPENSSL_FOUND)
    message(FATAL_ERROR "OpenSSL not found. Install libssl-dev or set OPENSSL_ROOT_DIR.")
endif()

# Find ZBar
find_path(ZBAR_INCLUDE_DIR zbar.h PATHS /usr/include /usr/local/include /opt/local/include)
find_library(ZBAR_LIBRARY zbar PATHS /usr/lib /usr/local/lib /opt/local/lib)

if(NOT ZBAR_INCLUDE_DIR OR NOT ZBAR_LIBRARY)
    message(FATAL_ERROR "ZBar not found. Install libzbar-dev or set ZBAR_ROOT_DIR.")
endif()

# Find libsodium
find_path(SODIUM_INCLUDE_DIR sodium.h PATHS /usr/include /usr/local/include /opt/local/include)
find_library(SODIUM_LIBRARY sodium PATHS /usr/lib /usr/local/lib /opt/local/lib)

if(NOT SODIUM_INCLUDE_DIR OR NOT SODIUM_LIBRARY)
    message(FATAL_ERROR "libsodium not found. Install libsodium-dev or set SODIUM_ROOT_DIR.")
endif()

add_executable(authenticator authenticator.cpp)

target_include_directories(authenticator PRIVATE
    ${ZBAR_INCLUDE_DIR}
    ${SODIUM_INCLUDE_DIR}
    ${OPENSSL_INCLUDE_DIR}
)

target_link_libraries(authenticator
    Qt6::Core
    Qt6::Widgets
    Qt6::Gui
    OpenSSL::Crypto
    OpenSSL::SSL
    ${ZBAR_LIBRARY}
    ${SODIUM_LIBRARY}
)

install(TARGETS authenticator RUNTIME DESTINATION bin)
