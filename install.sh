# installation script for ubuntu 22.04
export LLVM_VERSION=18

apt-get update && \
    apt-get install --no-install-recommends -y \
    curl \
    lsb-release \
    wget \
    software-properties-common \
    gnupg && \
    wget https://apt.llvm.org/llvm.sh && \
    chmod +x llvm.sh && \
    ./llvm.sh ${LLVM_VERSION} all && \
    rm llvm.sh && \
    apt install -y git build-essential mlir-18-tools libmlir-18-dev zlib1g-dev libzstd-dev clang-17
