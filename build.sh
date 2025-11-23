#!/bin/bash
set -e

ARGS="$@"

echo "[INFO] Installing LLVM 14..."
sudo apt-get update
sudo apt-get install -y llvm-14 llvm-14-dev clang-14 lld-14

echo "[INFO] Switching default LLVM to version 14..."
sudo update-alternatives --install /usr/bin/clang clang /usr/bin/clang-14 100
sudo update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-14 100
sudo update-alternatives --install /usr/bin/llvm-config llvm-config /usr/bin/llvm-config-14 100

echo "clang version: "
clang --version
echo "llvm-config version:"
llvm-config --version

export LLVM_DIR="/usr/lib/llvm-14/cmake"
export CMAKE_PREFIX_PATH="/usr/lib/llvm-14/cmake:${CMAKE_PREFIX_PATH}"

# If running inside SVF folder (workflow: first build)
if [[ "$PWD" == *"/SVF"* ]]; then
    echo "[INFO] Detected SVF build step."
    rm -rf build/
    mkdir build && cd build
    cmake -DLLVM_DIR=/usr/lib/llvm-14/cmake ..
    make -j2
    exit 0
fi

# Otherwise building student's assignment
echo "[INFO] Building student's assignment..."
rm -rf build/
mkdir build && cd build/

if [ -n "$ARGS" ]; then
  cmake -DCMAKE_BUILD_TYPE=Debug .. -DSUBDIRS="$ARGS"
else
  cmake -DCMAKE_BUILD_TYPE=Debug ..
fi

make -j4

echo "[INFO] Build Success!"
