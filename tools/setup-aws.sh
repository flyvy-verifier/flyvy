#!/bin/bash

# Install dependencies for an EC2 instance running Amazon Linux

set -e

cd

sudo yum -y groupinstall "Development Tools"
sudo yum -y install htop
sudo yum -y install python

# install rustup (-y disables confirmation)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
source "$HOME/.cargo/env"

# compile Z3 from source
# takes about 10min on z1d.xlarge
wget 'https://github.com/Z3Prover/z3/archive/refs/tags/z3-4.12.2.tar.gz'
tar -xf z3-4.12.2.tar.gz

cd z3-z3-4.12.2
./configure >/dev/null
cd build
make -j"$(nproc)"
sudo make install
cd

if [ ! -e ~/temporal-verifier ]; then
  git clone https://github.com/vmware-research/temporal-verifier
fi
cd ~/temporal-verifier
./tools/download-solvers.sh
rm solvers/z3
# don't use downloaded z3, it won't work due to an outdated libstd++ in the
# Amazon Linux image
cargo build --release
