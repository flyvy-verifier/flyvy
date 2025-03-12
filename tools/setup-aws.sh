#!/bin/bash

# Copyright 2022-2023 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

# Install dependencies for an EC2 instance running Amazon Linux

set -e

cd

sudo yum -y update
sudo yum -y groupinstall "Development Tools"
sudo yum -y install htop
sudo yum -y install python

# install rustup (-y disables confirmation)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
# don't try to read this file
# shellcheck disable=SC1091
source "$HOME/.cargo/env"

if [ ! -e ~/flyvy ]; then
  # TODO: remove branch when qalpha is merged
  git clone -b qalpha-contexts https://github.com/flyvy-verifier/flyvy
fi
cd ~/flyvy
./tools/download-solvers.sh

# don't use downloaded z3, it won't work due to an outdated libstd++ in the
# Amazon Linux image
rm solvers/z3

# compile Z3 from source
wget 'https://github.com/Z3Prover/z3/archive/refs/tags/z3-4.14.1.tar.gz'
tar -xf z3-4.14.1.tar.gz
mv z3-z3-4.14.1 z3
cd z3
./configure >/dev/null
cd build
time make -j"$(nproc)"
sudo make install
cp z3 ~/flyvy/solvers/z3
rm -r z3

cd ~/flyvy
cargo build --release
cargo build
