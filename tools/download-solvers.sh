#!/bin/bash

# Copyright 2022-2023 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

# This script downloads binary releases of Z3, CVC4, and cvc5 to solvers/ in
# the source directory, according to the versions specified in
# tools/solver-versions.sh. It handles Linux, macOS, and macOS arm64.

set -eu

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &>/dev/null && pwd)
cd "$SCRIPT_DIR/.."

# shellcheck disable=SC1091
source tools/solver-versions.sh

UNAME=$(uname)

if [ "$UNAME" = "Linux" ]; then
  Z3_FILE="z3-${Z3_VERSION}-x64-glibc-${Z3_GLIBC_VERSION}"
  CVC4_FILE="cvc4-${CVC4_VERSION}-x86_64-linux-opt"
  CVC5_FILE="cvc5-Linux"
elif [ "$UNAME" = "Darwin" ]; then
  UNAME_M=$(uname -m)
  if [ "${UNAME_M}" = "arm64" ]; then
    Z3_FILE="z3-${Z3_VERSION}-arm64-osx-11.0"
    CVC5_FILE="cvc5-macOS-arm64"
    # x86 binary, don't have an arm64 build
    CVC4_FILE="cvc4-${CVC4_VERSION}-macos-opt"
  elif [ "${UNAME_M}" = "x86_64" ]; then
    Z3_FILE="z3-${Z3_VERSION}-x64-osx-10.16"
    CVC5_FILE="cvc5-macOS"
    CVC4_FILE="cvc4-${CVC4_VERSION}-macos-opt"
  else
    echo "unexpected architecture for macOS: ${UNAME_M}" 1>&2
    exit 1
  fi
else
  echo "unexpected OS ${UNAME}" 1>&2
  exit 1
fi
Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/${Z3_FILE}.zip"
CVC4_URL="https://github.com/CVC4/CVC4/releases/download/${CVC4_VERSION}/${CVC4_FILE}"
CVC5_URL="https://github.com/cvc5/cvc5/releases/download/cvc5-${CVC5_VERSION}/${CVC5_FILE}"

mkdir -p solvers
if [ -x solvers/z3 ] && ./solvers/z3 --version | grep --fixed-strings --quiet "$Z3_VERSION"; then
  echo "found Z3"
else
  cd solvers
  echo "downloading Z3"
  wget -nv -O z3.zip "$Z3_URL"
  unzip -q z3.zip && rm z3.zip
  mv "$Z3_FILE/bin/z3" ./
  rm -r "$Z3_FILE"
  cd ..
fi

if [ -x solvers/cvc5 ] && ./solvers/cvc5 --version | grep --fixed-strings --quiet "$CVC5_VERSION"; then
  echo "found CVC5"
else
  echo "downloading CVC5"
  wget -nv -O solvers/cvc5 "$CVC5_URL"
  chmod +x solvers/cvc5
fi

if [ -x solvers/cvc4 ] && ./solvers/cvc4 --version | grep --fixed-strings --quiet "$CVC4_VERSION"; then
  echo "found CVC4"
else
  echo "downloading CVC4"
  wget -nv -O solvers/cvc4 "$CVC4_URL"
  chmod +x solvers/cvc4
fi
