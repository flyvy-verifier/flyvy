#!/bin/bash

# Copyright 2022-2023 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

## Helper script to regenerate insta snapshots from scratch.

set -eu

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

cd "$SCRIPT_DIR/.."


if [ "$(git status --porcelain | wc -l)" -ne 0 ]; then
  echo git repo is not clean, exiting to avoid losing work. commit your changes first.
  exit 1
fi

find . -type d -name snapshots -prune -exec rm -r {} \;
cargo insta test --accept
