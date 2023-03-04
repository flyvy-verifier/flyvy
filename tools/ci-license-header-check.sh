#!/bin/bash

# Copyright 2022-2023 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

## This script runs https://github.com/lluissm/license-header-checker to check
## that license headers are in place.
##
## It can be run locally but note that it modifies files in-place to add
## headers, then reports the diff. You'll need to install license-header-checker, which you can do with:
##
## go install github.com/lluissm/license-header-checker/cmd/license-header-checker@latest

set -eu

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$SCRIPT_DIR/.."

pre_diff="$(git status --porcelain)"

license-header-checker -a -r -i target ./tools/license-header.rs.txt . rs
license-header-checker -a -r -i target ./tools/license-header.sh.txt . fly sh

if [ "$(git status --porcelain)" != "$pre_diff" ]; then
  echo "ERROR: some files are missing license headers" 1>&2
  if [ -n "$pre_diff" ]; then
    echo "  (note: diff includes existing modifications)"
  fi
  git --no-pager diff
  exit 1
fi
