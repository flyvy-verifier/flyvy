#!/bin/bash

# Copyright 2022-2023 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

## This script runs the checks that we use in CI.
##
## When run locally without arguments, command are run with less verbose output.
## In CI we pass the --ci flag to produce verbose output from the build and test
## steps.

set -eu

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

cd "$SCRIPT_DIR/.."

blue=$(tput setaf 4 2>/dev/null || printf "")
red=$(tput setaf 1 2>/dev/null || printf "")
reset=$(tput sgr0 2>/dev/null || printf "")

info() {
  echo -e "${blue}$1${reset}"
}
error() {
  echo -e "${red}$1${reset}"
}

usage() {
  echo "$0 [--ci]"
  echo "--ci adds verbosity and some commands for GitHub actions"
}

ci=false
while [[ $# -gt 0 ]]; do
  case "$1" in
  --ci)
    shift
    ci=true
    ;;
  -h | -help | --help)
    usage
    exit 0
    ;;
  *)
    echo "unknown option/argument" 1>&2
    exit 1
    ;;
  esac
done

start_group() {
  if [ "$ci" = true ]; then
    echo "::group::$1"
  fi
  info "$1"
}

end_group() {
  if [ "$ci" = true ]; then
    echo "::endgroup::"
  fi
}

start_group "cargo build"
if [ "$ci" = true ]; then
  cargo build --tests --verbose
else
  cargo build --tests --quiet
fi
end_group

start_group "cargo test"
if [ "$ci" = true ]; then
  cargo test --all-targets --verbose -- --nocapture
else
  cargo test --all-targets --quiet
fi
end_group

info "cargo fmt --check"
if [ "$ci" = true ]; then
  cargo fmt --check
else
  ## locally we check but also apply the diff

  # run the usual check, print a diff if needed, and remember if it succeeded
  if cargo fmt --check; then
    fmt_good=true
  else
    fmt_good=false
  fi
  # actually apply the diff locally
  cargo fmt
  if [ "$fmt_good" = false ]; then
    error "cargo fmt made some changes"
    exit 1
  fi
fi

start_group "cargo clippy"
if [ "$ci" = true ]; then
  cargo clippy --tests -- --no-deps -D clippy::all
else
  cargo clippy --quiet --tests -- --no-deps -D clippy::all
fi
end_group

start_group "cargo doc"
if [ "$ci" = true ]; then
  cargo doc --document-private-items --no-deps
else
  cargo doc --quiet --document-private-items --no-deps
fi
end_group
