#!/bin/bash

set -euxo pipefail

CPUS=$(nproc --all)

cargo fuzz run --sanitizer none -j$CPUS $1
