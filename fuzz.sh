#!/bin/bash

set -euxo pipefail

CPUS=32

cargo fuzz run --sanitizer none -j$CPUS queue
