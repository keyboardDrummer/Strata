#!/bin/bash
set -euo pipefail

# Install the Lean toolchain specified in lean-toolchain
elan install "$(cat lean-toolchain)"

# Build and test to populate the Lake cache
lake build
lake test
