#!/usr/bin/env bash
# Builds the MiniLean4 kernel to WebAssembly for the ebook playground and
# copies it to docs/book/assets/minilean.wasm.
set -euo pipefail
cd "$(dirname "$0")"
rustup target add wasm32-unknown-unknown >/dev/null 2>&1 || true
cargo build --release --target wasm32-unknown-unknown
cp target/wasm32-unknown-unknown/release/minilean_playground.wasm ../assets/minilean.wasm
ls -l ../assets/minilean.wasm
