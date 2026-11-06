#!/usr/bin/env bash
# Runs the structural checker over every translated chapter in every locale.
# Usage: tools/check-all-translations.sh   (from docs/book)
set -u
cd "$(dirname "$0")/.."
fail=0
for loc in ja zh; do
  for f in src/*.md; do
    name=$(basename "$f")
    if [ ! -f "src-$loc/$name" ]; then echo "MISSING src-$loc/$name"; fail=1; continue; fi
    python3 tools/check-translation.py "$f" "src-$loc/$name" || fail=1
  done
done
exit $fail
