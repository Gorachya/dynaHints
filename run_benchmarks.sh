#!/bin/bash
set -e

if [ "$1" != "fast" ] && [ "$1" != "full" ]; then
    echo "Usage: $0 {fast|full}"
    exit 1
fi

MODE="$1"
export DYNAHINTS_BENCH_MODE="$MODE"

if [ -d "target/criterion" ]; then
    echo "Clearing previous criterion benchmark cache..."
    rm -rf target/criterion
fi

echo "========================================"
echo "      Step 1: Running cargo bench       "
echo "      Mode: $MODE"
echo "========================================"
cargo bench --bench synthetic_prove

echo ""
echo "========================================"
echo " Step 2: Generating benchmark results   "
echo "========================================"

if command -v python3 &>/dev/null; then
    python3 generate-table.py "$MODE"
else
    python generate-table.py "$MODE"
fi

echo ""
echo "Done! The results are saved in benchmark_results.md"
