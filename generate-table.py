import glob
import json
import os
import re
import sys
from pathlib import Path

GROUP = "synthetic_signature_aggregation_and_prove"
OUTPUT_FILE = Path("benchmark_results.md")


def parse_mode():
    if len(sys.argv) >= 2:
        mode = sys.argv[1]
        if mode not in ("fast", "full"):
            print("Usage: generate-table.py {fast|full}", file=sys.stderr)
            sys.exit(1)
        return mode
    return os.environ.get("DYNAHINTS_BENCH_MODE", "full")


def load_results():
    pattern = os.path.join("target", "criterion", "*", "*", "*", "new", "estimates.json")
    results = {}

    for estimate_path in glob.glob(pattern):
        path = Path(estimate_path)
        if path.parts[-5] != GROUP:
            continue

        match = re.fullmatch(r"n_(\d+)", path.parts[-4])
        committee_match = re.fullmatch(r"(\d+)", path.parts[-3])
        if not match or not committee_match:
            continue

        with path.open("r", encoding="utf-8") as estimate_file:
            estimate = json.load(estimate_file)

        mean_ns = estimate["mean"]["point_estimate"]
        results[(int(match.group(1)), int(committee_match.group(1)))] = mean_ns / 1_000_000

    return results


def main():
    mode = parse_mode()
    results = load_results()

    OUTPUT_FILE.write_text(
        "# Synthetic signature aggregation and prove benchmark\n\n"
        f"Mode: `{mode}`\n\n"
        "| n | committee_size | threshold | Time (ms) |\n"
        "|---|---:|---:|---:|\n"
        + "".join(
            f"| {n} | {committee_size} | {committee_size // 2 or 1} | {mean_ms:.4f} |\n"
            for (n, committee_size), mean_ms in sorted(results.items())
        ),
        encoding="utf-8",
    )

    print(f"Results written to {OUTPUT_FILE}")


if __name__ == "__main__":
    main()
