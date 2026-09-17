#!/usr/bin/env python3
"""Merge the pass outputs of the 4x4 census: later passes supersede earlier records with the same id.

Usage: merge.py out.jsonl chunk_files_pass1... -- chunk_files_pass2... -- chunk_files_pass3...
(any number of groups separated by --; within a group order does not matter)
"""
import json
import sys


def main():
    out = sys.argv[1]
    final = {}
    for f in sys.argv[2:]:
        if f == "--":
            continue
        for line in open(f):
            r = json.loads(line)
            final[r["id"]] = r
    with open(out, "w") as fh:
        for i in sorted(final):
            fh.write(json.dumps(final[i], separators=(",", ":")) + "\n")
    stats = {}
    for r in final.values():
        stats[r["status"]] = stats.get(r["status"], 0) + 1
    print(len(final), stats)


if __name__ == "__main__":
    main()
