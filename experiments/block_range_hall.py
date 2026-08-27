#!/usr/bin/env python3
"""Exact checker/searcher for block-range Hall shrinkage certificates.

Input JSON:
{
  "source_dims": [2, 1],
  "targets": [
    {"dim": 2, "ranges": [ [[1,0]], [[0,1]] ]}
  ]
}

For target j and source i, targets[j].ranges[i] is any spanning list of
vectors for R_(j,i) inside Q^target_dim. Entries may be integers or strings
accepted by fractions.Fraction (for example "3/7").

The tool enumerates nonempty source-block subsets, computes exact rational
ranks of the combined range spans, and returns the subset maximizing

    sum(source dimensions) - sum(target range-span dimensions).

For the fixed Fourier alphabets in the atlas program this exhaustive backend
is intentionally simpler than a general submodular-minimization package.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path


def q(x):
    if isinstance(x, bool):
        raise ValueError("boolean is not a rational entry")
    return Fraction(str(x))


def rank(vectors, dim):
    """Rank of row vectors over Q by exact Gaussian elimination."""
    rows = []
    for raw in vectors:
        if not isinstance(raw, list) or len(raw) != dim:
            raise ValueError(f"expected vector of length {dim}")
        row = [q(x) for x in raw]
        if any(row):
            rows.append(row)
    r = 0
    for c in range(dim):
        pivot = next((k for k in range(r, len(rows)) if rows[k][c]), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        z = rows[r][c]
        rows[r] = [x / z for x in rows[r]]
        for k in range(len(rows)):
            if k == r or not rows[k][c]:
                continue
            z = rows[k][c]
            rows[k] = [a - z * b for a, b in zip(rows[k], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


def check(data):
    source_dims = data.get("source_dims")
    targets = data.get("targets")
    if not isinstance(source_dims, list) or not source_dims:
        raise ValueError("source_dims must be a nonempty list")
    source_dims = [int(x) for x in source_dims]
    if any(x < 0 for x in source_dims):
        raise ValueError("source dimensions must be nonnegative")
    n = len(source_dims)
    if not isinstance(targets, list):
        raise ValueError("targets must be a list")

    parsed = []
    for j, t in enumerate(targets):
        if not isinstance(t, dict):
            raise ValueError(f"targets[{j}] must be an object")
        d = int(t.get("dim"))
        if d < 0:
            raise ValueError(f"targets[{j}].dim must be nonnegative")
        rs = t.get("ranges")
        if not isinstance(rs, list) or len(rs) != n:
            raise ValueError(f"targets[{j}].ranges must have {n} source entries")
        for i, vecs in enumerate(rs):
            if not isinstance(vecs, list):
                raise ValueError(f"targets[{j}].ranges[{i}] must be a list")
            for v in vecs:
                if not isinstance(v, list) or len(v) != d:
                    raise ValueError(
                        f"targets[{j}].ranges[{i}] contains vector not of length {d}"
                    )
                [q(x) for x in v]
        parsed.append((d, rs))

    best = None
    table = []
    for mask in range(1, 1 << n):
        subset = [i for i in range(n) if mask >> i & 1]
        src = sum(source_dims[i] for i in subset)
        target_ranks = []
        for d, rs in parsed:
            vecs = [v for i in subset for v in rs[i]]
            target_ranks.append(rank(vecs, d))
        image_bound = sum(target_ranks)
        deficit = src - image_bound
        row = {
            "subset": subset,
            "source_dimension": src,
            "target_range_dimensions": target_ranks,
            "image_dimension_upper_bound": image_bound,
            "deficit": deficit,
        }
        table.append(row)
        key = (deficit, -len(subset), tuple(-i for i in subset))
        if best is None or key > best[0]:
            best = (key, row)

    out = dict(best[1])
    out.update({
        "status": "shrunk" if out["deficit"] > 0 else "no_block_range_certificate",
        "source_block_count": n,
        "subsets_checked": (1 << n) - 1,
    })
    if data.get("include_all"):
        out["all_subsets"] = table
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("input", type=Path)
    ap.add_argument("--compact", action="store_true")
    args = ap.parse_args()
    try:
        data = json.loads(args.input.read_text())
        result = check(data)
    except (OSError, ValueError, TypeError, json.JSONDecodeError) as e:
        print(json.dumps({"status": "error", "error": str(e)}))
        return 2
    print(json.dumps(result, indent=None if args.compact else 2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
