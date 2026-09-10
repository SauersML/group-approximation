#!/usr/bin/env python3
"""Bounded, reproducible pseudorandom search pilot on T_4 x Z. MSI only."""

import argparse
from collections import Counter
import hashlib
import json
import random
import time

from exploration_search import balanced_search, verify_certificate


def neighbors(vertex):
    word, height = vertex
    for letter in range(4):
        reduced = word[:-1] if word and word[-1] == (letter ^ 1) else word+bytes([letter])
        yield reduced, height
    yield word, height+1
    yield word, height-1


def distance(u, v):
    a, ah = u
    b, bh = v
    prefix = 0
    while prefix < min(len(a), len(b)) and a[prefix] == b[prefix]:
        prefix += 1
    return len(a)+len(b)-2*prefix+abs(ah-bh)


def encode(vertex):
    word, height = vertex
    return len(word).to_bytes(4, "big")+word+height.to_bytes(8, "big", signed=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True)
    parser.add_argument("--trials", type=int, default=12)
    parser.add_argument("--cap", type=int, default=3000)
    args = parser.parse_args()
    assert 1 <= args.trials <= 24 and 1 <= args.cap <= 10000
    started = time.monotonic()
    origin = (b"", 0)
    lengths, percentages, directions = (16, 48, 96), (35, 60, 90), (0, 1, 2)
    records, witnesses = [], []
    for seed in range(args.trials):
        rng = random.Random(1000003+seed)
        walk, endpoints = origin, {}
        for n in range(1, max(lengths)+1):
            step = rng.randrange(12)
            if step >= 6:
                walk = tuple(neighbors(walk))[step-6]
            if n in lengths:
                endpoints[n] = walk
        key = seed.to_bytes(16, "big")
        for n in lengths:
            target = endpoints[n]
            labels = {}

            def label(edge):
                if edge not in labels:
                    labels[edge] = int.from_bytes(hashlib.blake2b(
                        encode(edge[0])+encode(edge[1]), key=key, digest_size=8).digest(), "big")
                return labels[edge]

            for percent in percentages:
                cutoff = percent*(1 << 64)//100
                group = []
                for direction in directions:
                    result = balanced_search(origin, target, neighbors, distance,
                                             lambda edge: label(edge) < cutoff,
                                             direction=direction, query_limit=args.cap)
                    verify_certificate(result, origin, target, neighbors)
                    record = {"seed": seed, "walk_length": n, "percent": percent,
                              "direction": direction, "distance": distance(origin, target),
                              "status": result["status"], "queries": len(result["trace"]),
                              "path_length": len(result["path"])-1 if result["path"] else None,
                              "finite_component_size": len(result["finite_component"])}
                    records.append(record)
                    group.append(record)
                statuses = {r["status"] for r in group}
                assert not ({"connected", "disconnected"} <= statuses)
                if group[0]["status"] == "censored" and group[2]["status"] == "connected":
                    witnesses.append({"seed": seed, "walk_length": n, "percent": percent,
                                      "distance": distance(origin, target),
                                      "breadth_first_queries_lower_bound": args.cap,
                                      "directed_queries": group[2]["queries"],
                                      "directed_path_length": group[2]["path_length"]})
    rows = []
    for n in lengths:
        for percent in percentages:
            for direction in directions:
                chosen = [r for r in records if (r["walk_length"],r["percent"],r["direction"])
                          == (n,percent,direction)]
                counts = Counter(r["status"] for r in chosen)
                rows.append({"walk_length": n, "percent": percent, "direction": direction,
                             "trials": len(chosen), "statuses": dict(counts),
                             "mean_observed_queries": sum(r["queries"] for r in chosen)/len(chosen),
                             "mean_endpoint_distance": sum(r["distance"] for r in chosen)/len(chosen)})
    report = {"status": "completed", "graph": "Cay(F_2 x Z, standard six generators)",
              "sampling": "Deterministic keyed BLAKE2b pseudorandom edge field and separate seeded lazy walk",
              "scope": "Censored finite pilot; no phase classification, infinite-cluster membership, or asymptotic upper bound",
              "query_cap": args.cap, "trials_per_row": args.trials,
              "certificates_checked": len(records), "rows": rows,
              "paired_witnesses": witnesses, "records": records,
              "elapsed_seconds": round(time.monotonic()-started, 3)}
    with open(args.output, "w") as output:
        json.dump(report, output, indent=2)
        output.write("\n")
    print(json.dumps({k:v for k,v in report.items() if k != "records"}, indent=2))


if __name__ == "__main__":
    main()
