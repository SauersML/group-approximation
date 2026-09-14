#!/usr/bin/env python3
"""Merge census shards and compare with the landed F_2 census (eada0577f / a4c730278 artifact):
per-degree histogram {1:357, 2:3804, 3:3399, 4:6951, 5:5799, 6:7629, 7:8037} and the exact list of 94329
pairs unsettled after degree 7.  Then report the extension to higher degrees, and the kernel dimension at
the first settling degree."""
import glob, gzip, json, collections

LANDED_HIST = {1: 357, 2: 3804, 3: 3399, 4: 6951, 5: 5799, 6: 7629, 7: 8037}
first = {}
kmax_done = {}
for sh in sorted(glob.glob("census/sh*")):
    for line in open(f"{sh}/first.txt"):
        a, b, k, ker = map(int, line.split())
        first[(a, b)] = (k, ker)
    # the largest k whose output exists and was fully written
    ks = sorted(int(p.split("_")[-1].split(".")[0]) for p in glob.glob(f"{sh}/out_*.jsonl"))
    done = [k for k in ks if len(open(f"{sh}/pairs_{k}.txt").read().splitlines()) ==
            len(open(f"{sh}/out_{k}.jsonl").read().splitlines())]
    kmax_done[sh] = max(done) if done else -1
kfull = min(kmax_done.values())
allpairs = [(a, b) for a in range(1, 512) for b in range(a + 1, 512)]
hist = collections.Counter(k for (k, _) in first.values())
ours_unsolved_7 = sorted(p for p in allpairs if not (p in first and first[p][0] <= 7))
landed = sorted(tuple(p) for p in json.load(gzip.open("s35_unsolved_after_k7.json.gz"))["unsolved"])
res = {
    "pairs": len(allpairs),
    "degrees_complete_in_all_shards": kfull,
    "hist_first_degree": dict(sorted(hist.items())),
    "hist_matches_landed_through_7": all(hist.get(k, 0) == v for k, v in LANDED_HIST.items()) and hist.get(0, 0) == 0,
    "unsolved_after_7_count": len(ours_unsolved_7),
    "unsolved_after_7_matches_landed_list": ours_unsolved_7 == landed,
    "unsettled_after": {k: sum(1 for p in allpairs if not (p in first and first[p][0] <= k)) for k in range(1, kfull + 1)},
    "kernel_at_first_degree_hist": {k: dict(sorted(collections.Counter(ker for (kk, ker) in first.values() if kk == k).items()))
                                    for k in sorted(hist)},
}
json.dump(res, open("census_compare.json", "w"), indent=1)
print(json.dumps(res, indent=1))
unsolved_final = [p for p in allpairs if p not in first]
with gzip.open(f"s35_unsolved_after_k{kfull}.json.gz", "wt") as f:
    json.dump({"unsolved": [list(p) for p in unsolved_final]} if kfull >= 0 else {}, f)
print("WROTE", f"s35_unsolved_after_k{kfull}.json.gz", len(unsolved_final))
print("DONE")
