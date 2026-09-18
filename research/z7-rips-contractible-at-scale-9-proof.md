---
rg: 2
id: z7-rips-contractible-at-scale-9-proof
kind: route
title: The uniform domination and link-collapse certificate at n = 7, scale 9, found in stages and replayed by the C++ checker
target: z7-rips-contractible-at-scale-9
requires: []
artifacts: [research/z6-rips-contractible-at-scales-6-to-9-proof.md, experiments/zn-rips-sharp-scale-2026-09-17/README.md, experiments/zn-rips-sharp-scale-2026-09-17/uniform.cpp, experiments/zn-rips-sharp-scale-2026-09-17/verify_fast.cpp, experiments/zn-rips-sharp-scale-2026-09-17/results.txt]
---

**The argument.** Sections 1–3 of `research/z6-rips-contractible-at-scales-6-to-9-proof.md` hold for every
`(n, r)`. Compactness reduces to boxes `[0,m]^n`. Anti-lexicographic peeling reduces those to the links
`Flag(L(I))`. The certificate theorem then says: one sequence of (D) and (K) moves on
`Lmax = L([−r,r]^{n−1} × [0,r])` that leaves exactly `{e_1, …, e_n}` proves `VR(Z^n, d_1; r)` contractible.
So it is enough to exhibit and check one certificate for `(7, 9)`.

**The search.** `|Lmax| = 112071`. `uniform.cpp` ran in three stages. Each stage starts from the survivor set of
the previous one (`initfile`) and appends moves to the same move sequence.

1. D-moves only: 87863 deletions, leaving 24208 points with coordinate extents up to 3.
2. D and K moves, stopped by a time budget at a move boundary: 2175 K-moves, leaving 22033 points.
3. D and K moves to completion, leaving `{e_1, …, e_7}`.

The concatenated certificate (`cert-7-9-a`, `-b1` and `-b2`, 581804772 bytes) is not committed; its sha256 is in
`results.txt`. Stage 2 stops on wall-clock time, so a rerun can split the sequence at a different point and give a
different certificate, which must be checked in the same way. Stage 1 alone leaves 24208 survivors, so K-moves are
essential at this scale too.

**The check.** `verify_fast.cpp` is a C++ replay written independently of the search. It rebuilds `Lmax` from its
definition. For every move it checks liveness, `w ∈ hull(0,x)` or `w ∈ hull(0,x,y)`, each domination inclusion by
explicit `d_1` computations over the current set or link, and that every link collapses to its survivor
`p ∈ hull(0,x)`. It accepts only if the final set is `{e_1..e_7}`. It replayed the whole certificate in checkpointed
runs (`./verify_fast 7 9 cert.txt state.bin 1000`, rerun until it exits 0):

| n | r | `|Lmax|` | D-moves | K-moves | K link steps | verify_fast |
|---|---|---|---|---|---|---|
| 7 | 9 | 112071 | 108368 | 3696 | 16816670 | ACCEPT |

The same checker agrees with `verify.py` on every certificate both have replayed: `(6,6..9)`, `(7,7)` and `(7,8)`.
It rejects the `r = n − 1` calibration certificates and hand-corrupted dominators. The numpy `verify.py` replayed
the first 49882 D-moves of `(7,9)` without error and was then stopped, because the full replay would take many hours
on this machine. So `(7,9)` has one complete independent replay, not two.
