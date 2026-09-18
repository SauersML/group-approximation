---
rg: 2
id: z7-rips-contractible-at-scales-7-and-8-proof
kind: route
title: The uniform domination and link-collapse certificate at n = 7, scales 7 and 8
target: z7-rips-contractible-at-scales-7-and-8
requires: []
artifacts: [research/z6-rips-contractible-at-scales-6-to-9-proof.md, experiments/zn-rips-sharp-scale-2026-09-17/README.md, experiments/zn-rips-sharp-scale-2026-09-17/uniform.cpp, experiments/zn-rips-sharp-scale-2026-09-17/verify.py, experiments/zn-rips-sharp-scale-2026-09-17/verify_fast.cpp, experiments/zn-rips-sharp-scale-2026-09-17/results.txt]
---

**The argument.** Sections 1–3 of `research/z6-rips-contractible-at-scales-6-to-9-proof.md` never use `n = 6`.
Lemma 1 reduces to boxes. Anti-lexicographic peeling (§2) reduces contractibility of `VR(Z^n, d_1; r)` to
contractibility of `Flag(L(I))` for every box `I ∋ 0` with some `b_i ≥ 1`. The certificate theorem (§3) says:
if a sequence of (D) and (K) moves on `Lmax = L([−r,r]^{n−1} × [0,r])` leaves exactly `{e_1, …, e_n}`, then
every such link is contractible. So for fixed `(n, r)` it is enough to exhibit one certificate.

**The certificates.** `uniform.cpp` (`./uniform 7 r 1 K.txt cert.txt`) produces one for `r = 7` and one for
`r = 8`. `verify.py` is an independent numpy replay, and `verify_fast.cpp` is a second independent replay in C++, sharing no code with the search. It checks liveness, hull
membership, the domination inclusions by explicit `d_1` computations, each link collapse to its survivor
`p ∈ hull(0,x)`, and that the final set is `{e_1..e_7}`.

| r | `|Lmax|` | D-moves | K-moves | K link steps | verifier |
|---|---|---|---|---|---|
| 7 | 24319 | 23172 | 1140 | 1928908 | ACCEPT |
| 8 | 54272 | 53593 | 672 | 2451984 | ACCEPT |

D-moves alone leave 6721 survivors at `(7,7)` and 10393 at `(7,8)`, so the link-collapse move is essential.
The certificates are 66 MB and 85 MB and are not committed. The search is deterministic, and `results.txt`
records their sha256. The verifier replays with checkpoints
(`python3 verify.py 7 r cert.txt state.npz 900`, rerun until it prints ACCEPT). The state file is tied to the
certificate's sha256.

**Consequence.** Before this, `VR(Z^7, d_1; r)` was known to be contractible only for
`r ≥ n(n+1) − 1 = 55` (Zaremsky; McCarty gives `r ≥ 56`). Gupta–Sarkar–Shukla (arXiv:2511.04238) settle
`n ≤ 5` and `n = 6, r ≥ 10`, and say Conjecture 1.1 is open for `n ≥ 7`. This route gives the sharp scale
`r = n` for `n = 7`, and also `r = 8`. The cases `r = 9..54` remain open.
