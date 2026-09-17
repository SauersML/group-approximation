---
rg: 2
id: cmsz-pg23-no-brick-coding-by-kraft
kind: route
title: Check (R1) and (R2) exactly for the two PG(2,3) tile 2-graphs, then apply the power-of-two corollary of the rigidity proposition
target: cmsz-pg23-rs-two-graphs-admit-no-brick-coding
requires:
  - two-graph-brick-codings-are-rigid-under-rank-two-h1
artifacts:
  - research/artifacts/nv-brick-codings-of-two-graphs-2026-09-17.md
  - experiments/nv-brick-coding-2026-09-17/tp_q3.json
  - experiments/nv-brick-coding-2026-09-17/check_q3.py
  - experiments/nv-brick-coding-2026-09-17/rs2graph.py
  - experiments/nv-brick-coding-2026-09-17/q3_hypotheses.py
  - experiments/nv-brick-coding-2026-09-17/q3_hypotheses.log
---

Details are in Part C of the artifact. To reproduce, run `python3 check_q3.py` and then
`python3 q3_hypotheses.py` in `experiments/nv-brick-coding-2026-09-17/`. The second script
writes `q3_hypotheses.log`.

1. **Model.**
   - `check_q3.py` checks (A1)–(A3) for T0 and T1, each with `|T| = 52`.
   - `rs2graph.build(T, npoints=13)` builds the tile 2-graph and asserts two things: unique
     filling, and that the square map is a bijection.
   - Each graph has 156 vertices, `1404 + 1404` edges and 12636 squares.
2. **(R1), checked exactly.**
   - For both T, every row sum of `M_1` and `M_2` is 9.
   - `A^4 > 0` entrywise for both colour matrices (primitive exponent 4), so both are
     primitive and hence irreducible.
   - Irreducibility of `M_1` also makes `K(Λ_T)` connected.
3. **(R2), checked exactly.** Let `D` be the integer coboundary `C^1 → C^2`, with one row per
   square `ef = f'e'`, equal to `e + f − f' − e'`.
   - The Gram matrix `DᵀD` has integer entries, computed exactly with a sparse product.
     Its rank over `GF(32749)` is 2651 for both T.
   - `rank_p(DᵀD) ≤ rank_p(D) ≤ rank_Q(D)`, so `rank_Q(D) ≥ 2651`.
   - This gives `dim H^1(K;Q) ≤ 2808 − 2651 − 155 = 2`.
   - The classes `[d_1]` and `[d_2]` are independent, because they pair differently with
     cycles of degree (1,0) and (0,1). So the dimension is at least 2, and equals 2.
4. **Conclusion.**
   - By the first "in particular" clause of `two-graph-brick-codings-are-rigid-under-rank-two-h1`,
     which uses (R1) and (R2) only, any brick coding forces `9 = 2^α` with `α` an integer.
   - That is impossible, so neither `Λ_T` has a brick coding in any dimension.
   - No SAT solver is involved.

**Trust base.**
- The computations are exact integer and modular arithmetic in Python/NumPy, and the
  `GF(p)` step only bounds the rank from below.
- The identification of the tile 2-graph with the Robertson–Steger 2-graph is not used by
  this claim.
