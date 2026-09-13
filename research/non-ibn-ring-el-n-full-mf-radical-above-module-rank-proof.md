---
rg: 2
id: non-ibn-ring-el-n-full-mf-radical-above-module-rank-proof
kind: route
title: Conjugate EL_(N+jd) into EL_N through a module isomorphism with a free coordinate, then isolate e_(kc')(1)
target: non-ibn-ring-el-n-full-mf-radical-above-module-rank
requires:
  - paradoxical-ring-el-n-full-mf-radical-from-twice-level
artifacts:
  - research/artifacts/un-middle-stable-paradox-threshold-2026-09-13-part2.md
---

Artifact part 2, §2.

1. `R^m ≅ R^{m+1} ⊕ R^{d−1}` gives `(m+1)[R] ≤ m[R]`, so `EL_M(R)` has full MF radical for `M ≥ 2m`. Pick
   `M = N + jd ≥ 2m`, with `XY = 1_m` and `YX = 1_{m+jd}`.
2. `A = diag(X, 1_{N−m})` and `B = diag(Y, 1_{N−m})` give a group isomorphism `Φ : GL_M(R) → GL_N(R)`, `g ↦ AgB`.
3. With a free index `c ↦ c'`:
   - `Φ(e_{ic}(r)) = Π_k e_{kc'}(x_ki r)` and `Φ(e_{ci}(r)) = Π_k e_{c'k}(r y_ik)`;
   - `e_ij(r) = [e_ic(r), e_cj(1)]`.
   So `Φ(EL_M(R)) ⊆ EL_N(R)`.
4. A homomorphism `φ` to an MF group kills `Φ(EL_M(R))`, hence each `Π_k e_{kc'}(x_ki r)`.
   - For `m = 1`: `Σ_i x_1i y_i1 = 1` gives `e_{1c'}(1) ∈ ker φ`.
   - For `m ≥ 2`: conjugating by `e_{kk'}(s)` and dividing gives `e_{kc'}(s x_{k'i} r)`, and `Σ_i x_{k'i} y_{ik'} = 1`
     gives `e_{kc'}(1) ∈ ker φ`.
5. For `N ≥ 3`, `e_{kc'}(1)` normally generates `EL_N(R)` (commutators and signed permutations), so `φ` is trivial.
