---
rg: 2
id: bk-relative-boundary-descends-or-is-positively-detected-proof
kind: route
title: Proof of the descent and dichotomy for the relative boundary
target: bk-relative-boundary-descends-or-is-positively-detected
requires: [bk-radical-traces-vanishing-on-boundary-are-zero, bk-radical-projection-quotients-are-toeplitz-infinite]
artifacts:
  - research/artifacts/bk-relative-lemma-b-dichotomy-2026-09-13.md
---

Item 1 (descent).  A densely finite l.s.c. trace `σ` on `A/I` with
`σ̂(π_*(G)) = 0` pulls back to `τ_0 = σ ∘ π ∘ q_J` on `R`, which is densely
finite because quotient maps carry `Ped(R)` onto `Ped(A/I)`; and `τ_0^(H) = 0`.
`bk-radical-traces-vanishing-on-boundary-are-zero` forces `τ_0 = 0`, hence
`σ = 0` since `π ∘ q_J` is onto.

Item 2 (dichotomy).  Six-term exactness gives
`ker(π_* : K_0(A) → K_0(A/I)) = im(K_0(I) → K_0(A))`.  If `π_*(G) = 0` then
`G ⊆ im(K_0(I))` and the lift is annihilated by `τ|_I`, faithful densely finite
on `I`; the extension `0 → I → A → A/I → 0` has nuclear QD UCT quotient, so
Brown--Dadarlat Theorem 3.4 reduces quasidiagonality to vanishing of one boundary
index.  If `π_*(G) ≠ 0` then item 1 gives the surviving property on `A/I`;
`π_*(G) = (q_K)_*(H)` is the boundary of `0 → R/K → E/K → E/R → 0`, so
`π_*(G) ∩ K_0^+(R/K) ≠ {0}` makes `E/K` not stably finite by Spielberg
(Brown--Dadarlat Prop 4.1), and a nonzero projection class of a stably finite
quotient cannot map to `0`, so no faithful embedding into a stably finite QD
algebra kills `G`.

Item 3 (forced).  Corollary 10 of
`bk-radical-projection-quotients-are-toeplitz-infinite` provides, in a type I
counterexample, a class of `H` with strictly positive rank at every elementary
point, i.e. the escaping-with-positive-detection case.

Full derivation and model tests: the cited artifact.
