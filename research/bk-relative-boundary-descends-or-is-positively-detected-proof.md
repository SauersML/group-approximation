---
rg: 2
id: bk-relative-boundary-descends-or-is-positively-detected-proof
kind: route
title: Proof of the descent and the blocked filtration route for the relative boundary
target: bk-relative-boundary-descends-or-is-positively-detected
requires: [bk-radical-traces-vanishing-on-boundary-are-zero, bk-radical-projection-quotients-are-toeplitz-infinite]
artifacts:
  - research/artifacts/bk-relative-lemma-b-dichotomy-2026-09-13.md
---

Item 1 (descent).  A densely finite l.s.c. trace `σ` on `A/I` with
`σ̂(π_*(G)) = 0` pulls back to `τ_0 = σ ∘ π ∘ q_J` on `R`, densely finite because
quotient maps carry `Ped(R)` onto `Ped(A/I)`, with `τ_0^(H) = 0`.
`bk-radical-traces-vanishing-on-boundary-are-zero` forces `τ_0 = 0`, hence
`σ = 0` since `π ∘ q_J` is onto.

Item 2 (absolute obstruction).  Brown--Dadarlat (remark after Definition 4.4): a
nonzero projection class of a stably finite algebra is nonzero, so a faithful
embedding into a stably finite QD algebra killing `G` needs `G ∩ K_0^+(A) = {0}`.
For `J = 0`, `H ∩ K_0^+(R) = {0}` by Spielberg (Prop 4.1) applied to
`0 → R → E → E/R → 0` with `E` stably finite.  `G ∩ K_0^+(A) ≠ {0}` is, by the
same Spielberg criterion for `0 → A → E/J → E/R → 0`, equivalent to `E/J` not
stably finite.

Item 3 (filtration stall).  Six-term exactness gives
`ker(π_* : K_0(A) → K_0(A/I)) = im(K_0(I) → K_0(A))`.  If `π_*(G) = 0` then
`G ⊆ im(K_0(I))` and the lift is annihilated by `τ|_I`, faithful densely finite;
the extension `0 → I → A → A/I → 0` has nuclear QD UCT quotient, so
Brown--Dadarlat Theorem 3.4 reduces the remaining step to vanishing of one
boundary index.  If `π_*(G) ≠ 0`, item 1 gives the surviving property on `A/I`;
and if `π_*(G) ∩ K_0^+(A/I) ≠ {0}` then the descended subgroup is non-singular in
`K_0(A/I)`, so by item 2 no faithful embedding of `A/I` into a stably finite QD
algebra kills it — the peeling route cannot factor through `A/I` — and, since
`π_*(G) = (q_K)_*(H)` is the boundary of `0 → R/K → E/K → E/R → 0`, Spielberg
makes `E/K` not stably finite.

Item 4 (forced).  Corollary 10 of
`bk-radical-projection-quotients-are-toeplitz-infinite` gives, in a type I
counterexample, a class of `H` with strictly positive rank at every elementary
point, so `π_*(H) ∩ K_0^+(R/K) ≠ {0}` and the boundary is not ideal-captured
through those quotients.

Full derivation and model tests: the cited artifact.
