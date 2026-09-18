---
rg: 2
id: lee-szczarba-level-three-top-cohomology-is-steinberg
kind: claim
title: The principal congruence subgroups Γ_n(p) of SL_n(Z) are rational duality groups of dimension binom(n,2), and for p = 3 their top rational cohomology is the Steinberg module of SL_n(F_3) (Borel--Serre, Lee--Szczarba, Miller--Patzt--Putman)
distinct_from:
  sl3z-finite-index-fd-projective-multiplier-is-finite: that is about the finitely realizable part of H^2(K;T) for all finite-index K; this imports the top-degree rational cohomology of the principal congruence subgroups, with no profinite input.
  sl3-polynomial-congruence-subgroups-have-large-b2: that is the function-field analogue, conditional on Soulé's fundamental domain; this is the number-field statement, imported from the literature.
artifacts:
  - experiments/sl3z-level-three-betti-2026-09-17/tits-quotient-and-euler-count.py
---

**ESTABLISHED by citation** (`lee-szczarba-level-three-top-cohomology-is-steinberg-citation`).

Let `p` be a prime, `n >= 2`, and `Γ_n(p) = ker(SL_n(Z) -> SL_n(F_p))`. Put `d = binom(n,2)`.
Let `T_n(F)` be the Tits building of `SL_n(F)` and `St_n(F) = H~_(n-2)(T_n(F))`.

1. **Vanishing.** `H^q(Γ_n(p); Q) = 0` for `q > d`.
2. **Duality.** `Γ_n(p)` is a rational duality group of dimension `d` with dualizing module
   `St_n(Q)`. In particular `H^d(Γ_n(p); Q) ≅ (St_n(Q) ⊗ Q)_(Γ_n(p))`.
3. **Top degree at small primes.** The map `(St_n(Q))_(Γ_n(p)) -> H~_(n-2)(T_n(Q)/Γ_n(p))`
   induced by the quotient map is surjective for every `p`, and injective iff `p <= 5`.
4. **Quotient at `p <= 3`.** `T_n(Q)/Γ_n(p) ≅ T_n(F_p)`.
5. **Rank.** `St_n(F_p)` is a free `Z`-module of rank `p^d`.

**Case used in the graph.** For `n = 3`, `p = 3`: `d = 3`, and items 2--5 give
`H^3(Γ_3(3); Q) ≅ (St_3(Q))_(Γ_3(3)) ⊗ Q ≅ St_3(F_3) ⊗ Q ≅ Q^27`.
Coinvariants commute with `⊗ Q` because `⊗ Q` is right exact.

The artifact `experiments/sl3z-level-three-betti-2026-09-17/tits-quotient-and-euler-count.py`
recomputes item 5 at `n = p = 3`. `T_3(F_3)` is the point--line incidence graph of `PG(2,3)`,
with 26 vertices and 52 edges; it is connected, and its `H_1` is free of rank `27 = 3^3`.

**Not claimed.** The case `p >= 7`, where item 3 fails for injectivity, is not used.
