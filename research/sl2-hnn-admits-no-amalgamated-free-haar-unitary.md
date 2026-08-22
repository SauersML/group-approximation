---
rg: 2
id: sl2-hnn-admits-no-amalgamated-free-haar-unitary
kind: claim
title: No regular-trace matrix model of SL2(Z[1/2]) carries a Haar unitary in the SL2(Z)-centraliser that is free from the lattice factor with amalgamation over L(SL2(Z))
distinct_from:
  relative-commutant-collapse-for-sl2-pair: that forbids every subgroup-central unitary that is not ambient-central; this forbids only the ones with the amalgamated-free joint distribution an embedding of the HNN factor would supply, and is implied by the collapse.
  sl3-hnn-admits-no-amalgamated-free-haar-unitary: that is the rank-two pair, where property (T) of the subgroup makes the centraliser coordinatewise; this is the Dogon--Vigdorovich pair SL2(Z) in SL2(Z[1/2]), whose subgroup is only virtually free, so neither the interchange formula nor any spectral gap of the subgroup is available.
  sl2-half-stability-excludes-hnn-hyperlinearity: that is the dichotomy between non-hyperlinearity of the HNN group and failure of flexible stability; this names the operator-algebraic statement equivalent to the first horn.
---

OPEN.  Let `C = SL_2(Z) <= A = SL_2(Z[1/2])`, `B = L(C) subset N = L(A)`.
For every trace-preserving embedding `iota : N -> M` into a tracial matrix
ultraproduct, there is no unitary `k in B' cap M` with `E_B(k^n) = 0` for
all `n != 0` such that `N` and `W^*(B, k)` are free with amalgamation over
`B`.

By `hnn-hyperlinearity-is-amalgamated-free-haar-unitary` this is exactly
non-hyperlinearity of `G_2 = <SL_2(Z[1/2]), t | [t, SL_2(Z)] = 1>`, the
first horn of `sl2-half-stability-excludes-hnn-hyperlinearity`.  It is
implied by the collapse `(RCC)` of
`relative-commutant-collapse-for-sl2-pair`
(`sl2-amalgamated-free-exclusion-from-collapse`) and by flexible
Hilbert--Schmidt stability of `SL_2(Z[1/2])` together with the co-dense
`(tau)` pair (`sl2-amalgamated-free-exclusion-from-stability`), and it
feeds the goal through `non-hyperlinear-from-sl2-amalgamated-free-exclusion`.

## Attempts

- **Standard model.**  In `L(A)^omega` no leak exists at all
  (`arithmetic-pair-group-factor-ultrapower-has-no-leak`, the `n = 2`
  case, proved through abelian centralisers rather than property (T)), so
  every candidate lives in `L^2(M) (-) L^2(L(A))`.
- **Exact models.**  Along congruence microstates `pi_n(A) = pi_n(C)`
  coordinatewise, so any `k` commuting with `pi_n(C)` commutes with
  `pi_n(A)` and cannot be amalgamated-free; only exotic microstates of
  `SL_2(Z[1/2])`, far from every congruence representation, can carry a
  candidate (`sl2-half-stability-excludes-hnn-hyperlinearity`).  The
  subgroup `SL_2(Z)` is same-dimension HS-stable
  (`sl2-z-same-dimension-hs-stable`), so the restriction of any model to
  `C` is near an exact representation `sigma_n`, and `k_n` may be taken in
  the honest commutant `sigma_n(C)'`, a direct sum of multiplicity
  algebras; the enemy is then the position of `pi_n(h)` relative to that
  isotypic decomposition.
- **Popa's theorem does not apply** (`B` non-amenable), and the entropy
  fence of `hnn-hyperlinearity-is-amalgamated-free-haar-unitary` shows no
  1-bounded-entropy count can decide it.
