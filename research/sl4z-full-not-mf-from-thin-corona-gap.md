---
rg: 2
id: sl4z-full-not-mf-from-thin-corona-gap
kind: route
title: An MF embedding of the full algebra is a corona representation in which the thin coset vector forces norm one
target: sl4z-full-cstar-is-not-mf
requires: [sl4z-corona-reps-have-thin-relative-spectral-gap, sln-z-thin-quasiregular-not-weakly-contained-in-fd]
artifacts:
  - research/artifacts/sl4z-thin-corona-gap-reduction-2026-09-16.md
---

The artifact, Lemma 5.1 and Theorem 7.1, gives the full proof.

1. **Embedding.**  Suppose `iota : C*(SL_4(Z)) -> Q_k` is an injective *-homomorphism.  It
   is isometric.
2. **Unitize.**  `e = iota(1)` is a projection in `Q_k`.
   - It lifts to projections `P_n` of ranks `r_n`, and `e Q_k e` is isomorphic to `Q_r`.
   - Corestricting gives a unital *-homomorphism `iota' : C*(SL_4(Z)) -> Q_r` with the same
     norms.
   - Since `e != 0`, infinitely many `r_n` are positive.  Discarding the indices with
     `r_n = 0` does not change `Q_r`.
3. **Norm one.**  By item 2 of `sln-z-thin-quasiregular-not-weakly-contained-in-fd`,
   `||x|| >= ||sigma_C(x)|| = 1`.  So `||iota'(x)|| = ||x|| = 1`.
4. **Contradiction.**  `sl4z-corona-reps-have-thin-relative-spectral-gap` says
   `||iota'(x)|| < 1`.

The same four steps apply to any *-homomorphism `psi` into a matrix corona with
`||psi(y)|| >= ||sigma_C(y)||` for all `y`.  In particular they apply to an embedding of
`sigma_C(C*(SL_4(Z)))`, and to an embedding of `C*(Lambda)` for an overgroup `Lambda`,
restricted to `C*(SL_4(Z))`.
