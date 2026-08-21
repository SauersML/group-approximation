---
rg: 2
id: sl3-pair-relative-commutant-route
kind: claim
title: The higher-rank pair SL3(Z) in SL3(Z[1/2]) gives the commutant-collapse route a genuine property (T) spectral gap and avoids the pi1 obstruction
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  relative-commutant-collapse-for-sl2-pair: that is the SL_2 pair, where the subgroup has only the Haagerup property so L(C) has no spectral gap; this uses SL_3(Z), which has property (T), so L(C) is rigid in M, and it avoids the infinite-pi1 condition that forces Dogon--Vigdorovich to SL_2.
  hnn-over-codense-kazhdan-subgroup-not-hyperlinear: that consumes flexible HS-stability of the base, which is VACUOUS for SL_3(Z[1/2]) (an infinite hyperlinear (T) group is not stable); this uses the relative-commutant form, which does not reference stability.
---

Take `C = SL_3(Z)`, `A = SL_3(Z[1/2])`, `a_1 = diag(2, 1, 1/2)`, and
`G = <A, t | [t, C] = 1>`.  Then:

1. `C = SL_3(Z)` has property (T) (higher rank), with a uniform Kazhdan
   constant; so `L(C)` has spectral gap in every tracial `M supseteq L(C)`
   (the conjugation action has isolated fixed-point space).
2. The pair is co-dense: every finite-dimensional representation of `A`
   factors through a congruence quotient `SL_3(Z/m)`, `gcd(m,2) = 1`
   (congruence subgroup property, higher rank), and `SL_3(Z)` surjects onto
   each by strong approximation.  So `rho(C)' = rho(A)'` for all
   finite-dimensional `rho`, and `C` is commensurated by `A`
   (`a_1` conjugates `C` to a commensurable copy; Schlichting completion
   `SL_3(Q_2) supseteq SL_3(Z_2)`).

By `hnn-route-is-relative-commutant-collapse` (whose proof only used
co-density and Britton, not stability), `G` is not hyperlinear as soon as

```text
pi(SL_3(Z))' cap M  =  pi(SL_3(Z[1/2]))' cap M                          (RC3)
```

in the matrix ultraproduct carrying `G`'s regular trace.

**Why this pair is better.**
- **Property (T) of the subgroup.**  `SL_3(Z)` is Kazhdan, so `k in
  pi(C)' cap M` sits in a spectrally isolated (rigid) subspace; the
  Haagerup property of `SL_2(Z)` gave no such gap.  Peterson's spectral-gap
  rigidity for (T) subalgebras is directly applicable.
- **No pi_1 obstruction.**  Dogon--Vigdorovich's central-extension route
  needs `pi_1(G(R))` infinite, which fails for `SL_3(R)` (`pi_1 = Z/2`),
  forcing them to `SL_2`.  The commutant-collapse route uses no central
  extension, so `SL_3` (and every higher-rank `SL_n`, `Sp`, etc.) is
  admissible, widening the search for a pair where `(RC3)` is provable.

## Attempts

- **The remaining content of `(RC3)`.**  `k in pi(C)' cap M` lies in a
  space `L(C)' cap M` that `a_1`-conjugation preserves (commensurability +
  (T) inherited by finite index make `L(a_1 C a_1^(-1))' cap M =
  L(C)' cap M`).  So `A` acts on `L(C)' cap M` by conjugation, and `(RC3)`
  says the `a_1`-fixed points of this action are all of it, i.e. the
  commensuration dynamics on the rigid space `L(C)' cap M` is trivial.
  This is the precise open point; property (T) supplies the rigidity of the
  space but not yet the triviality of the `a_1`-action on it.
- **Possible obstruction.**  If `A` itself has (T) and is hyperlinear, one
  must check `(RC3)` is not FALSE for a structural reason (a genuine
  `a_1`-non-fixed `k`), which would make `G` hyperlinear and kill this pair
  while leaving the goal open.  The `SL_2` and `SL_3` pairs may behave
  oppositely here, which is itself informative.
- **Tool.**  Peterson--Thom / Bekka character rigidity holds for
  `SL_3(Z[1/2])` too (higher rank), giving hyperfinite HS-stability by the
  same DV Prop 8.3; the residual non-hyperfinite gap is again `(RC3)`.
