---
rg: 2
id: relative-commutant-collapse-for-sl2-pair
kind: claim
title: In any matrix ultraproduct the relative commutant of L(SL2(Z)) equals that of L(SL2(Z[1/2]))
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  approximate-collapse-for-kt-compressor: that is the same statement for the EL_r(F_q[x]) compressed Kazhdan copy; this is the explicit arithmetic pair SL_2(Z) <= SL_2(Z[1/2]), where commensuration and character rigidity are available.
  iwahori-local-global-defect-question: that is the representation-variety (flexible stability) form; this is the intrinsic II_1-factor form, weaker to state and possibly easier because it never leaves the ultraproduct.
---

Let `M = prod_U M_(d_n)` be a tracial matrix ultraproduct and
`pi : SL_2(Z[1/2]) -> U(M)` any trace-preserving (regular-trace)
representation, `pi(SL_2(Z))'' = L(SL_2(Z))`, `pi(SL_2(Z[1/2]))'' =
L(SL_2(Z[1/2]))`.  Then

```text
pi(SL_2(Z))' cap M  =  pi(SL_2(Z[1/2]))' cap M.                         (RCC)
```

Equivalently, `L(SL_2(Z))` has spectral gap inside `M` relative to the
overalgebra: no unitary of `M` commutes with `L(SL_2(Z))` but not with
`L(SL_2(Z[1/2]))`.  By `non-hyperlinear-from-relative-commutant-collapse`
this produces an explicit non-hyperlinear group.

## Attempts

- **Commensuration.**  `SL_2(Z)` is commensurated by `SL_2(Z[1/2])` with
  Schlichting completion `SL_2(Q_2) supseteq SL_2(Z_2)`; the inclusion
  `L(SL_2(Z)) subseteq L(SL_2(Z[1/2]))` is the associated Hecke inclusion.
  Popa's spectral-gap/mixing criteria for such inclusions are the tool.
- **Character rigidity input.**  Peterson--Thom character rigidity of
  `SL_2(Z[1/2])` and the resulting HYPERFINITE HS-stability (Dogon--
  Vigdorovich Thm 6.2 + Prop 8.3) give `(RCC)` when the ambient piece is
  amenable; the open case is a non-amenable commutant, i.e. exactly when
  `L(SL_2(Z[1/2]))` fails to have spectral gap in `M`.
- **Relation to flexible stability.**  Flexible HS-stability of
  `SL_2(Z[1/2])` implies `(RCC)` (correct microstates, then co-density);
  `(RCC)` may be strictly weaker since it only asks about the commutant of a
  fixed subalgebra, not correction of the whole representation.
- **What a counterexample is.**  A faithful `pi` and a unitary `k in M`
  with `[k, pi(SL_2(Z))] = 0` but `[k, pi(diag(2,1/2))] != 0`; such a `k`
  would make the HNN group hyperlinear and would refute both `(RCC)` and,
  through it, DV-style stability.
