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
- **Relatively-icc form (2026-08-21).**  For group von Neumann algebras,
  `L(H)' cap L(G) = C` when the subgroup `H` is relatively icc in `G` (every
  `g != e` has infinite `H`-conjugacy class); `SL_n(Z)` is relatively icc in
  `SL_n(Z[1/p])` (a non-central `g` has finite `SL_n(Z)`-centralizer, so
  infinite conjugacy class).  Hence `A' cap B = C`, i.e. `L(SL_n(Z))` is an
  IRREDUCIBLE subfactor of `L(SL_n(Z[1/p]))`.  So `(RCC)`
  `A' cap M = B' cap M` is exactly a **commutant-absorption**: the relative
  commutant of the (T) subalgebra `A`, on passing from `B` to the ambient
  matrix ultraproduct `M`, must not acquire anything outside `B' cap M`.
  Caution (a wrong turn ruled out): one cannot argue `A' cap M = C` -- in the
  hyperlinear scenario `A' cap M` necessarily contains `L(<t>) = L(Z)` (the
  HNN letter centralizes `SL_n(Z)`, so `C_G(SL_n(Z)) = <t>`), so `A' cap M`
  is genuinely nontrivial; the content is only the INCLUSION
  `A' cap M subseteq B' cap M`, which the extra element `k = u_t` violates
  iff `G` is hyperlinear.
- **1-bounded entropy.**  For the higher-rank pair
  (`sl3-pair-relative-commutant-route`) both group factors have property (T)
  hence 1-bounded entropy zero (Jung; Hayes arXiv:1505.06682), which
  constrains the relative commutants to `h = 0` algebras (no free-group-
  factor content); for the `SL_2` pair the subgroup is only Haagerup and
  this tool does not apply on the subgroup side, so the `SL_3` pair is the
  one where 1-bounded-entropy absorption has a chance to prove `(RCC)`.
- **Proper proximality.**  `SL_2(Z)` (and `SL_3(Z)`) are properly proximal
  (Boutonnet--Ioana--Peterson, arXiv:1809.01881), so `L(SL_2(Z))` is
  solid/rigid and its commutants are controlled; a properly-proximal
  criterion for relative commutants inside a matrix ultraproduct (as opposed
  to a crossed product) is the missing form.  Alekseev--Thom Open Problem
  6.2 is exactly this collapse in general; `(RCC)` is its most explicit
  instance, so it is genuinely open, not a known theorem.
- **What a counterexample is.**  A faithful `pi` and a unitary `k in M`
  with `[k, pi(SL_2(Z))] = 0` but `[k, pi(diag(2,1/2))] != 0`; such a `k`
  would make the HNN group hyperlinear and would refute both `(RCC)` and,
  through it, DV-style stability.
- **Explicit falsification gate.**
  `coset-bernoulli-ce-refutes-relative-commutant-collapse` shows that Connes
  embeddability of

  ```text
  L^infinity(K^(A/C)) rtimes A,
  A=SL_2(Z[1/2]), C=SL_2(Z),
  ```

  would refute `(RCC)`: the coordinate at `C` commutes with `C` but is moved
  by every element of `A-C`.  This is conditional, because soficity/CE of
  this generalized Bernoulli action with nonamenable stabilizer is not known.
