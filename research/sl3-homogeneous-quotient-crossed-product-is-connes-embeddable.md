---
rg: 2
id: sl3-homogeneous-quotient-crossed-product-is-connes-embeddable
kind: claim
title: The crossed product of SL3(Z[1/2]) acting on a cocompact quotient of SL3(Q_2) is Connes embeddable
invalidates:
  - nonhyperlinear-from-projective-trace-square-transfer
  - non-hyperlinear-from-sl3-relative-commutant-collapse
  - sl3-collapse-from-projective-transfer
  - sl3-amalgamated-free-exclusion-from-collapse
  - sl3-amalgamated-free-exclusion-from-projective-transfer
  - sl3-regular-double-collapse-from-projective-transfer
  - projective-transfer-gives-universal-filtered-actuator
  - rcc-from-spherical-leak-exclusion
  - exact-leak-refuted-by-projective-transfer
  - projective-transfer-proves-canonical-iwahori-transfer
  - sl3-coset-lamp-collapses-from-projective-transfer
distinct_from:
  coset-wreath-is-hyperlinear: that asks for matrix models of the coset Bernoulli wreath group over SL_3(Z[1/3]), whose lamp algebra is weakly mixing for the lattice; this asks for matrix models of an explicit crossed product by SL_3(Z[1/2]) of a compact homogeneous quotient on which every compact-subgroup piece acts profinitely, and it is not a group von Neumann algebra.
  sl3-dyadic-building-vertex-action-is-sofic: that is soficity of the countable vertex action; this is Connes embeddability of the crossed product of the compact lattice quotient, and neither is known to imply the other.
  sl2-homogeneous-quotient-crossed-product-is-connes-embeddable: that is the rank-one instance, where the acting group is an amalgam and the target algebra is an amalgamated free product of profinite algebras; this is the higher-rank instance whose truth would refute the top frontier hole of the goal.
  kun-thom-clifford-crossed-product-ce: that is a Clifford-twisted crossed product for the Kun--Thom compressor pair; this is an untwisted crossed product of a commutative algebra for the arithmetic pair.
---

**OPEN (two-sided).**  Let `Lambda' < SL_3(Q_2)` be a torsion-free cocompact
lattice with at least two `SL_3(Z_2)`-orbits on `X = SL_3(Q_2)/Lambda'`.
Claim: the II_1 factor

```text
M = L^infinity(X) rtimes SL_3(Z[1/2])                                 (SH1)
```

is Connes embeddable.

**Stakes both ways.**  By
`homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse`, `(SH1)`
embeddable refutes `sl3-pair-relative-commutant-route`,
`projective-trace-square-transfer-for-sl3-pair` (the goal's top frontier
hole, `(PTS1)`), `projective-commutant-transfer-for-arithmetic-pair`
(`(PRT1)`) and `no-spherical-leak-in-matrix-ultraproducts`; hence the
`invalidates` keys on every route that consumes one of those four claims.
Conversely, any proof of the collapse must prove that the explicit algebra
`(SH1)` has **no** matrix microstates, which would be the first explicit
non-Connes-embeddable factor built from arithmetic alone, with no game or
constraint system.  Neither outcome by itself produces a nonhyperlinear
group: `M` is not a group factor, and a leak does not supply the
amalgamated-free Haar unitary that
`hnn-hyperlinearity-is-amalgamated-free-haar-unitary` requires.

**What is already known about `M`.**  Its restriction to `SL_3(Z)` is a
direct sum of copies of the profinite crossed product
`L^infinity(SL_3(Z_2)) rtimes SL_3(Z)`, with explicit congruence microstates
`M_([K:K_m]) (x) L(Gamma(m))`.  The only non-profinite ingredient is the
single unitary `u_h`, `h = diag(2,1,1/2)`, which conjugates the finite-index
subalgebra `L^infinity(X) rtimes (C cap h^-1 C h)` onto
`L^infinity(X) rtimes (h C h^-1 cap C)` inside that profinite algebra;
`SL_3(Z[1/2])` is not an HNN extension of `SL_3(Z)` (it has property (T)),
so `M` is a proper quotient of Ueda's HNN algebra of that partial
automorphism.  By `dense-s-arithmetic-translation-algebra-is-amplified-profinite`,
`M` is stably the crossed product `(N (x) B(l^2)) rtimes Lambda'` of a
Connes-embeddable II_infinity factor by the residually finite lattice
`Lambda'`.  The action `A` on `X` has no nontrivial finite factor (a finite
`A`-invariant partition would be `SL_3(Q_2)`-invariant by density, and
`SL_3(Q_2)` has no finite quotients), while `X` is a Cantor set on which
`h` acts by a homeomorphism mapping each level-`m` congruence cell onto a
union of level-`(m + O(1))` cells.

## Attempts

- **Finite building quotients as permutation models.**  The finite sets
  `K_m \ SL_3(Q_2) / Lambda'` carry Hecke correspondences, not actions of
  `A`; `h` does not descend to any level.  A permutation (Cartan) model of
  the action would make every `C`-invariant label nearly `A`-invariant in
  the model, against `(HQ3)`, so as for the coset Bernoulli action any
  matrix model must embed `L^infinity(X)` non-Cartanly.  The soficity of the
  action is therefore expected to fail by the same mechanism as Kun--Thom
  Corollary D, but that is not proved here and would not decide `(SH1)`.
  The exact common-level obstruction is proved separately by
  `homogeneous-k-orbit-factor-has-no-finite-a-refinement`:
  the nontrivial finite `K`-orbit factor has no finite `A`-equivariant
  refinement.  This does not exclude non-Cartan matrix microstates.
- **Amalgamated-free-product permanence.**  Brown--Dykema--Jung's theorem
  needs a hyperfinite base; for `n = 3` there is no amalgam decomposition
  at all, and for the `n = 2` sibling the base `L^infinity(X) rtimes (C cap g C g^-1)`
  is non-amenable.  Deferred until a finite-index-base amalgam permanence
  theorem exists.
- **Crossed-product permanence via `(DT2)`.**  Requires that the explicit
  right-translation action of the residually finite lattice `Lambda'` on the
  embeddable II_infinity factor `N (x) B(l^2)` be approximately implementable
  on microstates; no general theorem applies, and the action is not
  approximately inner (it permutes the `K`-coset corners freely).
- **Exact-face stability.**  If `SL_3(Z)` were flexibly HS-stable, any
  microstate sequence of `M` would restrict on `SL_3(Z)` to near-genuine
  congruence representations, and `u_h` would reduce to the one-unitary
  system of `arithmetic-pair-is-not-relatively-embeddable`; the Lambda-exact
  face analysis of the collapse lane then applies verbatim to `M`.  So
  `(SH1)` together with flexible HS-stability of `SL_3(Z)` would force the
  one-unitary system to be unstable; nothing is known about either.
- **Flat towers cannot be vertex-orbit permutation towers (2026-08-25).**
  `homogeneous-quotient-near-genuine-microstates-are-deep` proves that any
  near-genuine microstate sequence is a flat congruence tower of depth
  `Omega(1/epsilon)`.  The natural candidates, direct sums of the
  permutation representations of `C` on its vertex orbits
  `Omega_lambda = C . (lambda-translate of o)` (`lambda` a dominant coweight,
  `|Omega_lambda| ~ p^(<2 rho, lambda>)`), fail the flatness requirement:
  `h` maps the `C_0`-orbit of the base point of `Omega_lambda` bijectively
  onto the `C_1`-orbit of the base point of `Omega_(lambda + lambda_h)`, so
  exact `C_0`-isotypic matching level by level forces equal multiplicities
  along `h`-shifts, whereas flat level weights need multiplicities
  `~ p^(-<2 rho, lambda>)`.  Any flat tower must therefore match isotypic
  components across different orbit types; see the tree-case computation on
  `sl2-homogeneous-quotient-crossed-product-is-connes-embeddable`.
