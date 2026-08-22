---
rg: 2
id: arithmetic-leak-commutator-localizes-in-overlap-commutant
kind: claim
title: An arithmetic projective leak localizes to the commutant of the adjacent lattice overlap
distinct_from:
  sl3-lattice-inclusion-is-quasiregular-not-mixing: that constructs nonmixing vectors from finite-index intersections in a quasi-regular representation; this is an algebraic commutator identity valid in every exact representation and quantitatively in approximate matrix representations.
  finite-index-correction-is-equivalent-for-kazhdan-groups: that transfers flexible correction of an approximate group representation between a group and a finite-index subgroup; this localizes an external commutator unitary and does not correct the underlying representation.
  sl3-noncorrectable-lambda-sector-has-no-projective-leak: that asks to prove the localized commutator is scalar in canonical matrix ultraproducts; this identifies its exact finite-index overlap commutant and coboundary form but does not prove scalarity.
---

Let `Lambda<G` be a commensurated subgroup, `h in G`,
`M=Lambda cap h Lambda h^(-1)`, and let `pi:G->U(K)` be an exact unitary
representation.  If `U` centralizes `pi(Lambda)` and

```text
W=[U,pi(h)]=U pi(h) U^* pi(h)^*,
```

then

```text
W in pi(M)'.                                             (OL1)
```

The statement has a dimension-free approximate form.  Fix finite generating
sets of `Lambda` and `M`, fixed words for them in a finite presentation of
`G`, and fixed words `n_m in Lambda` with `m=h n_m h^(-1)` for each chosen
generator `m` of `M`.  There is a presentation-dependent constant `C` such
that, for every `delta`-representation `rho` and every unitary `U`,

```text
max_(m in S_M) ||[ [U,rho(h)], rho(m)]-1||_2
 <= C (delta + max_(s in S_Lambda)||[U,rho(s)]-1||_2).     (OL2)
```

For the SL3 pair, `M` has finite index in `Lambda`.  Hence every projective
leak in the perfect-lattice sector produces a nonscalar unitary of the
special coboundary form `[U,rho(h)]` which asymptotically centralizes this
fixed finite-index overlap.  This is the exact output of the commensurator
relations alone.  It is not yet a transfer theorem: the regular HNN leak
satisfies `(OL1)` with trace zero, so proving scalarity from `(OL2)` must use
matrix embeddability/canonical microstate information, not only the abstract
relations or finite index.
