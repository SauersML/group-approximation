---
rg: 2
id: clifford-compressor-site-growth
kind: claim
title: The Clifford compressor index is infinite at every strict positive compressor
distinct_from:
  relative-wall-commutant-growth: That claim is the model-free equivalence between existence of a wall and properness of one relative-commutant inclusion; this one computes the actual Pimsner--Popa index in the explicit Clifford crossed product, for every element of the positive compression monoid at once.
  commutant-no-growth: That claim is the finite-dimensional collapse for a genuine representation, where the index is forced to be one; this one exhibits infinite index in a fixed II_1 model and identifies the new Clifford modes with a monoid divisibility complement.
  commutator-compressor-carries-no-wall: That claim excludes a wall whenever two factors of a commutator compressor have finite growth index; this one determines the indices for the monomial-cone pair and thereby shows that exclusion is vacuous in the Clifford model.
  finite-site-orbits-invariant-clifford-kernel: That claim is about actions all of whose site orbits are finite; here every new site has an infinite orbit, which is what makes the Clifford monomials orthogonal to the commutant.
artifacts:
  - notes/TRUE_CLIFFORD_COMPRESSOR_SITE_GROWTH.md
---

For the monomial-cone Kun--Thom pair `Gamma=E_r(A[Lambda_+])`,
`G=E_r(A[Lambda]) semidirect SL_3(Z)`, `X=G/Gamma`, in the Clifford crossed
product `M_Cl=Cl(X) crossed_product G` with `N=M_Cl intersect pi(Gamma)'`,
the growth index of every element of the positive monoid
`L_+=SL_3(Z) intersect M_3(N)` is

```text
lambda(s)=[Ad pi(s)(N):N]=1 if s is a permutation matrix,
                          =infinity otherwise.
```

The `Gamma`-fixed site set contains an injective copy of `L_+` via
`p |-> p^(-1)Gamma`, the compressor acts on it by right division, and the new
Clifford modes are indexed by `L_+ minus L_+ s` — infinite unless `s^(-1)`
is again nonnegative, i.e. unless `s` is a unit.  Each new site has infinite
`Gamma`-orbit, so the Kazhdan average kills its Clifford monomials and a
Pimsner--Popa test projection of trace `2^(-k)` gives index at least `2^k`.

This settles Section 7 item 3 of `notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_
GROWTH.md` and strengthens its Corollary 7 from a disjunction to a
determination.

The relative commutant is computed alongside, as far as the external cosets
go.  `N intersect Cl(X)=Cl(X)^Gamma=Cl(X_fin)^Gamma` where `X_fin` is the
finite-orbit locus, and on the external cosets `ell Gamma` the orbit is a
single point if `ell` is a permutation matrix and infinite otherwise — no
middle ground — so that part of the fixed algebra is exactly
`Cl(iota(L_+))`.  Under `p |-> p^(-1)Gamma` the tower becomes right division
by `s` on the compression monoid, adjoining the modes `L_+ minus L_+ s` at
each step.  That system alone is the one-sided Clifford shift and is Connes
embeddable inside `R`; the difficulty is the coupling to the higher Fourier
degrees and to the rest of `G`, not the tower.  General cosets `(u,ell)Gamma`
and the higher-degree part of `N` are not computed.

**Scope, for reuse across the invariant-graph family.**  The site count is
graph independent — `X^Gamma` and its translates depend only on the `G`-set.
The *index* statement is not: the test projection pairs new sites into
factors `(1+i c c')/2`, which is a projection only when the two Majoranas
anticommute, i.e. only when the two sites are adjacent in the graph.  In the
complete graph every distinct pair is adjacent; for a general invariant graph
`S` one needs `k` disjoint `S`-edges inside `s X^Gamma minus X^Gamma`, or a
pairing of each new site with an `S`-adjacent old site, which also works
because `E_N` is an `N`-bimodule map and old-site Majoranas lie in `N`.
Neither has been checked for the sparse members.  It does not bear on Connes embeddability: the same
infinite-index tower shape is realized by the one-sided Clifford shift inside
the hyperfinite II_1 factor.
