---
rg: 2
id: berend-asymptotically-isometric-quotient-model-proof
kind: route
title: Enumerate finite orbit representations and compare with dense finite restrictions of commutative algebras
target: berend-finite-orbit-quotients-are-asymptotically-isometric
requires:
  - berend-proper-quotients-have-decomposition-rank-at-most-two
  - berend-torus-actions-give-strongly-qd-polycyclic-groups
artifacts:
  - research/artifacts/stw99-lxxxvi-berend-frontier-2026-08-30.md
---

The Berend group is amenable and residually finite.  Bekka's theorem, in
the form used in Eckhardt's Lemma 2.2, says that `A` is residually finite
dimensional.  A finite-dimensional representation cannot be faithful on
`C(T^3)`.  The nonfaithful half of that lemma therefore makes it factor
through `C(F) ⋊ Z^2` for a finite invariant subset `F`.

There are only countably many finite orbits: every point on one is a
torsion point of `T^3`.  Enumerate the finite orbits and let `F_n` be the
union of the first `n`.  Residual finite dimensionality and the preceding
factorization give

`||a|| = sup_n ||q_n(a)||`.                                    `(BAQ1)`

The sequence on the right is increasing, because restriction from
`F_{n+1}` onto `F_n` intertwines the quotient maps.  This proves the norm
limit in `(BFQ2)`.  The decomposition-rank estimate is
`berend-proper-quotients-have-decomposition-rank-at-most-two`, and the norm
in a product modulo the direct sum is the limsup of the coordinate norms,
which proves `(BFQ3)`.

Here is the precise no-go for extracting decomposition rank from `(BFQ2)`.
For any compact metrizable space `Y`, choose increasing finite subsets
`E_n` whose union is dense.  Restriction gives quotient homomorphisms

`r_n : C(Y) -> C(E_n)`,  with  `lim_n ||r_n(f)|| = ||f||`,       `(BAQ2)`

and every target has decomposition rank zero.  Nevertheless
`dr(C(Y)) = dim(Y)`.  Taking `Y = [0,1]^d` makes the source decomposition
rank any prescribed finite `d`, and an infinite-dimensional compactum
gives infinite decomposition rank.  Thus no bound on the dimensions of an
asymptotically norming family of quotient targets can bound the
decomposition rank of the source.

The logical gap is directional.  The maps `q_n` send `A` out to easy
quotients, while decomposition rank requires finite-colour order-zero maps
back into `A` whose sums are contractive and approximate the identity.
Neither residual finite dimensionality nor `(BAQ1)` supplies those lifts.
