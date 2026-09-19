---
rg: 2
id: kt-intrinsic-subfactor-data-does-not-see-ambient-wall-proof
kind: route
title: Compare the constant group-factor copy with the canonical Clifford crossed product
target: kt-intrinsic-subfactor-data-does-not-see-ambient-wall
requires:
  - kt-compressor-pair-group-factor-ultrapower-has-no-leak
  - clifford-compressor-site-growth
---

Set `P=L(Lambda)` and `N=L(Gamma)`.

For the first ambient, embed `L(G)` diagonally into `L(G)^omega`.  The
`q=2`, `d=3` Kun--Thom group has trivial central scalar subgroup, so
`kt-compressor-pair-group-factor-ultrapower-has-no-leak` gives

```text
P' cap L(G)^omega=N' cap L(G)^omega=C.
```

For the second ambient, use the canonical group unitaries in
`M_Cl=Cl(G/Gamma) crossed_product G`.  They have the regular group trace, so
the induced maps of `P<N` are faithful and trace preserving.  The strict
positive compressor case of `clifford-compressor-site-growth` identifies

```text
N' cap M_Cl < P' cap M_Cl
```

and proves that this inclusion has infinite Pimsner--Popa index.

The same site-orbit computation also proves `[Gamma:Lambda]=infinity`: the
site `t Gamma` has `Gamma`-stabilizer

```text
Gamma cap t Gamma t^(-1)=Lambda,
```

and Step 3 of `clifford-compressor-site-growth-proof` proves that its
`Gamma`-orbit is infinite.  For subgroup factors, the canonical
`L(Lambda)`--`L(Lambda)` decomposition of `L^2(L(Gamma))` over left cosets
gives `[L(Gamma):L(Lambda)]=[Gamma:Lambda]=infinity` (equivalently, the
standard conditional expectation has the usual group-subfactor index).

Everything called intrinsic in the claim is functorial under an isomorphism
of tracial inclusions.  Here there is no comparison map to construct: both
ambient embeddings restrict to the very same canonical inclusion
`L(Lambda)<L(Gamma)`.  Consequently its Jones index, standard invariant and
bimodule category coincide tautologically, although the ambient relative
commutants differ.

Finally, if `x_1,...,x_k in L(Gamma)` and `p` is a noncommutative
`*`-polynomial, trace preservation gives in either ambient

```text
tau_M(p(x_1,...,x_k))=tau_(L(Gamma))(p(x_1,...,x_k)),
||p(x_1,...,x_k)||_(2,M)=||p(x_1,...,x_k)||_(2,L(Gamma)).
```

Thus all fixed finite normalized-HS moment data of the inclusion agree.
Only a statistic quantifying over the ambient complement can distinguish the
two models.  The exact ambient index does so in the Clifford model, but the
explicit atom-refinement calculation in
`notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md`, Section 5, shows that this
index can diverge under an `O(sqrt(epsilon))` normalized-HS perturbation.
It therefore supplies no continuous finite-microstate inequality.

