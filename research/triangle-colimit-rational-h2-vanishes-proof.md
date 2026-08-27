---
rg: 2
id: triangle-colimit-rational-h2-vanishes-proof
kind: route
title: Cartan-Leray spectral sequence of the development with finite stabilizers
target: triangle-colimit-rational-h2-vanishes
requires: []
---

All references are to K. Brown, *Cohomology of Groups*, Chapter VII.7
(equivariant cohomology and its two spectral sequences).

**Setting.**  `Lambda` acts cellularly without inversions on the CW
complex `X`, with finite stabilizers `Lambda_sigma` and finitely many
orbits of cells; `X` is simply connected; `M` is a `Lambda`-module.
Equivariant cohomology `H^*_Lambda(X;M)` is the cohomology of
`Hom_Lambda(F (x) C_*(X), M)` for a projective resolution `F` of `Z`.

**Step 1 (second spectral sequence: injectivity in degree two).**  The
spectral sequence

```text
E_2^(p,q) = H^p(Lambda; H^q(X;M))  =>  H^(p+q)_Lambda(X;M)
```

has `H^0(X;M)=M` (connectedness) and `H^1(X;M)=Hom(H_1X,M) (+)
Ext(H_0X,M)=0` by the universal coefficient theorem, since `H_1(X)=0`
and `H_0(X)=Z` is free.  Hence `E_2^(*,1)=0`.  The only differentials
with target `E^(2,0)` are `d_2` from `E_2^(0,1)=0` and `d_3` from
`E_3^(-1,2)=0`, so `E_infty^(2,0)=E_2^(2,0)=H^2(Lambda;M)`, and
`E_infty^(2,0)` is the bottom filtration step, a subgroup of
`H^2_Lambda(X;M)`.  The same argument in degree one gives
`H^1(Lambda;M) = E_infty^(1,0) <= H^1_Lambda(X;M)`.  The filtration of
`H^2_Lambda` is `F^2=E_infty^(2,0)`, `F^1/F^2=E_infty^(1,1)=0`,
`H^2_Lambda/F^1=E_infty^(0,2) <= E_2^(0,2)=H^0(Lambda;H^2(X;M))`, and
the composite `H^2_Lambda(X;M) -> E_2^(0,2) <= H^2(X;M)` is the edge
homomorphism induced by `Hom_Lambda <= Hom_Z` (forgetting equivariance).
Therefore

```text
H^2(Lambda;M) = ker( H^2_Lambda(X;M) -> H^2(X;M) ).            (RH2)
```

**Step 2 (first spectral sequence: the equivariant group).**  The
spectral sequence `E_1^(p,q) = (+)_(sigma in Sigma_p) H^q(Lambda_sigma;
M_sigma) => H^(p+q)_Lambda(X;M)` runs over representatives `sigma` of
the `Lambda`-orbits of `p`-cells, with `M_sigma` the module `M` twisted by
the orientation character of `Lambda_sigma` on `sigma`.  Absence of
inversions makes every orientation character trivial.

(a) If `M` is a `Q`-vector space, then `H^q(Lambda_sigma;M)=0` for `q>0`
(averaging over the finite group), so `E_1` collapses to the cochain
complex `(+)_sigma M^(Lambda_sigma)`, i.e. the cellular cochains of the
quotient with coefficients in the stabilizer-fixed subspaces.  For
`M=Q` with trivial action this is the ordinary cellular cochain complex
of `X/Lambda`, so `H^k_Lambda(X;Q)=H^k(X/Lambda;Q)`.

(b) If `M=Z Lambda`, then `Z Lambda` restricted to the finite group
`Lambda_sigma` is a free `Z Lambda_sigma`-module (a basis is a set of
right coset representatives), hence cohomologically trivial in positive
degrees; `E_1` again collapses to `(+)_sigma (Z Lambda)^(Lambda_sigma)`.

**Step 3 (conclusion of (RH1)).**  With `M=Q`, Steps 1-2(a) give
`H^2(Lambda;Q) <= H^2(X/Lambda;Q)=0` and `H^1(Lambda;Q) <=
H^1(X/Lambda;Q)=0`.  Tensoring with `R` gives the real statements.

**Step 4 (the triangle formula (RH3)).**  For a triangle of finite
groups the quotient is one 2-simplex with face stabilizer `P_0`, edge
stabilizers `P_1,P_2,P_3` and vertex stabilizers `P_12,P_13,P_23`.  For a
`Q`-vector-space module `M`, Step 2(a) gives

```text
H^2_Lambda(X;M) = M^(P_0) / ( M^(P_1) + M^(P_2) + M^(P_3) ),
```

the cokernel of the cellular coboundary (signs do not affect the span),
and `(RH2)` identifies `H^2(Lambda;M)` with the kernel of the induced
map to `H^2(X;M)`.

**Step 5 (the instance).**  Simple connectivity of the development of a
developable complex of groups over a simply connected base, with respect
to the canonical morphism to its fundamental group (which is the colimit
of the local groups when the base is a simplex), is Bridson--Haefliger
III.C.3.13; finiteness of stabilizers, absence of inversions and
compactness of the quotient are immediate from the construction
`D(Y,phi)=(Lambda x Y)/~`.  The Kac--Moody lattices are colimits of
their rank-`<=2` Levi triangle by Abramenko--Mühlherr [AM97] (as quoted
in Rémy, arXiv:math/0402300, Theorem 5, for `2`-spherical type and
`q>3`); the instance (2,4,6) of `simple-kazhdan-kac-moody-lattices-exist`
is `2`-spherical with `q>1764^3`.
