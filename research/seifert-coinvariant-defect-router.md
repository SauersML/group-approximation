---
rg: 2
id: seifert-coinvariant-defect-router
kind: claim
title: The (3,4,infinity) monodromy funnels all gluing twists to one cyclic defect
distinct_from:
  two-cone-central-router-determinant: that is the abstract arithmetic after a central presentation is already available; this claim records the stronger source-specific fact that monodromy and the cusp filling actually collapse the rank-four lattice to that presentation.
  central-word-state-face-compiler: that asks for a nonlinear state-face compiler in approximation theory; this is an exact integral monodromy and fundamental-group computation.
artifacts:
  - research/artifacts/seifert-coinvariant-router-2026-08-23.md
---

For the explicit rank-four lattice representation of the `(3,4,infinity)`
triangle group in the uploaded `s6.pdf` manuscript, let `Lambda_tor` be the
cusp vanishing lattice and let

```text
gamma : Lambda -> Z
```

be the invariant primitive coordinate used there.  Then

```text
sum_g im(A(g)-I) = ker(gamma),
Lambda_G ~= Z via gamma,
```

and the smallest `<A_1,A_2>`-invariant subgroup containing `Lambda_tor` is
exactly `ker(gamma)`.  Consequently the filling relations kill every lattice
direction except the image `c` of a `gamma=1` vector, and the three discrete
gluing parameters enter only through

```text
ell_0, ell_1=gamma(v_1), ell_2=gamma(v_2).
```

The resulting fundamental group has presentation

```text
<c,x,y |
   c central,
   x y = c^ell_0,
   x^3 = c^ell_1,
   y^4 = c^ell_2>
```

and hence

```text
pi_1(X) ~= Z/|12 ell_0 - 4 ell_1 - 3 ell_2|Z.
```

For admissible twists the displayed integer is coprime to `12`.  In
particular the source choice `(ell_0,ell_1,ell_2)=(0,1,-1)` kills the residual
defect completely, while changing only the second elliptic twist to
`(0,1,1)` leaves `Z/7`.
