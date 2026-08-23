---
rg: 2
id: seifert-coinvariant-defect-router-proof
kind: route
title: Collapse the monodromy lattice and apply the central determinant router
target: seifert-coinvariant-defect-router
requires: [two-cone-central-router-determinant]
artifacts:
  - research/artifacts/seifert-coinvariant-router-2026-08-23.md
---

## Source import and reduction

The uploaded manuscript `s6.pdf`, *A compact complex threefold fibred by tori
over the projective line, and the six-sphere*, gives the required integral
input explicitly.

Lemma 2.7 proves

```text
Sigma_Lambda := sum_g im(A(g)-I) = ker(gamma),
Lambda_G = Lambda/ker(gamma) ~= Z via gamma,
```

and also that the smallest `<A_1,A_2>`-invariant subgroup containing the cusp
vanishing lattice `Lambda_tor` is `ker(gamma)`.  Thus, after the cusp filling
kills `Lambda_tor` and normal closure under the two elliptic monodromies is
taken, the image of `Lambda` is one infinite cyclic group.  Write its
primitive generator as `c`, represented by any lattice vector of `gamma=1`.

Remark 6.8 identifies the complete discrete gluing data as
`(ell_0,ell_1,ell_2)`, with `ell_j=gamma(v_j)` at the elliptic points and
`ell_0` the cusp regluing integer.  Lemma 7.16 fixes the relative signs of the
two elliptic relations: both local rotation conventions are coupled by the
requirement that their product generate the unique cusp, so the two filling
relations have the same sign convention.

Theorem 7.17 then obtains by van Kampen

```text
<c,x,y |
   c central,
   x y = c^ell_0,
   x^3 = c^ell_1,
   y^4 = c^ell_2>.
```

Apply `two-cone-central-router-determinant` with

```text
m=3, n=4, e=ell_0, a=ell_1, b=ell_2.
```

Since `gcd(3,4)=1`, this gives

```text
pi_1(X) ~= Z/|12 ell_0 - 4 ell_1 - 3 ell_2|Z
```

whenever the determinant is nonzero.  Theorem 7.17 further proves from the
admissibility conditions `3 not| ell_1` and `ell_2` odd that this integer is
coprime to `12`, hence is indeed nonzero.  Finally the source's two explicit
choices give

```text
(0,1,-1) -> |-4+3| = 1,
(0,1, 1) -> |-4-3| = 7,
```

which are the claimed trivial and `Z/7` residual defects.
