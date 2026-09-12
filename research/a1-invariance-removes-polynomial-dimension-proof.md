---
rg: 2
id: a1-invariance-removes-polynomial-dimension-proof
kind: route
title: Remove polynomial variables unstably, then stabilize over the two-torus
target: rank-five-laurent-k2-stability-is-dimension-free
requires:
  - sinchuk-a1-invariance-for-a4-containing-types
  - stable-laurent-k2-has-minimal-three-symbol-packet
---

The coefficient ring

```text
A=k[x_1^(+-1),x_2^(+-1)]
```

is regular, noetherian, and has Krull dimension two.  Classical injective
stability therefore gives, for `r>=5`,

```text
K2(r,A) ~= K2(A).                                            (AIP1)
```

For the root system `A_(r-1)`, the hypothesis `r>=5` is exactly the
condition that the root system contain `A_4`.  Apply unstable A1-invariance
successively to the regular rings obtained while adjoining
`x_3,...,x_d`.  This gives

```text
K2(r,A) ~= K2(r,R_d).                                        (AIP2)
```

Stable Quillen homotopy invariance gives the bottom isomorphism in the
natural square

```text
K2(r,A)  --------->  K2(r,R_d)
   |                      |
   | stabilize            | stabilize
   v                      v
K2(A)    --------->  K2(R_d).                                (AIP3)
```

The top arrow is (AIP2), the bottom arrow is stable homotopy invariance,
and the left arrow is (AIP1).  Naturality makes (AIP3) commute, so the
right stabilization arrow is an isomorphism.  This proves (RFL1).

The twofold Bass fundamental theorem computes

```text
K2(A) ~= K2(k) (+) 2 K1(k) (+) K0(k)
      ~= Z (+) C_(q-1) (+) C_(q-1).                         (AIP4)
```

The boundary calculation in the three-symbol packet identifies its three
generators with (RFL3), proving (RFL2).  Since the fixed-rank Steinberg
kernel maps isomorphically to central stable `K2`, it is central as well.
Quotienting by the generators therefore gives (RFL4), and the same
`F_ell^3` quotient used in the minimality proof shows that three central
relators are necessary when `q>2`.

The proof deliberately stops at `r=5`: neither the A1-invariance theorem
used in (AIP2) nor the dimension-two stability theorem (AIP1) supplies the
needed isomorphism in ranks three or four.
