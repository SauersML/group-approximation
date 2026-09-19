---
rg: 2
id: mikhailova-profinite-pinch-mf-visibility-proof
kind: route
title: Choose a closure point, kill its Britton pinch in every finite quotient and separate it in the compiler corona
target: mikhailova-profinite-pinch-is-mf-visible
requires:
  - mikhailova-positive-rope-is-not-lef
  - mf-safe-finite-presentation-compiler
  - matricial-stability-identifies-radicals
---

The Mikhailova edge `L` is not closed in the profinite topology of the
residually finite base `K`.  Choose

```text
k in closure_pf(L) \ L.                                    (MPMP1)
```

In `Gamma=<K,v | [v,L]=1>`, the word `w=[v,k]` is
Britton-reduced: the only possible pinch would require `k in L`.  Hence
`w!=1` in `Gamma`, and it remains nontrivial in the outer HNN extension `R`
because both HNN constructions embed their bases.

Let `phi:R->F` be any homomorphism to a finite group.  Its restriction to
`K` is a finite quotient model of `K`, so `(MPMP1)` gives
`phi(k) in phi(L)`.  Choose `l in L` with `phi(k)=phi(l)`.  The defining
relations give `[phi(v),phi(l)]=1`, and therefore

```text
phi(w)=[phi(v),phi(k)]=1.                                   (MPMP2)
```

Thus `w` lies in the finite residual of `R`.

On the other hand [[mf-safe-finite-presentation-compiler]] gives the positive
rope an injective homomorphism

```text
Theta:R -> U(prod_n M_(d_n) / direct-sum_n M_(d_n))         (MPMP3)
```

into a norm matrix corona.  Since `w!=1`, injectivity gives
`Theta(w)!=1`; equivalently the matrix words representing `w` stay a
positive operator-norm distance from the identity along a subsequence.  So
`w` is not in the MF radical, proving `(MPMV3)`.

Finally suppose `R` is point-norm matricially stable.  Since it is MF,
[[matricial-stability-identifies-radicals]] gives
`Rad_fd(R)=Rad_MF(R)=1`; hence some finite-dimensional unitary
representation detects `w`.  Such a representation cannot have finite
image, by `(MPMP2)`.  This proves that ordinary matricial stability, even if
available, leads to an infinite-image exact representation rather than a
non-MF contradiction.
