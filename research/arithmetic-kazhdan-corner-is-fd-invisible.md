---
rg: 2
id: arithmetic-kazhdan-corner-is-fd-invisible
kind: claim
title: The arithmetic Kazhdan corner gives an explicit nonzero finite-dimensional-radical element
distinct_from:
  arithmetic-leak-has-fd-null-laplacian-witness: that constructs exponentially finite-dimensional-null group-ring approximants; this identifies their fixed nonzero maximal-C-star limit.
  explicit-sl3-hnn-mark-is-fd-invisible: that is a group word in a larger centralizer HNN group; this is the Kazhdan-corner element of the maximal group C-star algebra of SL3(Z[1/p]) itself.
---

Let `A=SL_3(Z[1/p])`, `C=SL_3(Z)`, and let `p_C` be the Kazhdan
projection of `C`, viewed in `C^*_(max)(A)`.  For the denominator element
`h`, put

```text
z=(u_h-1)p_C in C^*_(max)(A).                           (AKC1)
```

Then `z` is nonzero but every exact finite-dimensional unitary
representation of `A` kills it.

Nonzero follows from the quasi-regular representation on `ell^2(A/C)`:
`p_C delta_C=delta_C`, while

```text
z delta_C=delta_(hC)-delta_C != 0.                      (AKC2)
```

For any exact finite-dimensional representation `sigma`, arithmetic
co-density gives `H^C=H^A`.  The operator `sigma(p_C)` projects onto this
common invariant space, where `sigma(h)-1` vanishes, so `sigma(z)=0`.

Moreover, the heat elements from
`arithmetic-leak-has-fd-null-laplacian-witness` converge in maximal norm:

```text
x_N -> p_C,
y_N=(h-1)x_N -> z.                                     (AKC3)
```

Thus the arithmetic projective-transfer wall is an explicit
finite-dimensional-radical versus MF-radical question for one fixed
Kazhdan-corner element.  The strong statement that every matrix-ultraproduct
representation of `A` kills `z` would suffice, but the terminal PTS route
needs only invisibility on the selected twice-adjoint representations
arising from arithmetic microstates.
