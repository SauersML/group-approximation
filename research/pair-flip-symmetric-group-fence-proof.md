---
rg: 2
id: pair-flip-symmetric-group-fence-proof
kind: route
title: Restrict the group Fourier expectation and exhibit finite conjugacy-orbit sums
target: pair-flips-in-finitary-symmetric-group-add-no-envelope
requires: []
---

The subgroup `A` is invariant under the `Lambda`-action.  The group
inclusions `A<K` and `Lambda< K rtimes Lambda` therefore give `(PFS1)`; the
canonical group trace of the large semidirect product restricts to the
canonical trace of `A rtimes Lambda`, so the extension to group von Neumann
algebras is injective.  Fourier transform on the abelian group `A` identifies
its group algebra with `L^infinity({+-1}^Y,Haar)`, proving the first assertion.

For the commutant assertion, choose `k in K minus A` with finite support.
Only the finitely many pair flips whose pairs meet that support can change
`k` by conjugation; all other generators of `A` commute with it.  Hence the
orbit `O={a k a^(-1):a in A}` is finite.  The nonzero group-algebra element

```text
x_O = sum_(h in O) lambda(h)
```

is fixed by conjugation with every `lambda(a)`, so
`x_O in L(A)' cap L(K)`.  Its Fourier support is disjoint from `A`, hence
`x_O notin L(A)`.  Thus `L(A)` is not maximal abelian.  The calculation is
equivariant under `Lambda` and is unaffected by the crossed product.

