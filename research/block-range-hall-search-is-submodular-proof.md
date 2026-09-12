---
rg: 2
id: block-range-hall-search-is-submodular-proof
kind: route
title: Each target contribution is a linear-matroid rank function
target: block-range-hall-search-is-submodular
requires: []
---

Fix one target block `j` and write

```text
r_j(A)=dim(sum_(i in A) R_(j,i)).
```

For source-block sets `A,B`, let

```text
U=sum_(i in A) R_(j,i),
V=sum_(i in B) R_(j,i).
```

Then

```text
r_j(A)+r_j(B)
 = dim(U)+dim(V)
 = dim(U+V)+dim(U intersect V).
```

Now `U+V` is exactly the span attached to `A union B`, while the span attached
to `A intersect B` is contained in `U intersect V`.  Hence

```text
r_j(A)+r_j(B) >= r_j(A union B)+r_j(A intersect B).
```

So every `r_j` is submodular.  Their sum is submodular, and

```text
A |-> sum_(i in A) dim(H_i)
```

is modular, so subtracting it preserves submodularity.  Therefore `f` in
`(BRH3)` is submodular.

Finally, if `min_A f(A)=-r<0`, then the minimizing `A` satisfies

```text
sum_(i in A) dim(H_i)-sum_j dim(R_j(A))=r,
```

and `block-range-hall-implies-shrunk-subspace` turns that subset into an
`r`-shrunk subspace.
