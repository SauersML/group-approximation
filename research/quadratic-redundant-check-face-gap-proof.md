---
rg: 2
id: quadratic-redundant-check-face-gap-proof
kind: route
title: Commute through pairwise row sums and count face-pinching incidence
target: quadratic-redundant-check-overlay-gives-uniform-face-gap
requires:
  - complete-overlay-code-group-has-uniform-conjugation-gap
---

Write `Q_i` for the coordinate reflections in an exact augmented-face
representation.  Given any coordinates `i,j`, choose original rows `a,b`
with `i in supp(h_a)` and `j in supp(h_b)`.  If `i` also lies in `h_b`, then
`Q_i,Q_j` share face `b`; if `j` lies in `h_a`, they share face `a`.
Otherwise both lie in the symmetric-difference face `h_a+h_b`.  In every
case they commute.  The original parity relations then identify the group
with the finite abelian group dual to `C`; the added equations are redundant
in this abelian group.

The same observation proves support connectivity.  If a codeword support
had two components, choose original checks meeting the two components.
Their support intersections are disjoint, while the symmetric-difference
face contains both, joining the components.

It remains to compare the face and coordinate energies.  Put

```text
P_i=(I+Ad(Q_i))/2,
e_i(X)=||(I-P_i)X||_2^2,
e_f(X)=||(I-Phi_f)X||_2^2.                               (QRP1)
```

Because the coordinates in `f` commute, `Phi_f` is the product of their
commuting projections `P_i`.  Hence

```text
sum_(i in f) e_i(X) <= |f| e_f(X) <= 2q e_f(X).          (QRP2)
```

If coordinate `i` occurs in `w_i` original rows, it occurs in exactly
`w_i(M-w_i)` pair-sum faces: membership flips precisely when one chosen row
contains `i` and the other does not.  Since `1<=w_i<=D`, this is at least
`M-D`.  Summing `(QRP2)` over faces gives

```text
sum_f e_f(X)
 >= (M-D)/(2q) sum_i e_i(X).                             (QRP3)
```

There are at most `M(M-1)/2+M` augmented faces.  Since `M=Theta(L)`, division
by `|F|` turns `(QRP3)` into

```text
<X,H_F X> >= c(q,D,M/L) (1/L)sum_i e_i(X).               (QRP4)
```

Finally, the established code-distance conjugation gap says

```text
(1/L)sum_i ||Ad(Q_i)X-X||_2^2
 >= 4 delta ||X-E_(N')(X)||_2^2.                         (QRP5)
```

Since `||Ad(Q_i)X-X||_2^2=4e_i(X)`, equations `(QRP4)`--
`(QRP5)` prove `(QRF3)`.  The occurrence count follows from
`w_i(M-w_i)=O(L)` and the already available `Theta(L)` copies of every
coordinate.
