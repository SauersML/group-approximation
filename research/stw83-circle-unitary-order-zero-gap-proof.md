---
rg: 2
id: stw83-circle-unitary-order-zero-gap-proof
kind: route
title: Cut the circle at the common zero set of orthogonal order-zero supports
target: stw83-circle-unitary-order-zero-plus-constants-gap
requires:
  - stw83-plateau-buffer-recolouring-hinge
---

## The scalar separation lemma

An order-zero map from a finite-dimensional algebra to an abelian algebra
vanishes on every noncommutative matrix summand.  On the one-dimensional
summands it therefore has the form

```text
eta(b)=sum_(j=1)^m lambda_j h_j,                         (4)
```

where `abs(lambda_j)<=1` and the `h_j` are pairwise orthogonal positive
contractions in `C(T)`.  We prove that the functions in (4), even after an
arbitrary constant is added, cannot converge uniformly to `z`.

Suppose otherwise.  There are constants `c_n`, pairwise orthogonal positive
contractions `h_(n,j)`, and scalars `lambda_(n,j)` in the closed unit disc
such that

```text
epsilon_n
 = norm(z-c_n-sum_j lambda_(n,j) h_(n,j)) -> 0.         (5)
```

The constants `c_n` are bounded by (5), so pass to a subsequence with
`c_n->c`.  Put

```text
V_n={t in T: abs(t-c_n)<=epsilon_n},
W_n=T\V_n.                                               (6)
```

For all sufficiently large `n`, the intersection of the circle with the
closed disc in (6) is either empty or a proper closed arc.  Hence `W_n` is
connected.  Let

```text
U_(n,j)={t:h_(n,j)(t)>0}.
```

The `U_(n,j)` are pairwise disjoint.  Outside their union the order-zero
term in (5) is zero, so (5) shows that `W_n` is contained in their union.
Connectedness therefore puts all of `W_n` in one `U_(n,j(n))`.  On `W_n`
only that one summand can be nonzero, and hence

```text
dist(t-c_n,[0,lambda_(n,j(n))]) <= epsilon_n
for every t in W_n.                                     (7)
```

After another subsequence, `lambda_(n,j(n))->lambda` in the closed unit
disc.  If `c` is not on the circle, every fixed `t in T` eventually belongs
to `W_n`; if `c` is on the circle, the same holds for every `t!=c`.
Letting `n` tend to infinity in (7) gives

```text
t-c in [0,lambda]
```

for every `t` on the circle, with at most the single point `c` omitted.
This is impossible: a punctured circle is not contained in one line segment.
Thus the infimum of the left side of (1), over all the displayed data, is
strictly positive.  Calling that infimum `delta` proves (1).

## The finite-set plateau consequence

Identify the rank-one corner `eDe` with `C(T)`.  If (2) holds, write

```text
e eta^(1)(b_1) e=c e.
```

Compression by `e` does not change `eta^(0)(b_0)` and is contractive.
Therefore

```text
norm(z e-eta^(0)(b_0)-eta^(1)(b_1))
 >= norm(z e-eta^(0)(b_0)-c e)
 >= delta,
```

where the last inequality is (1).  Notice that no commutation between `e`
and the range of `eta^(1)` was used.  Its off-diagonal matrix entries may be
arbitrary.  The obstruction concerns only the coefficient-blind plateau
diagonal, so it survives precisely the off-diagonal escape left open by the
whole-corner block-diagonal no-go.
