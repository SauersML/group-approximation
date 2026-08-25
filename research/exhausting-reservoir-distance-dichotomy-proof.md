---
rg: 2
id: exhausting-reservoir-distance-dichotomy-proof
kind: route
title: Separate the persistent affine distance and annihilate the dense ideal tail
target: exhausting-ideal-reservoirs-have-lift-or-quotient-separator
requires:
  - point-norm-approximate-ucp-sections-close-to-exact
---

Work in the real Banach space

```text
X=L_sa(E,A)
```

with the operator norm.  The spaces `V_m=L_sa(E,L_m)` are increasing, so the
numbers `delta_m` in `(ERD2)` decrease.

Suppose first that `delta_m->0`.  Choose `d_m in V_m` and
`phi_m in UCP(E,A)` such that

```text
||t+d_m-phi_m|| <= delta_m+1/m.                            (1)
```

Because `d_m(E) subset I`, applying the contractive quotient map gives

```text
||q phi_m-id_E|| <= delta_m+1/m ->0.                       (2)
```

Thus the ucp maps `phi_m:E->A` are point-norm approximate lifts of `id_E`.
By `point-norm-approximate-ucp-sections-close-to-exact`, `id_E` has an exact
ucp lift.

Conversely, let `s:E->A` be an exact ucp lift.  Then `h=s-t` is a
self-adjoint linear map into `I`.  Since `E` is finite-dimensional and
`union_m L_m` is dense in `I`, there are self-adjoint maps `h_m:E->L_m`
with `||h_m-h||->0` (choose a self-adjoint basis of `E` and approximate its
finitely many images; the value at `1` may be fixed as zero).  Hence

```text
delta_m <= ||t+h_m-s||=||h_m-h|| ->0.                      (3)
```

This proves `(ERD4)` and the first alternative.

Now suppose `delta=inf_m delta_m>0`.  The standard distance form of geometric
Hahn--Banach, applied in the quotient Banach space `X/V_m` to the point
`t+V_m` and the convex set which is the image of `C=UCP(E,A)`, gives a real
functional `ell_m in X^*` such that

```text
||ell_m||=1,       ell_m|_(V_m)=0,
ell_m(t)-sup_(phi in C) ell_m(phi) >= delta_m.             (4)
```

(Taking the closure of the image of `C` does not change its distance from the
point, so no closed-image assumption is hidden here.)

Take a weak-star cluster point `ell` of a tail subnet of `(ell_m)` in the
weak-star compact unit ball of `X^*`.  If `v` belongs to `V_k`, then
`ell_m(v)=0` for every `m>=k`, and therefore `ell(v)=0`.  The union of the
`L_m` is dense in `I`, while `E` is finite-dimensional, so `union_m V_m` is
dense in `L_sa(E,I)`.  Continuity now gives

```text
ell|_(L_sa(E,I))=0.                                       (5)
```

For each fixed `phi in C`, `(4)` gives

```text
ell_m(t-phi)>=delta_m>=delta.
```

Passing to the cluster point yields

```text
ell(t-phi)>=delta.                                        (6)
```

Equation `(5)` says that `ell` factors through the quotient map on map
spaces.  Writing the resulting functional as `bar ell`, equation `(6)` is
exactly

```text
bar ell(id_E-q phi)>=delta,
```

which is `(ERD3)`.  An exact lift would make its left side zero, so this also
proves directly that the second alternative excludes liftability.
