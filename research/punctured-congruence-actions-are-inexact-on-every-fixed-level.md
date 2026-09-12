---
rg: 2
id: punctured-congruence-actions-are-inexact-on-every-fixed-level
kind: claim
title: Punctured SL3 congruence actions stay inexact on every fixed congruence subgroup
distinct_from:
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that imports strict normalized-HS instability for every infinite hyperlinear Kazhdan group; this gives one explicit compatible arithmetic construction and records its flexible one-point correction.
  finite-index-correction-is-equivalent-for-kazhdan-groups: that concerns flexible distance to exact representations; these punctured models are literally inexact on every fixed level but flexibly exact after restoring one point.
  sl3z-regular-microstates-are-congruence-correctable: that asks whether every regular microstate is flexibly correctable; this example is already flexibly corrected and therefore is not an enemy to that claim.
---

Let `G=SL_3(Z)` and enumerate any nested principal congruence family

```text
G >= N_1 >= N_2 >= ... .                                  (PCA1)
```

There is one regular-character permutation almost-representation sequence
`phi_j` of `G` such that, for every fixed `a`, the restriction
`phi_j|_(N_a)` is not a homomorphism for all sufficiently large `j`.
Nevertheless `phi_j` is flexibly `o(1)`-close to an exact congruence
representation: one restores a single deleted point.

Choose primes `q_j->infinity` avoiding the levels of `N_1,...,N_j` and
separating the first `j` nonidentity elements of `G`.  Put

```text
Q_j=SL_3(F_(q_j)),       X_j=Q_j\{1}.                    (PCA2)
```

For `y in Q_j`, define a permutation `f_y` of `X_j` by puncturing left
translation and repairing its unique broken arrow:

```text
f_y(x)= yx        if x != y^(-1),
f_y(y^(-1))=y.                                             (PCA3)
```

(`f_1=1`.)  Define `phi_j(g)=f_(g mod q_j)`.  Each `f_y` differs from left
translation by one arrow.  Hence for every fixed `g,h in G`,

```text
d_Ham(phi_j(g)phi_j(h),phi_j(gh)) <= 3/(|Q_j|-1),        (PCA4)
```

and the normalized-HS multiplicative defect is `O(|Q_j|^(-1/2))`.  If
`g !=1`, its reduction is nonidentity eventually; nontrivial left
translation has no fixed point, while puncturing changes only one arrow.
Thus

```text
tr(phi_j(g))->0.                                         (PCA5)
```

The inexactness is visible inside every fixed `N_a`.  Write its level as
`M_a`.  For `j>=a`, reduction modulo `q_j` is surjective on `N_a` by CRT and
elementary generation.  More concretely the commuting elements

```text
u_a=e_12(M_a),       v_a=e_13(M_a)                       (PCA6)
```

belong to `N_a` and have distinct nontrivial reductions, with neither the
inverse of the other.  For any distinct commuting nonidentity `u,v in Q`,
the punctured translations do not commute: at `u^(-1)`,

```text
f_u f_v(u^(-1))=v,       f_v f_u(u^(-1))=vu != v.        (PCA7)
```

Therefore `phi_j(u_a)` and `phi_j(v_a)` violate their exact commutator
relation, proving the asserted simultaneous inexactness.

Finally, adjoining the missing point `1` replaces every `f_y` by the exact
left regular permutation `L_y` on `Q_j`.  The dimension ratio is
`|Q_j|/(|Q_j|-1)->1`, and only one arrow per matrix changes.  Thus this is a
compatible inexact-on-every-fixed-level sequence but not a flexible outlier.
It proves that CSP and canonical trace can never force literal exactness on
some fixed congruence subgroup; the only meaningful remaining question is
the flexible correction problem isolated by
`finite-index-correction-is-equivalent-for-kazhdan-groups`.
