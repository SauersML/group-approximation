---
rg: 2
id: packed-d-coset-flip-has-full-bs-hull
kind: claim
title: A vanishing-energy packed dihedral flip can have full BS hull
distinct_from:
  displacement-carrier-has-p-fold-bs-hull: that flips one dihedral-fixed line and forces a p-dimensional hull; this packs one coordinate D-coset from every B-D double coset and forces the entire regular block.
  weighted-coset-hulls-are-energy-sublinear: that proves an energy-two-thirds hull bound for external orthogonal sums of canonical rank-one cells; this gives one-block packed projections for which the hull density is one while the energy tends to zero.
  congruence-cross-type-mixing-has-uniform-polar-repair: that repairs mixing after exact endpoint types have been authenticated; this is a raw same-block displacement projection and shows that its invariant hull cannot be charged before endpoint selection.
---

**ESTABLISHED.**  Let `p` be an odd prime and use the standard left-regular
Iwahori endpoint on

```text
G_p=PSL_2(F_p),       H_p=l2(G_p),
Y_p=lambda_p(x),      B_p=<r,s>,       D_p=<r,x>.       (PDF1)
```

Write `m_p=ord_p(4)`.  Thus `|B_p|=p m_p` and `|D_p|=2m_p` (with the same
ratio in the harmless small degeneracies).  Choose one representative
`g_j` of every double coset in `B_p\G_p/D_p`, put

```text
E_p=disjointUnion_j D_p g_j,
Q_p=M_(1_(E_p)),       C_p=1-2Q_p,       X_p=C_pY_p.    (PDF2)
```

Then `Q_p` commutes with `lambda_p(D_p)`, so the BS core, involution, and
inversion rows of `(X_p,lambda_p(r),lambda_p(s))` are exact.  Moreover

```text
X_p-Y_p=-2Q_pY_p,       |X_p-Y_p|=2Q_p.                (PDF3)
```

Thus `Q_p` is literally the nonzero displacement spectral projection.  If
`k_p=rank(Q_p)=|E_p|`, the sum of the two squared Frobenius cubic defects is
at most `24k_p`, while

```text
k_p/|G_p| <= |D_p|/|B_p| = 2/p.                        (PDF4)
```

Consequently the normalized two-cubic energy is at most `48/p`, and tends
to zero.

Nevertheless the smallest reducing carrier for the exact BS subgroup
`B_p=<r,s>` which contains `Q_pH_p` is all of `H_p`.  Indeed coordinate
vectors in `Q_pH_p` are indexed by `E_p`, and their `B_p`-orbit spans

```text
l2(B_p E_p)=l2(G_p),                                  (PDF5)
```

because the sets `B_pD_pg_j` exhaust the chosen double-coset partition of
`G_p`.  Hence

```text
rank(Hull_(B_p)(Q_p))/|G_p|=1                          (PDF6)
```

along a sequence whose normalized relator energy goes to zero.

It follows that no dimension-uniform estimate

```text
rank(Hull_B(Q))/d <= C E(Q)^alpha                      (PDF7)
```

can hold for any `C<infinity` and `alpha>0`, even when `Q` is the exact
high-displacement projection, the BS core/involution/inversion rows are
literal, and the ambient endpoint is a single authenticated regular
congruence block.  This failure does not require cancellation between the
two cubic rows.  In particular property-`(tau)`, parity-cocycle rounding,
or the post-authentication polar repair cannot justify invariantizing the
raw high-displacement support: the legal hull can already be the whole
block.

## Proof of the defect and rank estimates

The set `E_p` is left `D_p`-invariant.  Therefore `Q_p`, and hence `C_p`,
commutes with both `lambda_p(r)` and `Y_p`.  Since `C_p` and `Y_p` are
commuting involutions, `X_p` is an involution; the same commutation gives

```text
X_p lambda_p(r) X_p
 =C_pY_p lambda_p(r) C_pY_p
 =Y_p lambda_p(r)Y_p=lambda_p(r)^(-1).
```

For either exact cubic vertex `A` of the original endpoint, put
`A_0=A`, `A_1=Ad(A)(C_p)`, and `A_2=Ad(A^2)(C_p)`.  Since `A^3=1`,

```text
(C_pA)^3=C_p Ad(A)(C_p) Ad(A^2)(C_p).                 (PDF8)
```

Each factor on the right differs from the identity on a rank-`k_p`
projection.  The difference of their product from the identity has range
contained in the sum of those three ranges, hence rank at most `3k_p`.
It is the difference of two unitaries and has operator norm at most `2`,
so its squared Frobenius norm is at most `12k_p`.  Summing the two cubics
gives `24k_p`.

Finally, if `nu_p=|B_p\G_p/D_p|`, then the selected right `D_p`-cosets are
disjoint and

```text
k_p=nu_p|D_p|
   <=[G_p:B_p]|D_p|
   =|G_p| |D_p|/|B_p|=2|G_p|/p.                       (PDF9)
```

The orbit calculation `(PDF5)` proves the full-hull assertion.

DERIVATION
packed-d-coset-full-hull-proof
