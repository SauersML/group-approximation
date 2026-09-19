---
rg: 2
id: stw10-matrix-corner-coordinate-proof
kind: route
title: Expand through matrix units and read the model from the e11 corner
target: stw10-matrix-core-models-are-corner-amplifications
requires:
  - stw10-qd-traces-admit-exact-finite-dimensional-core-models
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Put `p=e_11` and `B=pAp`.  For `a,b in A`, insertion of
`1=sum_ell e_(ell ell)` gives

```text
e_1i ab e_j1
 = sum_ell (e_1i a e_ell1)(e_1ell b e_j1).
```

This proves multiplicativity of the map `Phi` in `(MC1)`; the star relation
is immediate.  Conversely, matrix-unit multiplication shows

```text
e_1r (sum_(i,j) e_i1 b_ij e_1j) e_s1=b_rs,
sum_(i,j) e_i1(e_1i a e_j1)e_1j=a.
```

So the displayed inverse is exact.  Also
`Phi(e_rs)=E_rs tensor p`, verifying the orientation and the image of `D`.

Now let `D subset MD(psi)`.  A unital representation of `M_d` on
`C^k` is a multiple of its defining representation, so `k=dm` and a target
unitary makes

```text
psi(e_ij)=E_ij tensor 1_m.
```

For `b in B`, the multiplicative-domain identities imply

```text
psi(b)=(E_11 tensor 1_m) psi(b) (E_11 tensor 1_m)
      =E_11 tensor chi(b)
```

for a unique map `chi:B -> M_m`.  Corner compression shows that `chi` is
completely positive, and `chi(p)=1_m`, so it is u.c.p. relative to the unit
`p` of `B`.  For every `b in B`, bimodularity gives

```text
psi(e_i1 b e_1j)=E_ij tensor chi(b).
```

Summing this identity proves `(MC2)`.  It also proves uniqueness.  Conversely
`id_(M_d) tensor chi` is u.c.p. and is manifestly multiplicative on
`M_d tensor 1_B`, proving the algebraic equivalence.

For `Phi(x)=[b_ij]` and `Phi(y)=[c_ij]`, subtract the two matrix products in
`M_d(M_m)`.  The resulting `(i,j)` entry is exactly `(MC3)`.  If each
summand has norm at most `eta`, each entry has norm at most `d eta`.  The
operator norm of a `d` by `d` operator matrix is bounded by `d` times its
largest entry norm (apply the scalar row/column-sum bound to the matrix of
entry norms), giving `d^2 eta` with no hidden dimension factor.

It remains to check traces.  Traciality gives `tau(e_ii)=1/d`; hence
`tau_B=d tau|B` is normalized.  Off-diagonal terms have trace zero, while

```text
tau(e_i1 b e_1i)=tau(b e_1i e_i1)=tau(b)       (b in B).
```

Therefore

```text
tau(Phi^(-1)([b_ij]))=sum_i tau(b_ii)
 = (1/d)sum_i tau_B(b_ii),
```

which is `tau=tr_d tensor tau_B`.  Applying the same normalized tensor-trace
formula to `(MC2)` proves `(MC4)`.  Finally, direct matrix-unit multiplication
shows that `iota` is a unital star homomorphism and
`Phi(iota(b))=1_d tensor b`.  Consequently both the multiplicative defect
norm and normalized trace discrepancy on `iota(b),iota(c)` equal exactly the
corresponding quantities for `chi` on `b,c`.

For a CAR stage in `R`, the prior core-exactification theorem permits us to
impose `D_n subset MD(psi)` before applying this classification.  Formulae
`(MC3)` and `(MC4)` then give the stated finite-packet corner criterion in
both directions.

**Trust boundary.**  Full matrix units summing to `1_A` are essential.  For
a nonunital or nonfull matrix corner the map in `(MC1)` need not identify all
of `A` with a matrix algebra.  No near inclusion is promoted to a
homomorphism: exact membership `D subset MD(psi)` is used.  The target trace
is normalized, so `tau_B=d tau|B`; omitting this factor would make `(MC4)`
false.
