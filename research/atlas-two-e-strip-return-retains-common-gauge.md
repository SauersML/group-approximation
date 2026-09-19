---
rg: 2
id: atlas-two-e-strip-return-retains-common-gauge
kind: claim
title: The shortest two-E chart return retains the common Atlas seam gauge
invalidates:
  - atlas-two-e-strip-authenticates-ee-mode
artifacts:
  - experiments/atlas_first_nonscalar_mixed_row_audit.py
distinct_from:
  atlas-reverse-dictionary-does-not-close-ee-return: that proves the literal reverse rows do not contain x12(ee); this adjoins the shortest derived Steinberg word that does contain it and lands on the reverse-chart root.
  atlas-first-common-rhs-return-star-has-rank-two: that leaves the common RHS as a bare nuisance; this returns it to x12(1) through two coefficient-E actors but keeps the resulting nested monomial as a mandatory nuisance.
  atlas-steinberg-spare-index-independence: that proves all derived monomial roots and splits agree in the presented group; this computes the nuisance-quotient rank of one such derived return on the mixed-row face.
---

**ESTABLISHED SCOPED QUOTIENT-RANK FENCE.** Let

```text
R=x_12(ee).
```

The shortest legal St3/orthogonality return using single-letter actors which
both contains `R` and lands on its original root subgroup is

```text
[x_13(E),[x_31(E),R]]=x_12(1)=p1_23.                 (TER1)
```

Indeed the inner commutator prepends one `E` and changes endpoint `1` to
`3`, while the outer one prepends the second `E` and returns that endpoint:

```text
E(ee)=e,                 E(e)=1.                      (TER2)
```

One nonzero St3 interaction changes one endpoint, so no one-interaction word
in this single-letter St3/orthogonality class can return to `(1,2)`.

The consequence has fixed support in the literal packet. Using the `j=4`
factorization of `R`, it follows by Steinberg commutator collection from the
zero-based full-family rows

```text
3335  st3_142_ee,        2182  orth_31_42_Ee,
3789  st3_314_Ee,        3924  st3_342_1e,
3270  st3_132_Ee,                                      (TER3)
```

together with the reverse row `p1_23=x_12(1)`. The respective syllable and
Atlas-X lengths are

```text
(85,295), (49,167), (53,157), (49,179), (53,157).
```

The resulting nested seam word has 121 syllables and Atlas `X`-length 366.
The MSI audit constructs it and verifies `(TER1)` exactly by binary Leavitt
arithmetic. Its derivability for the two-letter root is also the split and
spare-index calculus of `atlas-steinberg-spare-index-independence`.

However `(TER1)` does **not** add the missing scalar quotient direction.
Write the nested reduced monomial as

```text
N=[x_13(E),[x_31(E),R]].                              (TER4)
```

After the chart occurrence `p1_23` is authenticated, the four projected
rows are the three star equations `P_j-R=0` and `N-p1_23=0`. With desired
columns `(P_3,P_4,P_5)` and mandatory nuisance columns `(R,N)`, their
homogeneous coefficient matrices have

```text
C = [ I_3 ; 0 ],
D = [ -1_3  0 ; 0  1 ],
rank[C D]=4,          rank(D)=2.                      (TER5)
```

Thus the quotient-rank increment remains `4-2=2`, not three.

The surviving gauge is exact already in the projected block calculus. For
any nonidentity invertible matrix `U`, put

```text
P_3=P_4=P_5=R=U,
x_31(E)|_mult=U^(-1),       x_13(E)|_mult=I.           (TER6)
```

Factor every star path as `U*I`. Then the inner coefficient product in
`(TER1)` is `U^(-1)U=I`, the outer product is `I`, and the authenticated
chart output is `I`; every projected row is exact while `U` is arbitrary.
Choosing `U` in `GL_d(F_2)` realizes these products by elementary block
transvections in a finite matrix group. This is a countermodel to the
claimed scalar nuisance-rank certificate, not a model of all 4,648 packet
words.

Therefore the first genuine reverse/chart consequence reaches the correct
chart occurrence but leaves a two-actor seam gauge. A successful next
family must identify the nested monomial with `R` on the authenticated
reservoir, or provide an independent reverse return which eliminates the
two stripping actors; endpoint return alone is insufficient.

DERIVATION
atlas-two-e-strip-return-gauge-proof
