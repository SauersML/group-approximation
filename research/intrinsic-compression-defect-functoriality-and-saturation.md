---
rg: 2
id: intrinsic-compression-defect-functoriality-and-saturation
kind: claim
title: The intrinsic compression defect is functorial, multiplicative and saturates simple cores
root: true
artifacts:
  - research/intrinsic-compression-defect-functoriality-and-saturation-proof.md
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/NormalKazhdanMFRadical.lean
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
distinct_from:
  normal-kazhdan-defect-non-mf: that is the analytic inclusion of a normal Kazhdan subgroup in the MF residual; this gives the algebraic functoriality, product formula and simple-core saturation which manufacture the hypothesis in images and quotients.
  defect-saturation-full-mf-radical: that is one torsion-free construction realizing total defect; this is the intrinsic calculus valid for every marked subgroup pair.
---

For `L<=G`, define

```text
Comp_G(L)={u in G : uLu^-1<=L},

D_G(L)=<<[ucu^-1,l] :
          u in Comp_G(L), c in C_G(L), l in L>>_G.       (ICD1)
```

Then:

1. **Functoriality.**  Every homomorphism `f:G->Q` satisfies

   ```text
   f(D_G(L)) <= D_(f(G))(f(L)).                           (ICD2)
   ```

2. **Products.**  For `L_i<=G_i`,

   ```text
   D_(G_1 x G_2)(L_1 x L_2)
     =D_(G_1)(L_1) x D_(G_2)(L_2).                       (ICD3)
   ```

3. **Finite-dimensional invisibility.**  Every finite-dimensional linear
   representation of `G`, over every field, kills `D_G(L)`.

4. **Simple-core saturation.**  If `S<=G` is nontrivial and simple and

   ```text
   S intersect D_G(L) != 1,
   ```

   then `S<=D_G(L)`.  If `S` normally generates `G`, then `D_G(L)=G`.

5. **Image saturation.**  Let `f:G->Q` be onto.  If a simple subgroup
   `S<=D_G(L)` survives under `f` and `f(S)` normally generates `Q`, then

   ```text
   D_Q(f(L))=Q.                                           (ICD4)
   ```

6. **MF consequence.**  If `f(L)` and `Q` have property `(T)`, the
   hypotheses of item 5 imply

   ```text
   Rad_MF(Q)=Q.                                           (ICD5)
   ```

Thus the construction of a full MF radical separates into two exact tasks:
place one nonzero piece of a simple subgroup in the intrinsic defect, then
make its surviving image normally generate the target.  The analytic input
is applied only after these algebraic operations have filled the target.
