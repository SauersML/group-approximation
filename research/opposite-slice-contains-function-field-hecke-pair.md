---
rg: 2
id: opposite-slice-contains-function-field-hecke-pair
kind: claim
title: The opposite-transvection Kun--Thom slice contains the function-field Hecke pair SL_r(F_q[t]) < SL_r(F_q[t,1/t])
distinct_from:
  opposite-transvections-are-first-nonore-relative-gate: that isolates the opposite slice and proves finite-image collapse; this finds a one-place S-arithmetic Hecke sub-pair inside it whose double embeds in the slice double, so every positive answer for the slice is a positive answer for that pair
  farey-tree-lift-hits-opposite-steinberg-cycle: that is a no-go for one construction of the slice action; this is a containment theorem which transfers soficity, hyperlinearity and RE/C from the slice down to a commensurated Hecke pair
  sl3-dyadic-building-vertex-action-is-sofic: that is the number-field building action of SL3(Z[1/2]); this shows the function-field building action of SL_r(F_q[t,1/t]) is a sub-action of the Kun--Thom opposite slice
  kun-thom-single-compressor-sofic-joint-nonsofic: that shows one compressor is positive and the full action is nonsofic; this names the algebraic feature that first appears between them, a Laurent unit in the kernel ring
---

Keep the notation of `opposite-transvections-are-first-nonore-relative-gate`:
`k=F_q`, `r,d>=3`, `Gamma=EL_r(k[x_1,...,x_d])`,
`A=I+E_12`, `B=I+E_21`, `P=<Gamma,(1,A),(1,B)>=E_pm rtimes SL_2(Z)`, where
`E_pm=EL_r(k[x_1^(+-1),x_2^(+-1),x_3,...,x_d])`.  Put

```text
Lambda_1=EL_r(k[x_1^(+-1)]),        Gamma_1=EL_r(k[x_1]).
```

Then the following hold.

1. `Lambda_1 <= E_pm <= P` and

   ```text
   Lambda_1 intersect Gamma = Gamma_1.                          (HP1)
   ```

2. The `Lambda_1`-orbit of the base site `o=Gamma` in `P/Gamma` is
   `Lambda_1`-isomorphic to `Lambda_1/Gamma_1`.  With `t=x_1`, this is the
   action of `SL_r(k[t,1/t])` on the type-zero vertices of the Bruhat--Tits
   building of `SL_r(k((t)))`.                                  (HP2)

3. The natural homomorphism

   ```text
   D_1=Lambda_1 *_(Gamma_1) Lambda_1  ->  D=P *_Gamma P         (HP3)
   ```

   is injective.

4. Consequently:
   - if `P action P/Gamma` is sofic, then `Lambda_1 action Lambda_1/Gamma_1`
     is sofic;
   - if `D` is sofic, respectively hyperlinear, then so is `D_1`;
   - if `L(Gamma) subset L(P)` is `RE/C`, then
     `L(Gamma_1) subset L(Lambda_1)` is `RE/C`.  Contrapositively, a proof
     that the function-field Hecke inclusion is not `RE/C` makes `D`
     non-hyperlinear.

5. Both `Gamma_1<Lambda_1` and `Gamma<E_pm` are co-dense in every finite
   quotient of the larger group:

   ```text
   q(Gamma_1)=q(Lambda_1),        q'(Gamma)=q'(E_pm)            (HP4)
   ```

   for every homomorphism `q` of `Lambda_1`, and `q'` of `E_pm`, to a finite
   group.  Both smaller groups are Kazhdan.  Hence
   `codense-kazhdan-coset-action-forces-permutation-outliers` applies to
   both coset actions: every orbit atlas has a uniform positive gap against
   exact finite actions of `Lambda_1` (respectively `E_pm`).  Any sofic model
   of the opposite slice restricts to noncorrectable models of these
   Kazhdan pairs.

6. **Units dichotomy.**  Let `S` be a left Ore monoid of positive monomial
   compressors, and `N_S=union_(s in S) s^(-1) Gamma s` its telescope kernel.
   Then `N_S=EL_r(k[M_S])`, where `M_S` is a directed union of pointed
   simplicial cones.  So `M_S intersect (-M_S)={0}`, the ring `k[M_S]` has
   unit group `k^x`, and `N_S` contains no elementary matrix `e_ij(x^(-v))`
   with `0!=v in M_S`.  The opposite slice has kernel ring with unit group
   `k^x x x^(Z^2)`.  Each primitive `v in N^2 x {0}` gives a copy
   `EL_r(k[x^(+-v)]) > EL_r(k[x^v])` of the same Hecke pair, with (HP1)--(HP4).

**What this changes.**  In the standard compressor atlas, the non-Ore gate is
the first slice whose kernel ring has a nontrivial unit.  That unit carries the
one-place function-field Hecke pair.  The pair is commensurated and co-dense,
with a Kazhdan vertex group, and its vertex stabilizers are incompressible (a
maximal compact open subgroup contains no proper conjugate of itself).  So no
Kun--Thom compression step acts inside it.  Every positive answer for the gate,
whether a sofic coset action, a sofic or hyperlinear double, or `RE/C`, is
therefore also a positive answer for `SL_r(F_q[t]) < SL_r(F_q[t,1/t])`.  That
pair is the positive-characteristic analogue of the open dyadic problems
`sl3-dyadic-building-vertex-action-is-sofic` and
`arithmetic-pair-is-not-relatively-embeddable`.  Free-monoid telescopes and
Følner counting along `<A,B>_+` cannot settle the gate unless they also settle
this building action.

The containment is one-directional.  It does not say that a positive answer
for the Hecke pair gives one for the slice, and it does not decide either
pair.

DERIVATION
opposite-slice-function-field-hecke-pair-proof
