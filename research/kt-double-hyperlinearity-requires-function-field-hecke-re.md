---
rg: 2
id: kt-double-hyperlinearity-requires-function-field-hecke-re
kind: claim
title: Hyperlinearity of the Kun--Thom double or wreath requires RE/C of the function-field Hecke pair SL_r(F_q[t]) < SL_r(F_q[t,1/t])
distinct_from:
  opposite-slice-contains-function-field-hecke-pair: that is the containment inside the opposite slice; this composes it with the inclusion of the slice in the full vertex group and states what it forces on the Q3.4 witnesses and on non-hyperlinear-group
  kt-wreath-hyperlinear-iff-double-hyperlinear: that is the wreath, double and RE/C equivalence for the Theorem E pair itself; this is a necessary condition for that common status, read on a smaller S-arithmetic pair
  bowen-chapman-witness-is-kt-double-at-q2-r3-d3: that identifies the Lean witness with the double at (2,3,3) and names its hyperlinearity bit; this shows that bit implies RE/C of SL_3(F_2[t]) < SL_3(F_2[t,1/t])
  kt-hyperlinear-coset-wreath-forces-nonroundable-vertex: that extracts a vertex-rounding failure from hyperlinearity; this extracts relative embeddability of a commensurated Hecke sub-pair
---

Let `Gamma=EL_r(F_q[x_1,...,x_d]) < G=EL_r(F_q[x_1^(+-1),...,x_d^(+-1)]) rtimes SL_d(Z)`
be the Kun--Thom Theorem E pair (`r,d>=3`).  Let `P` be the opposite-transvection
slice, and `Lambda_1=EL_r(F_q[x_1^(+-1)]) > Gamma_1=EL_r(F_q[x_1])` the Hecke
sub-pair of `opposite-slice-contains-function-field-hecke-pair`.  For `H<=G`
containing the relevant base group `C` (`Gamma` or `Gamma_1`), write
`D_H=H *_C H`, and `W_H=(direct_sum_(H/C) Z/2) rtimes H` for its binary coset
wreath.

1. The natural maps

   ```text
   D_(Lambda_1) -> D_P -> D_G,        W_(Lambda_1) -> W_P -> W_G      (KH1)
   ```

   are injective homomorphisms.

2. Each statement below implies the next:
   - `L(Gamma) subset L(G)` is `RE/C`; equivalently `D_G` is hyperlinear,
     equivalently `W_G` is hyperlinear;
   - `L(Gamma) subset L(P)` is `RE/C` (the opposite-transvection gate);
   - `L(Gamma_1) subset L(Lambda_1)` is `RE/C`; equivalently
     `SL_r(F_q[t,1/t]) *_(SL_r(F_q[t])) SL_r(F_q[t,1/t])` is hyperlinear.

3. **Q3.4 witnesses.**  Every Kun--Thom route to a hyperlinear nonsofic group
   takes `D_G` or `W_G` as the witness and needs its hyperlinearity.  This
   includes `hyperlinear-nonsofic-from-kt-ce-stabilizer` and the Bowen--Chapman
   Lean witness `D_G` at `(q,r,d)=(2,3,3)`.  Each such route therefore also
   proves `RE/C` for `SL_r(F_q[t]) < SL_r(F_q[t,1/t])`, which is
   `SL_3(F_2[t]) < SL_3(F_2[t,1/t])` for the Lean witness.  Kun--Thom
   Theorem A gives the nonsofic half, and it has no analogue here.  The Hecke
   pair has a Kazhdan vertex group and a co-dense, incompressible base.

4. **Non-hyperlinear side.**  If `L(SL_r(F_q[t])) subset L(SL_r(F_q[t,1/t]))`
   is not `RE/C` for some `q` and `r>=3`, then the Hecke double is
   non-hyperlinear.  By (KH1), so are `D_P` and `D_G` for that `(q,r)` and
   every `d>=3`.  This settles `non-hyperlinear-group`, and it rules out every
   Kun--Thom-double witness for Q3.4 at those parameters.

**Coupling of two program expectations.**  The arithmetic lanes conjecture
that the dyadic pairs `SL_n(Z) < SL_n(Z[1/2])` are not `RE/C`
(`arithmetic-pair-is-not-relatively-embeddable`).  The Kun--Thom Q3.4 lanes
need the Kun--Thom double to be hyperlinear, and by item 2 that makes the
function-field analogue `RE/C`.  The pairs are analogues, not the same pair, so
the two expectations do not contradict each other.  They do disagree on
analogous commensurated Kazhdan Hecke pairs.  A proof technique for either
expectation that does not see the characteristic, or the difference between
`Z[1/2]` and `F_q[t,1/t]`, decides both in the same direction and kills one
program.

DERIVATION
kt-double-hecke-re-necessity-proof
