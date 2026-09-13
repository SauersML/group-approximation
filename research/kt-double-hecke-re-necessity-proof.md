---
rg: 2
id: kt-double-hecke-re-necessity-proof
kind: route
title: Compose the Hecke containment with the slice inclusion, for doubles and for coset wreaths
target: kt-double-hyperlinearity-requires-function-field-hecke-re
requires:
  - opposite-slice-contains-function-field-hecke-pair
  - opposite-transvections-are-first-nonore-relative-gate
  - kt-wreath-hyperlinear-iff-double-hyperlinear
  - binary-free-and-ordinary-coset-wreaths-share-hyperlinearity
  - bowen-chapman-witness-is-kt-double-at-q2-r3-d3
---

## (KH1) for doubles

We need one normal-form fact.  Let `C<=A` and `A'<=A`, and put
`C'=A' intersect C`.  Then `A' *_(C') A' -> A *_C A` is injective.  A reduced
alternating word with letters in `A'\C'` has letters in `A\C`, so by the
normal form theorem (Serre, *Trees*, I.1.2) its image is nontrivial.  The
elements of length zero form `C'`, which maps injectively into `C`.

The slice `P` contains `Gamma`, so `P intersect Gamma=Gamma` and
`D_P -> D_G` is injective.  The map `D_(Lambda_1) -> D_P` is (HP3) of
`opposite-slice-contains-function-field-hecke-pair`.  The composite is the
natural map `D_(Lambda_1) -> D_G`.

## (KH1) for coset wreaths

Let `H<=G` and `X=G/Gamma`.  The orbit `Y=H o` of `o=Gamma` is `H`-invariant
and `H`-isomorphic to `H/(H intersect Gamma)`.  Extending lamp functions by
zero outside `Y` gives a homomorphism

```text
(direct_sum_Y Z/2) rtimes H -> (direct_sum_X Z/2) rtimes G,
```

and it is injective because `Y` is `H`-invariant.  For `H=P` we get
`W_P -> W_G`.  For `H=Lambda_1`, (HP1) gives `Y ~= Lambda_1/Gamma_1`, and
`Lambda_1 o` lies inside `P o`, so the map factors through `W_P`.

## Item 2

The equivalence of the three forms of the first bullet is
`kt-wreath-hyperlinear-iff-double-hyperlinear`.  Hyperlinearity passes to
subgroups.  So by (KH1),

```text
D_G hyperlinear => D_P hyperlinear => D_(Lambda_1) hyperlinear.
```

Items 4 and 6 of `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity`,
applied to `Gamma<=P` and to `Gamma_1<=Lambda_1`, turn the second and third
statements into `RE/C`.  As in the slice proof, `F_q[t]` and `F_q[t,1/t]` are
Euclidean, so `Lambda_1=SL_r(F_q[t,1/t])` and `Gamma_1=SL_r(F_q[t])` with
`t=x_1`.

## Item 3

A Kun--Thom route to a hyperlinear nonsofic group proves `D_G` or `W_G`
hyperlinear, and item 2 applies.  Step 3 of
`hyperlinear-nonsofic-from-kt-ce-stabilizer` concludes exactly that `D_G` is
hyperlinear.  `bowen-chapman-witness-is-kt-double-at-q2-r3-d3` identifies the
Lean witness with `D_G` at `(q,r,d)=(2,3,3)`, and there the Hecke pair is
`SL_3(F_2[t]) < SL_3(F_2[t,1/t])`.

The three properties of the Hecke pair come from items 5 and 6 of the slice
claim and its proof: a Kazhdan base, co-density (TR1), and incompressibility.

## Item 4

This is the contrapositive of item 2, together with (KH1).  If the Hecke
inclusion is not `RE/C`, then `D_(Lambda_1)` is non-hyperlinear by the same
general equivalence.  A group containing a non-hyperlinear subgroup is
non-hyperlinear, so `D_P` and `D_G` are non-hyperlinear.  The subgroup
`Lambda_1=EL_r(F_q[x_1^(+-1)])` lies in `G` for every `d>=1`.
