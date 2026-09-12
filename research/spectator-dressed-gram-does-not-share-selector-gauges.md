---
rg: 2
id: spectator-dressed-gram-does-not-share-selector-gauges
kind: claim
title: A dual-Heisenberg-blind dressed Gram does not share the raw selector gauges
artifacts:
  - research/spectator-dressed-selector-gram-fence-proof.md
  - experiments/spectator_dressed_selector_gram_fence.py
distinct_from:
  root-valued-overlap-does-not-undress-external-selector: that uses a scalar external root transporter and proves that even maximal overlap cannot identify a dressed occurrence with an undressed word; this preserves both exact affine rank rows and makes a full dual-Heisenberg label menu blind to two different reservoir dressings.
  packet-dressed-shared-implementer-requires-one-outer-class: that proves packet dressing shares one implementer only within one outer-automorphism class; this treats commuting multiplicity spectators, for which every label outer action is unchanged but the raw gauges still have incompatible ranks.
  two-shared-gauge-selector-rows-have-an-affine-rank-obstruction: that gives the contradiction once the two raw gauges are conjugate; this proves that maximal cross Gram for spectator-dressed words does not establish that hypothesis.
---

**ESTABLISHED DRESSING-TYPE FENCE.**  There are two different operations
which must not be conflated.  If an affine selector row is

```text
W R W^*=T                                                   (SDG1)
```

and an involution `H` commutes with the source reflection `R`, then the
right-dressed **conjugator** satisfies

```text
(WH)R(WH)^*=T.                                              (SDG2)
```

Likewise left dressing by an involution commuting with `T` preserves the
row.  But `(SDG2)` leaves the target `T` unchanged, so it does not change
the multiplicity gauge occurring in the affine target reflection.

By contrast, if `H` commutes with a target reflection

```text
T=C_q tensor V,
```

then the dressed **target word**

```text
HT=C_q tensor (HV)                                         (SDG3)
```

has a changed reservoir factor.  Even when `H,V` are commuting
involutions, `(SDG3)` is not the target in `(SDG1)`.  Its negative rank is
`Phi_q(theta(HV))`, not `Phi_q(theta(V))`; preserving the packet covariance
does not preserve the affine rank row.

This distinction cannot be repaired by imposing a finite dual-Heisenberg
spectator menu and taking a positive cross Gram.  There is an exact model
on

```text
H=C^8 tensor C^12
```

with the full three-qubit primal/dual Pauli packet acting on `C^8`, and two
reservoir involutions satisfying

```text
theta(V_1)=6/12=1/2,          theta(V_2)=10/12=5/6.          (SDG4)
```

Choose nested label reflections `C_1,C_2` with negative fractions `1/4`
and `1/8`, respectively, and put

```text
T_1=C_1 tensor V_1,          T_2=C_2 tensor V_2.             (SDG5)
```

The affine formula gives

```text
neg(T_1)=Phi_(1/4)(1/2)=1/2,
neg(T_2)=Phi_(1/8)(5/6)=1/4.                                (SDG6)
```

Thus taking `R_i=T_i,W_i=1` realizes both desired selector rank rows
exactly.  Set

```text
H_i=I_8 tensor V_i.                                         (SDG7)
```

Each `H_i` is a fixed involutory spectator normalizer in this representation
and commutes with every primal Pauli, every dual Pauli, every label
covariance, and `R_i,T_i`.  Consequently `W_iH_i=H_i` is a legitimate
dressing of the affine conjugator in `(SDG2)`.

If instead one forms the proposed dressed output words, then

```text
N_i=H_iT_i=C_i tensor I_12.                                (SDG8)
```

After the fixed label factors are removed, both dressed reservoir gauges
are literally the identity.  Their cross Gram is maximal on the whole
carrier, its polar is exact, and all mixed primal/dual Heisenberg tests are
exact.  Nevertheless the **raw** gauges `V_1,V_2` are not unitarily
conjugate because their positive ranks in `(SDG4)` differ.

Amplifying this model preserves all normalized ranks and makes it an
arbitrary-profile obstruction.  Therefore

```text
dual-Heisenberg covariance + positive dressed cross Gram
  does not imply the raw-gauge conjugacy required by SGS2.                (SDG9)
```

The dressed Gram can align the dressed words, but it records no information
about which commuting spectator was multiplied into each one.  Recovering
`SGS2` requires an ordinary occurrence relation that undresses `H_1,H_2`,
identifies them on the same reservoir, or compares the raw `T_i` directly.
This is exactly consistent with
`root-valued-overlap-does-not-undress-external-selector`: positivity is an
overlap theorem after occurrence typing, not an inverse to packet dressing.

This is a scoped finite-matrix interface countermodel, not a representation
of the full binary Leavitt elementary or Steinberg group.  No Property T,
Kazhdan input, canonical trace, literature theorem, local computation, or
Lean compilation is used.

DERIVATION
spectator-dressed-selector-gram-fence-proof

