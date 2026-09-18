---
rg: 2
id: q-coefficient-leavitt-tensor-unit-groups-are-fp
kind: claim
title: For a finitely presented central simple Q-ring B with vanishing Leavitt K-theory the unit group of B ⊗ L_Q(1,2) is finitely presented, but its simple scalar quotient cannot be
distinct_from:
  prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre: that is coefficients over F_p, where the scalars are finite, so the scalar quotient is finitely presented and simple; this is coefficients over Q, where the scalars Q^x are central and not finitely generated.
  leavitt-unit-groups-over-every-field-are-simple-mod-scalars: that is B = Q, which is not a finitely presented ring; this needs B finitely presented, which forces B noncommutative.
  gl-n-q-embeds-in-e-n-plus-1-of-a-fp-ring: that is the elementary group of the non-simple finitely presented Toeplitz ring, which is finitely generated but not known to be finitely presented; this is the unit group of a simple Leavitt tensor ring.
---

**OPEN.** Let `B` be a simple unital `Q`-algebra with centre `Q` that is finitely
presented as a ring, and put `R = B ⊗_Q L_Q(1,2) = B ⊗_Z L_Z(1,2)`. Suppose
`K_1(R) = K_2(R) = 0`; by `ara-cortinas-leavitt-tensor-k-theory-vanishes`, this holds
whenever `B` is regular supercoherent. Then `R^x` is finitely presented. It contains
`GL_∞(Q)`, `V` and `SL_3(Z)`, through the unital inclusion `L_Q(1,2) ⊆ R` and the
prefix-code map of `leavitt-unit-groups-over-every-field-are-simple-mod-scalars`.

## The scalar obstruction (established, elementary)

If `G` is a finitely presented group and `C ≤ Z(G)` is not finitely generated, then
`G/C` is not finitely presented.
- **Proof.** If `G/C` were finitely presented, `C` would be the normal closure of
  finitely many elements. The normal closure of finitely many central elements is the
  subgroup they generate, which is finitely generated.
- **Consequence for Q-coefficient Leavitt hosts.** In any `Q`-algebra `R` with
  `GL_N(R) = E_N(R)`, as for Leavitt tensors with `K_1 = 0`, the scalars
  `λ I`, `λ ∈ Q^x`, are central in `E_N(R) = GL_N(R) ≅ R^x`. `Q^x` is not finitely
  generated. So when `R^x` is finitely presented, the simple group `R^x / Q^x` is *not*
  finitely presented.
- **What this route can and cannot give.** Leavitt tensor hosts over `Q`-coefficients
  give at best a finitely presented overgroup of `GL_∞(Q)`, which serves
  `gl-n-q-explicit-natural-fp-overgroup`. They never give a finitely presented simple
  one by passing to the scalar quotient. The same holds for every `Q`-algebra whose
  elementary groups contain all rational scalars. `E_N(Q) = SL_N(Q)` is not such a case:
  its centre is finite.

## What transfers, and what is missing

Transfer is from `leavitt-tensor-hosts-khanh-transfer-proof` and
`prime-field-leavitt-tensor-hosts-proof`.
- **Characteristic-free steps.**
  - normalization and division (steps 1–2), which use only simplicity of `B`;
  - frame complexes (step 3);
  - the compression argument (step 4), which turns `K_i(R) = 0` into vanishing of the
    compression map on `H_n` for `n <= 2`;
  - Menal–Moncasi GE, Voronetsky's refinement, Krstić–McCool;
  - the signed transporters (prime-field proof, step 3).

  `R` is a finitely presented ring when `B` is.
- **Missing.** The Steinberg comparison `φ_4: St_4(R) ≅ GL_4(R)` uses
  `H_2(GL_3(R); Z) = 0`. Over `F_p` this comes from Khanh's acyclicity criterion
  (Theorem 2.2), whose scalar-weight Lemma 2.4 needs finite fields `F_(p^m) ⊆ R`. There
  are none in characteristic zero, and no replacement is known here. Two ways to close
  the gap:
  - a characteristic-zero proof of `H_2(GL_3(R); Z) = 0`;
  - direct checks of `j_3(N_3(R)) = 1` and simple connectivity of `|X_4(R)|` for Khanh's
    Theorem 5.1 in the signed form.
- **Simplicity of `R^x / Q^x`** would follow from `GL = E` and root detection modulo the
  centre, with two-sided division and `Z(R) = Q`. It is not needed for this claim.
