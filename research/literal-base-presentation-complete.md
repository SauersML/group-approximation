---
rg: 2
id: literal-base-presentation-complete
kind: claim
title: The twenty literal base relators present exactly the affine group
distinct_from:
  literal-kazhdan-clifford-inputs: That claim asserts property (T), injectivity of the doubling endomorphism and `v_1` outside its image — all of them statements that already hold in the affine IMAGE and transfer along any surjection. This claim is the opposite direction: that the evaluation map has no kernel, so the presented group has no extra elements.
  literal-telescope-split-normal-form: That claim is about the whole literal group, giving the retraction `E -> V` and the split `E = N_E semidirect V`; this one is about the six-generator base subpresentation alone and is one of its inputs.
  literal-group-structural-normal-form: That root asks for a normal form, a kernel description and the word problem for `E`; this claim settles only the base factor.
artifacts:
  - GroupApproximation/Monsters/LiteralBaseCompleteness.lean
  - notes/E_SOFICITY_SELF_CONTAINED_2026-08-16.md
---

The canonical affine evaluation of the twenty-relator base subpresentation of
`def:E` is an isomorphism

```text
Base  ~=  gammaBar  =  Z^3 semidirect SL_3(Z),
```

i.e. the twenty displayed relators present the affine group exactly, with no
extra elements surviving.  Lean: `LiteralBaseCompleteness.baseAffineEquiv`.

**Why this is a node and not a remark.**  Everything the literal soficity
chain says about the telescope levels — `Gamma_n ~= Z^3 semidirect SL_3(Z)`,
hence finitely generated, hence residually finite — is a statement about the
PRESENTED base, while the easy proofs (linearity, Mal'cev, the formalized
`gammaBar_residuallyFinite`) are statements about the MATRIX group.  Until the
evaluation was known injective, the gap between them was the single conditional
input `B ~= Gammabar` that the 2026-08-15 adversarial audit of
`notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md` identified, and it made
`literal-group-sofic` conditional while `literal-group-fails-mf-conventions`
was not — a trust-surface inversion recorded in that document's header.

It is now discharged in-repo and with no literature premise.  The proof
assembles four finished layers: the semidirect skeleton of the presented base
reduces injectivity to the two factors; on the rotation factor the
eight-relator group receives the thirteen-relator Steinberg presentation by
audited short words and `P13DescentMaster.toSL3_injective` forces the rotation
matrix model to be injective; on the translation factor the three commuting
generators normal-form into `v_1^a v_2^b v_3^c`, and the affine matrix reads
off the exponents, so it is the identity only when the rotation part and all
three exponents are trivial.

Consumers: `literal-telescope-split-normal-form-proof` (the identification of
`V` and of the levels), `literal-telescope-core-lef-via-central-embedding`
(residual finiteness of `Gamma_n`), and the Lean endpoints of
`literal-mark-quotient-not-mf-parity-proof`.
