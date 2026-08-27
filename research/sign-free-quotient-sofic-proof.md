---
rg: 2
id: sign-free-quotient-sofic-proof
kind: route
title: Abelianize the lamps, then replay the telescope-window pipeline
target: sign-free-quotient-sofic
requires: []
artifacts:
  - GroupApproximation/Sofic/CommutingLampQuotientSofic.lean
---

## Direct proof, formalized

Three layers, all in `GroupApproximation/Sofic/CommutingLampQuotientSofic.lean`.

1. **Killing the sign abelianizes the lamps, with no normal-form
   theory.**  The mod-two model `ModTwoLamp X = Multiplicative (X →₀
   ZMod 2)` receives the presented Clifford group through the
   universal property (`toModTwo`: sign to 1, lamp to the single-site
   flip; every relator dies in the abelian target).  The kernel is
   pinned to `zpowers (sign X)` by a SECTION: the quotient
   `SignQuot X` is abelian (two passes of the generator extension
   lemma `cliffordHom_ext`, itself the repo's
   `mem_subgroup_of_sign_mem_of_lamp_mem` applied to an `eqLocus`),
   so `Finsupp.liftAddHom` assembles `psiHom : ModTwoLamp X →*
   SignQuot X` from hand-rolled order-two point evaluations, and
   `psiHom ∘ toModTwo = mk'` on generators (`ker_toModTwo`).
2. **The ambient quotient is the mod-two model under the vertical
   action.**  `Phi := SemidirectProduct.lift` of `inl ∘ toModTwo` and
   `inr` is surjective with kernel `zpowers (signAmbient)`
   (`ker_Phi`), giving `signFreeQuotientEquiv : Ambient/⟨sign⟩ ≃*
   ModTwoLamp (Cosets) ⋊ Vertical`.
3. **The sofic pipeline replays verbatim.**  Finite site orbits of a
   telescope level (`SoficMarkedCompression.finite_levelSiteAction_orbit`,
   reused as-is) give finite invariant mod-two windows
   (`finsuppWindow`, locally finite by support counting); the local
   finite-kernel criterion `isSofic_semidirectProduct_of_invariant_finite`
   and the generic reassociation `SemidirectAssoc.assocEquiv` plus
   `SoficIntegerExtension.isSofic_int_semidirectProduct` finish
   exactly as for the Clifford ambient group.

Endpoints: `isSofic_signFreeQuotient` (generic: sofic base +
finite-index compression), `literalSignFreeQuotient_isSofic` (via the
kernel-checked `gammaBar_isSofic` and `conjD_range_finiteIndex`), and
`literalSignFreeQuotient_isSofic_and_not_isCDEOperatorMF`, the packaged
sofic-and-non-MF headline with the non-MF half from
`CommutingLampCollapse`.  Authored in the 2026-08-15 wave; the closing
validation build certifies the kernel check.
