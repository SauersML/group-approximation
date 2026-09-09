---
rg: 2
id: jacobson-laurent-kernel-surjects-natural-affine-module
kind: claim
title: The actual Laurent cover has a noncentral kernel surjecting onto the natural Laurent module
distinct_from:
  jacobson-positive-root-gluing-misses-laurent-coherence: that omits the shared opposite-root equation; this satisfies the full presentation and disproves coherence in the actual group.
  jacobson-coherence-defect-is-an-orthogonal-translation: that identifies equivalent words without deciding their vanishing; this proves those words are nonidentity using an explicit affine quotient.
  jacobson-shift-literal-quotient-is-laurent-times-z: that identifies the literal image and compares kernels; this proves its abstract kernel is infinite and noncentral.
artifacts:
  - research/artifacts/jacobson-laurent-cover-has-a-noncentral-affine-quotient-2026-09-08.md
---

Let `R=F_2[z,z^(-1)]` and let `kappa:Lambda->SL_3(R)` be
the established Laurent map. There is a surjective homomorphism

```text
Phi:Lambda -> R^3 semidirect SL_3(R)
```

whose linear projection is exactly `kappa`. For the coherence
word `e=q(h u h)q(h r h)`, with `u=[h c h,k]`, one has

```text
Phi(e)=translation_(z e_1),
Phi([e,k])=translation_(z e_3),
Phi(ker(kappa))=R^3.
```

Thus `e!=1`, `[e,k]!=1`, and `ker(kappa)` is infinite and
noncentral. Specializing `z=1` gives a faithful eight-point
action of the image `AGL_3(F_2)`, of order `1344`, satisfying
both complete finite-factor tables, their entire common subgroup,
and both mixed relators.

For the corresponding full word `E` in `Gamma=Theta_shift`,

```text
E!=1,  [E,k_P]!=1,  [E,L]=[E,t]=1.
```

The literal kernel consequently has the same infinite natural
module quotient. These statements identify a quotient of the
kernel; they do not identify the entire kernel or the order of
the abstract word `e`. Every displayed affine map factors through
`Gamma/L`, so it kills the head. The marked matrix gap remains open.

DERIVATION
jacobson-affine-laurent-countermodel-proof
