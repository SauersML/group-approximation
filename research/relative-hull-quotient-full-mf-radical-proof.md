---
rg: 2
id: relative-hull-quotient-full-mf-radical-proof
kind: route
title: Take the common quotient of the source and the saturated group over the whole saturated group
target: relative-hull-quotient-with-full-mf-radical
requires:
  - common-quotient-onto-normal-subgroup
  - defect-saturation-full-mf-radical
artifacts:
  - research/artifacts/mf-radical-linear-certificate-2026-09-07.md
---

## Why sufficient

Let `Q` be the two-generated, finitely presented, torsion-free,
acylindrically hyperbolic property-(T) group with `Res_MF(Q)=Q`.

Apply `common-quotient-onto-normal-subgroup` with `G_1=G`, `G_2=Q`,
`D=Q`, `F_1=Omega` and `F_2` empty.  Both groups are torsion-free, so their
finite radicals are trivial; `Q` is acylindrically hyperbolic, so it is
infinite, and it is normal in itself, so `D` is an infinite normal subgroup
of `G_2`.  The conclusion supplies `P` acylindrically hyperbolic with trivial
finite radical and surjections `alpha_1:G ->> P`, `alpha_2:Q ->> P` with
`alpha_1|_Omega` injective.  Clause 3 makes `P` torsion-free and clause 4
makes it finitely presented, since `G` and `Q` are.

The remaining properties come from `alpha_2`.  Two-generation and property
(T) pass to quotients.  Full MF residual passes through surjections, so
`Res_MF(P)=P`.  Put `phi=alpha_1`.

For the girth statement take `G=F_2`, which is finitely presented,
torsion-free, and acylindrically hyperbolic, and `Omega` the ball of radius
`n` in the free basis.  Injectivity on `Omega` means `P` has no relation of
length at most `n` in the images of the basis.
