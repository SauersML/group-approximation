---
rg: 2
id: component-measure-size-separates-compressor-images
kind: claim
title: A measure-type size on the space of Gamma-components separates realized twists of the Leavitt cover from their strict compressor images
refuted_by:
  - component-space-sizes-miss-leavitt-cover-defect
distinct_from:
  relative-normalization-modulo-kazhdan-kernel: that is the open normalization statement; this is one proposed size for proving it, which is false on the cover.
  support-proportion-size-separates-compressor-images: that is the refuted support-proportion candidate, a conjugation invariant of realizers alone; this is the relative candidate, which reads realized twists through their action on the measure space of sigma(Gamma)-components.
  component-space-sizes-miss-leavitt-cover-defect: that is the established obstruction; this is the specific candidate it refutes.
---

**REFUTED.** Proposed as the surviving shape in the Attempts of
`relative-normalization-modulo-kazhdan-kernel` and in
`finite-orbit-indices-miss-twists-without-finite-quotients`.
- **The candidate.** Let `Q_s` act on the measure space of
  `Gamma_s`-components, together with the compressor refinement factor from
  `sigma(t Gamma t^-1)`-components to `Gamma_s`-components and its fibre counts.
  These are Kun--Thom's orbit and isotropy sizes with counting replaced by
  measure.
- **The claim.** Some size read from these data is strictly monotone along the
  strict self-embedding `eps_u` of the subgroup `A <= Q_s` that carries the
  relative defect of the hyperbolic Leavitt cover.

Refuted by `component-space-sizes-miss-leavitt-cover-defect`:
- block invariance makes the component space pointwise fixed by `sigma(G)`, so
  the refinement factor is the identity and its fibre counts are `1`;
- compressed twists act on components exactly as the original twists do, so
  every such size takes equal values on `B` and `eps_u(B)`;
- host twists, including all of `A`, act on components as centralizer elements.

## Attempts

- **Diffuse cluster types with infinite orbits: dead.** Infinite orbits escape
  the finite-orbit obstruction, but `A` fixes every corner class
  `[sigma|_Gamma p]`, since `sigma(G)` preserves every component. So `A` acts
  trivially on the diffuse type distribution as well. See the refuter.
