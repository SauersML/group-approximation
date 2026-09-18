---
rg: 2
id: once-punctured-mcg-is-lipschitz-retract-of-out-free
kind: claim
title: The mapping class group of a once-punctured closed surface is a Lipschitz retract of Out(F_2g), hence undistorted
distinct_from:
  free-factor-system-stabilizers-distortion-dichotomy: that is the Handel--Mosher dichotomy for stabilizers of free factor systems in Out(F_n); this is the Hamenstädt--Hensel retraction onto a surface mapping class group, which is not the stabilizer of a free factor system.
  subsurface-mapping-class-groups-are-undistorted: that places subsurface mapping class groups undistortedly inside a surface mapping class group; this places a surface mapping class group undistortedly inside Out(F_2g).
---

**ESTABLISHED (literature import).**

> **Theorem 4.3 (Hamenstädt--Hensel, arXiv:1109.2687v3).** Map(S_{g,1}) is a Lipschitz retract
> of Out(F_{2g}). In particular, it is undistorted (i.e. the inclusion map is a quasi-isometric
> embedding).

Here `S_{g,1}` is the closed genus-`g` surface with one puncture, so `π_1(S_{g,1}) = F_{2g}`.
`Map(S_{g,1})` is identified with its image under the Dehn--Nielsen--Baer map. By their Theorem 4.2,
that image is the set of outer automorphisms that preserve the cusp class.

**Scope.**
- One puncture only. The paper's Remark 4.1 says the authors "believe that our methods can also be
  used with minor modifications to treat the case of more than one boundary component, however we
  did not verify the details". Surfaces with several punctures are not covered.
- The retraction goes onto the group in `Out(F_{2g})`. The paper does not state an `Aut(F_{2g})`
  version for a boundary component.

Nothing is reproved here, and there is no Lean counterpart.
