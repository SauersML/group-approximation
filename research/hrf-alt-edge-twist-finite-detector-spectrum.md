---
rg: 2
id: hrf-alt-edge-twist-finite-detector-spectrum
kind: claim
title: Finite detection of perfect-vertex edge twists is exactly a Schur-multiplier lift-discrepancy spectrum
distinct_from:
  edge-twist-extensions-of-triangle-colimits-moment-test: that tests splitting on the kernel of a fixed finite quotient by cellular moments; this identifies all finite central detectors through unique vertex lifts and explains why first-level full moment spaces can be forced
artifacts:
  - research/artifacts/hyperbolic-rf-alternatives-2026-09-20.md
---

Let `Λ` be a nonpositively curved triangle colimit with trivial face group, finite
perfect vertex groups `A_v`, and `H^2(A_v;F_p)=0`. Put
`V=⊕_e Hom(E_e,F_p)`, with the orientation convention of
[[edge-twist-extensions-of-triangle-colimits-moment-test]], and let `Λ_c`
be its central edge twist by `c in V`.

For every finite quotient `f:Λ ->> Q`, a central extension class
`β in H^2(Q;F_p)` has unique lifts of the vertex maps. Their discrepancies
on the three edges define a linear map

```
D_f: H^2(Q;F_p) = Hom(H_2(Q;Z),F_p) -> V.
```

Then `Λ_c` has a finite quotient injective on its central `F_p` iff
`c in im D_f` for some finite quotient `f`. The union of these images is
a subspace, since taking the image in a product gives a common refinement.
Thus a quotient whose Schur multiplier has order prime to `p` supplies
no nonzero twist through this central detector test. This is not a
classification of finite quotients of `Λ`.

There is a sharper statement at one level. If `N=ker f` has
`H^1(N;F_p)=0` and `H^2(Q;F_p)=0`, restriction
`H^2(Λ;F_p) -> H^2(N;F_p)` is injective. Consequently no nonzero edge twist
splits over `N`. If, in addition, `f` is injective on every vertex group
(so `N` is torsion-free in this setting), then for cyclic order-`p` edges
the moment space at `N` is therefore all of `F_p^3`.

**Status:** written elementary proof independently reviewed on 2026-09-20,
including the vertex-injectivity hypothesis in the moment corollary; see
Section 5 of `research/artifacts/hyperbolic-rf-stability-audit-2026-09-20.md`.
This is a detector and an audit of first-level evidence; it establishes no
persistent class and no non-residually-finite hyperbolic group.

Proof: [[hrf-alt-edge-twist-finite-detector-spectrum-proof]].
