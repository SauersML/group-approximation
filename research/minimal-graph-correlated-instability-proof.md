---
rg: 2
id: minimal-graph-correlated-instability-proof
kind: route
title: Extract the marked Majorana wall and isolate the blockwise projective alternative
target: minimal-graph-ce-forces-correlated-actor-instability
requires:
  - kun-thom-nonsofic-wreath
  - infranormal-compact-closure-normal
  - kazhdan-weak-ucp-stability-is-flexible-stability
  - clifford-direct-sum-dilution-forces-an-exact-good-block
  - finite-presentation-refutes-marked-graph-scalar-window
---

Assume the rank-three minimal marked crossed product is Connes embeddable.
Lift its actor generators and base Majorana to matrices.  The canonical trace
and marked edge give a hyperlinear actor approximation satisfying

```text
[c,u_s] -> 0  (s in K),
c (u_h c u_h^*) + (u_h c u_h^*) c -> 0.
```

Weak ucp-stability of the residually finite Kazhdan actor is flexible
HS-stability.  A flexible correction, Kazhdan averaging of the extended
lamp, and compact normality of the closure of the infranormal subgroup make
the corrected lamp commute with `rho(h)`, because `h` is in the normal
closure of `Gamma`.  Leakage back to the original corner makes the returned
lamp equal to the base lamp, contradicting its anticommutation.

For the finite image table of the finitely presented Steinberg cover, a
vanishing-cost covariant Clifford retraction leaves vanishing multiplication
defects on a direct sum of invariant irreducible Clifford blocks.  The
direct-sum quantization theorem selects one block with scalar phase-space
curvature on every tested triangle, contradicting
`finite-presentation-refutes-marked-graph-scalar-window`.  Every CE
realization therefore escapes that blockwise projective locus by a fixed
nonvanishing amount.  If the cover table has `m` triangles, the product
Lipschitz bound makes the floor explicit:

```text
epsilon+3 eta >= sqrt(2/m),
```

where `epsilon` is its actor multiplication defect and `eta` the actor part
of the retraction cost.
