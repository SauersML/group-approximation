---
rg: 2
id: finite-equidistributed-orbits-give-sofic-action
kind: claim
title: A measure-preserving topological action of a sofic group is sofic when finite invariant sets equidistribute to the measure
distinct_from:
  sofic-action-with-sofic-ergodic-components-is-sofic: that assembles finite models of ergodic components by disjoint union; this builds finite models from honest finite orbits lying inside the space, weighted by weak-star convergence
  paunescu-sofic-action-class-permanence: that imports the group families all of whose actions are sofic; this is a criterion for a single action of an arbitrary sofic group
artifacts:
  - research/artifacts/sl3z-lattice-space-hecke-sofic-2026-09-12.md
  - research/artifacts/sl3z-lattice-space-hecke-sofic-part2-2026-09-12.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be a countable sofic group acting by homeomorphisms on a second
countable locally compact Hausdorff space `X` and preserving a Borel probability measure `μ`. Suppose
there are finite `Γ`-invariant sets `V_k ⊆ X` with

```text
(1/|V_k|) Σ_(x ∈ V_k) f(x)  →  ∫ f dμ      for every f ∈ C_c(X).
```

Then `Γ ↷ (X,μ)` is sofic (Păunescu Definition 1.4).

Freeness of the action is not assumed, and the finite sets need not be asymptotically free. Freeness is
supplied by a sofic approximation of `Γ`, taken as a second tensor factor.

**Instances.**
* `SL_n(Z) ↷ SL_n(R)/SL_n(Z)`, through its Hecke orbits: `sl3z-lattice-space-action-is-sofic`.
* `SL_n(Z) ↷ T^n`, through the torsion points `(N^(−1)Z/Z)^n`.

**Model test.** The hypothesis fails where it must, for the Kun--Thom nonsofic generalized Bernoulli
action `G ↷ ({0,1}, fair)^(G/Γ)` of an infranormal non-normal Kazhdan pair. Kun--Thom
(arXiv:2608.06222v3, p. 2) show that the profinite closure of `Γ` contains its normal closure. So every
colouring with finite orbit agrees on `Γ` and on `gΓ` for some `g ∉ Γ`, while the product measure gives
disagreement probability `1/2` (part 2 artifact, Section 7). An irrational rotation shows the hypothesis
is not automatic.

**Credit.** A folklore-level principle; no source was checked.

Proof in `finite-equidistributed-orbits-give-sofic-action-proof`.
