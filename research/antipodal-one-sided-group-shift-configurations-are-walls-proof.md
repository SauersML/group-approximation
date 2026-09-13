---
rg: 2
id: antipodal-one-sided-group-shift-configurations-are-walls-proof
kind: route
title: Superpose two opposite one-sided configurations pushed apart
target: antipodal-one-sided-group-shift-configurations-are-walls
requires: [sft-wall-rigidity-iff-idempotent-commutator-ideal, sft-crossed-product-fp-iff-quantum-rigid]
artifacts:
  - research/artifacts/quantum-rigidity-group-shifts-and-gluing-2026-09-13.md
---

The artifact, Section 1 (Proposition G1), gives the proof.

1. **The superposition.** Translate `c_+` by a lattice vector `g_+` with `<g_+, v> >= L`, and `c_-` by `g_-`
   with `<g_-, v> <= -L`. Put `y = σ^(g_+) c_+ + σ^(g_-) c_-`. It lies in `X`, because `X` is a shift-invariant
   group.
2. **The wall.** The difference set of the pair `(0, y)` is `supp y`. It is contained in
   `{<n,v> > L} ⊔ {<n,v> < -L}`, and meets both. For `L > D`, it is not `2D`-connected.
3. **Consequences.** The first cited claim turns the wall certificate into a noncommuting triangular family on
   `k^2` and a non-idempotent commutator ideal. The second turns failure of rigidity at every scale into
   infinite presentation of the crossed product.
