---
rg: 2
id: induced-lattice-action-mixing-forces-c0-homogeneous-space
kind: claim
title: An induced action L x_Gamma Z is mixing for a cocompact lattice only if L has vanishing coefficients on L^2_0(L/Gamma)
distinct_from:
  howe-moore-lattice-nonsofic-action-transfers-to-mixing: that proves mixing when the envelope is Howe-Moore; this is the necessary condition for mixing of any induced action, with no hypothesis on the envelope
  tree-product-lattice-nonsofic-gives-mixing-nonsofic-action: that proves mixing for lattices with dense projections in a product of two simple tree groups; this says which envelopes and seed lattices can never give mixing
---

**ESTABLISHED.** Let `L` be a locally compact second countable group, `Γ, Λ <= L`
lattices with `Λ` cocompact, and `(Z, ζ)` a p.m.p. `Γ`-space. Put

```text
W = L ×_Γ Z = (L × Z)/Γ,      (l, z)·γ = (lγ, γ^(-1) z),
```

with `L` acting on the left and its invariant probability measure. Let `π_0` be
the Koopman representation of `L` on `L^2_0(L/Γ)`.

1. **Necessity.** If `Λ ↷ W` is mixing, then every matrix coefficient of `π_0`
   vanishes at infinity on `L`.
2. **Consequences.** If `Λ ↷ W` is mixing, then
   * every closed non-compact subgroup `S <= L` acts ergodically on `L/Γ`;
   * if `Γ ≠ L`, then `Γ` contains no infinite subgroup that is normal in `L`.
3. **Bernoulli seed.** If `Z = ({0,1}, fair)^Γ`, the Koopman representation of `L` on
   `L^2_0(W)` is `π_0 ⊕ π_B`, where `π_B` is contained in a multiple of the left
   regular representation of `L`. So `Λ ↷ W` is mixing iff `Λ ↷ L/Γ` is mixing.

So an induced action can be mixing only when the homogeneous space `L/Γ` already has
decay of correlations for all of `L`. A discrete normal subgroup of `L` inside `Γ`,
or a closed non-compact subgroup with invariant functions on `L/Γ`, rules out mixing
for every seed `Z` and every cocompact lattice `Λ`.

Proof in `induced-lattice-action-mixing-forces-c0-homogeneous-space-proof`.
