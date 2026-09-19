---
rg: 2
id: rigid-minimal-topfree-sft-with-non-amenable-point-stabilizer
kind: claim
title: Over the finitely presented group (F_2 × Z) * Z there is a minimal, topologically free SFT, quantum rigid over every field at all large scales, with a point whose stabilizer is F_2 × Z; so its action is not topologically amenable
distinct_from:
  quantum-rigid-minimal-topfree-subshift-actions-are-amenable: that conjectures that every rigid minimal topologically free subshift action is topologically amenable; this is a counterexample, and that node names this one in refuted_by.
  tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts: that builds the rigid minimal topologically free SFT from any two compactifications; this chooses a compactification with a global fixed point, which the gluing turns into non-amenable isotropy.
  f2-times-f2-has-a-quantum-rigid-free-minimal-sft: that asks for a free (not merely topologically free) rigid minimal SFT over a one-ended non-amenable group; this is only topologically free, over a free product, and is not free.
  decidable-groups-lie-in-fp-groups-with-rigid-topfree-sfts: that asks for rigid minimal topologically free dynamics over an overgroup of every decidable group; this shows that such dynamics can carry non-amenable isotropy, so no amenability obstruction stands in the way.
---

**ESTABLISHED** (2026-09-18, lane proof by bh-break, not reviewed), conditional only on its two imports
(route `non-amenable-stabilizer-from-gluing-a-cone-compactification`).

## Statement

Let `Λ = (F_2 × Z) * Z`, which is finitely presented. There is an SFT `X ⊆ A^Λ` such that:
1. `Λ ↷ X` is minimal and topologically free;
2. `X` is `D`-quantum rigid over every field, for all large `D`;
3. some `x_∞ ∈ X` has `Stab(x_∞) = F_2 × Z`, the first free factor.

Since `F_2 × Z` is not amenable and point stabilizers of topologically amenable actions are amenable,
`Λ ↷ X` is not topologically amenable. So `quantum-rigid-minimal-topfree-subshift-actions-are-amenable`
is false.

**General form.** For every `Λ_0 ∈ 𝒞`, the group `(Λ_0 × Z) * Z` carries a rigid, minimal, topologically
free SFT with a point stabilized by all of `Λ_0 × Z`.

## What it does not touch

`Λ` is exact, being a free product of exact groups. So the weaker adversarial form, "a rigid minimal
topologically free SFT forces the acting group to be exact", is untouched. Through the gluing, any non-exact
member `Λ_0` of `𝒞` would refute it, via `Λ_0 * Z`. So it is at least as strong as "`𝒞` contains only
exact groups".

## Lesson for general BH

Rigidity is blind to isotropy. The amenability obstruction to the master route is gone, and with it the
heuristics that "every rigidity mechanism manufactures amenable boundary dynamics" and that "non-amenable
isotropy destroys rigidity". A cone over a rigid compactification pushes a whole non-amenable group onto
one point, and the tree-gluing turns that point into a stabilizer of a minimal rigid system. What remains
of the analytic question is exactness of the acting group itself.
