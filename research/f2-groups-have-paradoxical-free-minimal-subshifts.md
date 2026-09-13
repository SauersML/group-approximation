---
rg: 2
id: f2-groups-have-paradoxical-free-minimal-subshifts
kind: claim
title: Every finitely generated group containing a nonabelian free subgroup has a free minimal Cantor subshift with a finite generating clopen family and an elementary paradox
distinct_from:
  north-south-minimal-cantor-action-is-paradoxical: that gets a paradox from one north–south element on a given minimal space; this builds a free minimal symbolic model from a paradoxical decomposition of the group itself, with no boundary.
  gjs-countable-groups-have-free-minimal-subflows: that gives free minimal subflows of 2^G with no paradox; this multiplies one by the encoding of a paradoxical decomposition and keeps the paradox.
artifacts:
  - research/artifacts/un-horofunction-families-paradoxical-subshifts-2026-09-13.md
---

**ESTABLISHED (unreviewed; proof in `f2-groups-have-paradoxical-free-minimal-subshifts-proof`).**

**Statement.** Let `Γ` be a finitely generated group containing a nonabelian free subgroup. Then `Γ` acts on a Cantor
space `Z` (a subshift over a finite alphabet) and the action is free and minimal, with two further properties.
- **(H-gen)** Some finite family of clopen subsets of `Z` has `Γ`-translates separating the points of `Z`.
- **(H-par)** There are clopen partitions `Z = A_1 ⊔ A_2 = B_1 ⊔ B_2` and elements `g_1, g_2, h_1, h_2 ∈ Γ` such that
  `g_1 A_1, g_2 A_2, h_1 B_1, h_2 B_2` are pairwise disjoint.

These are the hypotheses of `paradoxical-cantor-actions-give-simple-kazhdan-not-mf` (freeness gives topological freeness).

**Construction.**
- A free subgroup `⟨a, b⟩` gives a two-piece paradox on `Γ` for left translation: `W(a) ⊔ a W(a^{-1})`, extended along a
  transversal of right cosets.
- Encode the four pieces as a configuration `x_0 ∈ ({0,1}^4)^Γ` under the action `(γ·x)(g) = x(gγ)`; partitions and
  disjointness are closed coordinate identities, so they pass to `X = cl(Γ x_0)`.
- Multiply by a free minimal subflow `W ⊆ 2^Γ` (Gao–Jackson–Seward) and take a minimal subset `Z ⊆ X × W`.

**Model test.** An amenable `Γ` has an invariant probability measure on every compact `Γ`-space, which (H-par) excludes.
So the free-subgroup hypothesis is load-bearing.

**Instances** (recalled, not imported): non-elementary hyperbolic groups, not virtually solvable finitely generated
linear groups. By Tarski's theorem the same construction should work for every finitely generated non-amenable group;
that is not claimed here.
