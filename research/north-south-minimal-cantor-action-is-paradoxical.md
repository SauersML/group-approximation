---
rg: 2
id: north-south-minimal-cantor-action-is-paradoxical
kind: claim
title: A minimal action on a Cantor space with one north–south element admits an elementary paradox 2[X] <= [X] with two pieces per copy
distinct_from:
  no-invariant-measure-steinberg-elementary-no-mf-quotient: that produces a paradox multiple from the absence of invariant measures through Tarski's theorem; this produces an explicit two-piece paradox from one north–south element, with no Tarski input.
artifacts:
  - research/artifacts/un-boundary-families-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed; proof in `north-south-minimal-cantor-action-is-paradoxical-proof`).**

**Definition.** Let `Γ` act on a compact space `X`. An element `g ∈ Γ` is *north–south* if there are points
`ξ^+ != ξ^-` with the following property: for every compact `K ⊆ X \ {ξ^-}` and every open `V ∋ ξ^+`, `g^n K ⊆ V`
for all large `n`. The same must hold for `g^(-1)`, with `ξ^+` and `ξ^-` exchanged.

**Statement.** Let `Γ` act minimally on a Cantor space `X`, and suppose some `g ∈ Γ` is north–south. Then there are
clopen partitions `X = A_1 ⊔ A_2 = B_1 ⊔ B_2` and elements `g_1, g_2, h_1, h_2 ∈ Γ` such that the four sets
`g_1 A_1`, `g_2 A_2`, `h_1 B_1` and `h_2 B_2` are pairwise disjoint. This is hypothesis (H-par) of
`paradoxical-cantor-actions-give-simple-kazhdan-not-mf`.

**Examples.**
- A free generator on `∂F_d`.
- `ab` on the boundary of `A * B`.
- `diag(p, p^(-1))` on `P^1(Q_p)`.
- Hyperbolic automorphisms of trees on ends.

**Model test.** An invariant probability measure `μ` excludes north–south elements on a minimal infinite space: it
would push `μ` onto an atom at `ξ^+`. A minimal `Z`-subshift has no north–south element.

**Review (un-verify-3, 2026-09-13): PASS.** Re-derived: `Fix(g) = {ξ^+, ξ^-}`; minimality makes point stabilizers infinite index, and Neumann's lemma gives `c` off four cosets, so `h = cgc^(-1)` is north–south with four distinct poles; compression with `A_1 = X\C`, `A_2 = C`, `B_1 = X\D`, `B_2 = D` into disjoint neighbourhoods via `g^n, h^n, g^(-n), h^(-n)`. `research/artifacts/un-review3-2026-09-13-part4.md` §2.
