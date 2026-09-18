---
rg: 2
id: periodic-dense-sft-hosts-have-only-thompson-simple-subgroups
kind: claim
title: Full-group hosts restrict to closed invariant subsets, so if a subshift has dense finite orbits every finitely generated simple subgroup of the full group of G_V × (Λ ⋉ X) embeds in Thompson's V, and over Z every finitely generated subgroup has word problem in PSPACE
distinct_from:
  definable-parameter-hosts-cap-simple-subgroups-at-pspace: that specializes parameters using finite presentation; this restricts the phase space to invariant pieces, needs no finite presentation, and applies to subshift hosts whose phase space has no tame presentation.
  fp-alternating-full-groups-of-free-subshifts-force-sft: that says finite presentation forces finite type; this says why the SFT must also be free (and, for simple hosts, why minimal is the natural choice) and why dimension one is excluded.
artifacts:
  - research/artifacts/gq-bh-bh-free-32-order-rigidity.md
---

**ESTABLISHED** through `periodic-dense-sft-hosts-restriction-proof` (lane proof, elementary; not
independently reviewed). No priority is claimed.

## Setting

- `𝒢` is an ample groupoid on a Cantor space `Y`, and `[[𝒢]]` is its topological full group. The
  alternating full group `A(𝒢)` is a subgroup of it.
- `G_V` is the groupoid of Thompson's `V` on `C = {0,1}^N`.
- `Λ` is a finitely generated group, `X ⊆ A^Λ` a subshift, and `Λ ⋉ X` the action groupoid.

This is the master-route shape `A(G_V × (Λ ⋉ X))` of `research/artifacts/gq-bh-synthesis-master-route.md`.

## Statement

1. **Restriction principle.** Let `Y_j ⊆ Y` be closed `𝒢`-invariant subsets whose union is dense.
   Then every finitely generated simple subgroup of `[[𝒢]]` embeds, by restriction, in
   `[[𝒢|_{Y_j}]]` for some `j`.
2. **Dense finite orbits.** If the points of `X` with finite `Λ`-orbit are dense, every finitely
   generated simple subgroup of `[[G_V × (Λ ⋉ X)]]` embeds in `V`. Hence its word problem is in
   polynomial time (Birget; not re-read). Every finitely generated simple subgroup of
   `[[Λ ⋉ X]]` is finite.
3. **Dimension one.** For `Λ = Z` and any sofic subshift `X`, in particular any SFT, every finitely
   generated subgroup of `[[G_V × (Z ⋉ X)]]` has word problem in PSPACE. The reason is that folding
   `x ↦ (x_n, x_{-1-n})_{n ≥ 0}` makes the action parameter-free ω-automatic. If `X` is an
   irreducible SFT, item 2 applies too, because periodic points are dense. A minimal `Z`-SFT is a
   single finite orbit.

## Lesson for general BH: how the master route's SFT hosts escape the complexity wall

The master route needs a free minimal SFT `X` over `Λ = Λ₀ × H`. The caps above and
`definable-parameter-hosts-cap-simple-subgroups-at-pspace` say what such a host must avoid, and
**they do not block it**.

- *Freeness and minimality are forced, not decorative.*
  - Any dense family of closed invariant pieces with tame full groups turns the host into a
    residually tame group. Its simple subgroups are then tame.
  - Finite orbits give `V`. So hard simple hosts need `X` without dense finite orbits.
  - Minimality removes every proper closed invariant piece at once, so the restriction principle
    has nothing to act on.
- *Dimension one is excluded* (design rule 1): items 2 and 3.
- *Where the complexity enters.*
  - The global shifts embed `Λ` in the host, faithfully when `X` is free. Deciding `w ≠ 1` needs
    `WP(Λ)` and the pattern language `L(X)`, which is decidable for minimal SFTs.
  - These are the only two non-definable ingredients: the multiplication rule of `Λ` on `A^Λ`, and
    the solution set `X` of finitely many local rules. The second is non-deterministic, i.e. a
    global `Π^0_1` constraint.
  - In dimension one, SFTs are regular, so both are tame. Over a group with undecidable domino
    problem, `X` has no tame presentation, and the collapse theorem does not apply.
- *So the escape is legitimate and has a price.* Hardness must come from `Λ₀`, as design rule 4
  says, or from `L(X)`. `WP(Λ₀)` is at least `WP(G)` for the input `G ≤ Λ₀`, and it is carried
  into the host through the shift rule, never through a parameter.

## Not claimed

- That any free minimal SFT host is finitely presented or simple. That is crux G2/G3g.
- That hardness of `L(X)` alone, over a tame `Λ` such as `Z²`, can give hard hosts. It would need a
  free minimal `Z²`-SFT with a hard language and a finitely presented host, and neither is
  addressed here.
