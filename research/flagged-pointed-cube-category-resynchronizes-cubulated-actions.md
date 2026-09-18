---
rg: 2
id: flagged-pointed-cube-category-resynchronizes-cubulated-actions
kind: claim
title: Allowing pointed-cube states to forbid extra adjacent walls gives a Li-Garside category with trivial units whose boundary is the whole Roller boundary and on which every element of a free cocompact cubulated group acts by a global bisection
requires:
  - pointed-cube-bisection-locus-is-the-regular-boundary
  - pointed-cube-categories-are-li-garside-categories
  - cubulated-groups-act-by-bisections-of-a-pointed-cube-category
distinct_from:
  cubulated-groups-act-by-bisections-of-a-pointed-cube-category: that coding records only crossed adjacent walls and resynchronizes only at regular points; this adds voluntary wall labels, and every point resynchronizes.
  pointed-cube-bisection-locus-is-the-regular-boundary: that proves the old coding fails off R; this is the repair, with the flag that coding lacked built into the states.
---

**ESTABLISHED** through `flagged-pointed-cube-category-proof` (lane proof, elementary apart
from standard CAT(0) cube complex facts and X. Li, arXiv:2110.04505v2, read at source; not
independently reviewed; no priority claimed).

## The flagged category `C⁺_X`

`X` is a locally finite, finite-dimensional CAT(0) cube complex, and `G` acts on it freely on
vertices and cocompactly. Write `adj(w)` for the set of hyperplanes adjacent to the vertex
`w`.
- **Objects.** `G`-orbits of pairs `(w, σ)` with `w` a vertex and `σ ⊆ adj(w)` any set of
  adjacent walls, the **forbidden** walls. There are finitely many.
- **Morphisms.** `G`-orbits of triples `(w,σ; u,τ)` such that:
  - `H(w,u) ∩ σ = ∅`, so the path never crosses a forbidden wall;
  - `τ ⊆ adj(u)` and `τ ⊇ π(σ; w, u) := (σ ∪ H(w,u)) ∩ adj(u)`.

  The target is `[(w,σ)]`, the domain is `[(u,τ)]`, and composition is concatenation.
- **Two kinds of morphism.** When `τ = π(σ;w,u)` it is an ordinary step. When `u = w` and
  `τ ⊋ σ` it is a **flag** `ε`, which forbids a wall the future will not cross.
- **Relation to the old coding.** `C_X` sits inside as the morphisms from `(w, ∅)` with
  minimal labels, where the minimal label is `Max`. The only new data are the voluntary
  flags.

## Statement

1. **Li-Garside.** `C⁺_X` satisfies every standing hypothesis of Li's `intro:Gars`, with
   trivial units.
   - It is cancellative, right Noetherian and finitely aligned, and it has lcms: the lcm
     of `(u_1,τ_1)` and `(u_2,τ_2)` is the median join `j` with the union of the
     propagated labels.
   - The one-step morphisms (a cube step or a flag, with any admissible label) form a
     locally finite Garside family. The normal forms are Niblo–Reeves normal cube paths
     with maximal compatible labels, and every `(𝔖^{≤L})^♯` is closed under left
     divisors.
2. **Boundary.** The base cone of Li's `∂Ω(C⁺_X)` is the whole Roller boundary `∂_R X`,
   with its topology. The point `ω` is the maximal character
   `D_ω = {(z,σ) : z ∈ I(o,ω), σ ⊇ Max(o,z), σ ∩ H(z,ω) = ∅}`.
   - The cone of `[(w,σ)]` is the Roller boundary of the sector
     `Q(w,σ) = ∩_{J ∈ σ} (w-side of J)`.
3. **Resynchronization everywhere.** Every `g ∈ G` acts on `∂_R X` by a global compact open
   bisection of `𝒢⁺ = I_l ⋉ ∂Ω(C⁺_X)` reduced to the base cone. At any `ω`, take `n` large
   along a ray `z_n → ω`, with `κ_n = Max(o,z_n)`, and let:
   - `F_g = H(g^{-1}o, o)`;
   - `M_+ = Max(o,gz_n) ∖ gκ_n` and `M_- = gκ_n ∖ Max(o,gz_n)`. Both are sets of `g`-images
     of walls of `F_g` adjacent to `z_n`, and both are eventually constant.

   Then near `ω`, `g` is the prefix replacement
   `[o→(z_n, κ_n ∪ g^{-1}M_+)] w ↦ [o→(gz_n, Max(o,gz_n) ∪ M_-)] w`. The two domains
   are the same object, since `Max(o,gz_n) ∪ M_- = g(κ_n ∪ g^{-1}M_+)`.

So gate (G1) of `virtually-torsion-free-cubulated-groups-satisfy-boone-higman` holds for
every free cocompact cubulation on which `G` acts faithfully on `∂_R X`: take the closed
carrier `∂Ω(C⁺_X)`.

## Why the flag is exactly the missing datum

`pointed-cube-bisection-locus-is-the-regular-boundary` showed where the old coding breaks.
Along a tail beside a wall `J ∈ F_g`, the codings from `o` and from `go` disagree forever
on whether `J` counts as crossed. The disagreement is harmless for the future, since the
tail never crosses `J` either way, but the old states could not express it.

A flag says "the future avoids `J`" without saying "`J` was crossed". So the two codings
become the same object after one flag move. On futures that later leave the carrier of
`J`, the flag is dropped by propagation and nothing changes.

## Lesson for general BH

When two base points' codings of the same boundary point never resynchronize, the missing
state is usually a **promise about the future**, not a record of the past. Letting states
carry voluntary promises (forbidden walls) makes the coding base-point free. The category
stays Garside, because promises propagate by the same local rule as crossings and join by
union.

The same device should repair any geodesic coding whose states record "which walls lie
behind": median graphs, buildings with wall trees, and Coxeter-type cell complexes.
