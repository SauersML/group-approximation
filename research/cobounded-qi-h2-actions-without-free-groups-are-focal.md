---
rg: 2
id: cobounded-qi-h2-actions-without-free-groups-are-focal
kind: claim
title: A cobounded isometric action on a space quasi-isometric to H^2 by a group without free subgroups is focal, with circle boundary
---

Let `X` be a geodesic metric space quasi-isometric to `H^2`. Let `G` be a group with no non-abelian
free subgroup, acting on `X` by isometries with a coarsely dense orbit. Then there are `δ ≥ 0` and
`o ∈ X` with the following properties. The objects `(x|y)_w`, `∂X` and `(u|v)_o` are defined as in
`busemann-null-isometries-have-no-boundary-contraction`.

1. `X` satisfies `(x|z)_w ≥ min{(x|y)_w, (y|z)_w} − δ` for all `x, y, z, w ∈ X`.
2. `∂X` carries a topology with these three properties:
   - it is homeomorphic to the circle `S^1`;
   - every isometry of `X` acts on `∂X` by a homeomorphism;
   - if `u_n → u` in `∂X`, then `(u_n|u)_o → ∞`.
3. `G` fixes some `ξ ∈ ∂X`.
4. Some `g ∈ G` fixes exactly two points of `∂X`, and one of them is `ξ`.

This is the structure half of the reduction `thompson-f-no-cobounded-qi-h2-action-via-busemann`. It
is meant as a packaging of classical coarse geometry plus the classification of hyperbolic actions.
The third pass below reduces it, through route `cobounded-qi-h2-focal-via-dsu-classification`, to the
single claim `geodesic-spaces-qi-to-h2-have-circle-gromov-boundary` together with the established claims
`busemann-null-isometries-have-no-boundary-contraction` and
`two-boundary-fixed-points-block-cobounded-qi-h2-actions`. The circle claim has a direct route,
`qi-h2-circle-boundary-via-quantitative-morse-lemma`.

## Attempts

- **Proof outline (2026-09-16, swarm lane zaremsky-2-18).** Each ingredient is classical, but none of
  the sources was re-read for this claim.
  - **Item 1.** A geodesic space quasi-isometric to a Gromov hyperbolic geodesic space is hyperbolic
    (Bridson–Haefliger, *Metric spaces of non-positive curvature*, III.H.1.9; numbering unverified).
    Slim triangles imply the four-point inequality with a larger constant (same book, III.H.1.22;
    unverified).
  - **Item 2.**
    - For the topology, use the sequential boundary with neighbourhood bases
      `{v : (u|v)_o > r}` (Bridson–Haefliger III.H.3; Väisälä, *Gromov hyperbolic spaces*,
      Expo. Math. 23 (2005), Section 5; both unverified). Then the third property is immediate.
    - Quasi-isometries between geodesic hyperbolic spaces induce homeomorphisms of boundaries.
      Bridson–Haefliger III.H.3.9 is stated for proper spaces, as far as recalled.
    - **Here `X` need not be proper**: for example, glue infinitely many unit segments at every point
      of `H^2`. So one needs the non-proper version, as in Väisälä, Section 6 (unverified).
    - `∂H^2 ≅ S^1` is standard.
  - **Items 3 and 4.** These use the classification in arXiv:2406.12982v2. Its text was read on
    2026-09-16; it is itself attributed to Gromov [Gro87, 8.2], Hamann [Ham17] and ABR23 Theorem 2.7,
    none of which were read.
    - Citation 1.1: the action is elliptic, parabolic, lineal or non-elementary according as
      `|Λ(G)| = 0, 1, 2, ∞`.
    - Quoted: "A loxodromic element g fixes precisely two points in the (Gromov) boundary ∂X".
    - Definition 1.2: a non-elementary action is quasi-parabolic (focal) if `G` fixes a point of
      `∂X`, "or equivalently if all loxodromic elements have one fixed point in ∂X in common".
      Otherwise it is of general type, and "a standard ping-pong argument shows that the group
      contains non-abelian free subgroups".
    - Coboundedness makes every boundary point a limit of orbit points, so `Λ(G) = ∂X ≅ S^1` is
      infinite. The absence of free subgroups rules out general type. So the action is focal and
      fixes some `ξ`.
    - Remaining gap in this first pass: that a non-elementary action contains a loxodromic element.
      This is part of Gromov's classification but is not stated in the BFFZ text. Once it has one,
      `g` fixes exactly two points, and `ξ` is one of them since `G` fixes `ξ`.
  - **Weak points for a referee (first pass).**
    - The non-proper boundary theory, including the boundary homeomorphism `∂X ≅ S^1`.
    - The identification of `Λ(G)` for the sequential boundary with the one used in the
      classification.
    - The existence of loxodromics in non-elementary actions.
- **Second pass (2026-09-16, same lane): the loxodromic gap and the limit-set identification.**
  Source: P.-E. Caprace, Y. de Cornulier, N. Monod, R. Tessera, *Amenable hyperbolic groups*,
  arXiv:1202.3585v2 (12 Nov 2013). The PDF was fetched and its text extracted on 2026-09-16. Quotes
  below are verbatim up to extraction spacing.
  - **Non-proper setting.** Section 3 says: "We emphasize that X will not be assumed proper, unless
    explicitly stated otherwise."
  - **Their boundary matches ours.**
    - Their definition: "A sequence (x_n) in X is Cauchy-Gromov if (x_n|x_m)_x tends to infinity when
      n, m both tend to ∞ ... We identify two Cauchy-Gromov sequences (y_n) and (z_n) if (y_n|z_n)
      tends to infinity."
    - For sequences converging at infinity this agrees with our equivalence. One direction restricts
      to the diagonal. For the other, `(y_i|z_j) ≥ min{(y_i|y_j), (y_j|z_j)} − δ`.
  - **Limit set.** "consists of those elements (y_n) in the boundary, that can be represented by a
    Cauchy-Gromov sequence of the form (g_n x) with g_n ∈ Γ".
  - **Hyperbolic element.** γ is "hyperbolic if lim_{n→∞} (1/n)|γ^n(x)|_x > 0". This is BFFZ's
    "loxodromic" (the map `n ↦ g^n x` is a quasi-isometric embedding).
    - Since `|g^n x|_x` is subadditive in `n`, Fekete gives `|g^n x|_x ≥ nτ` for `τ` the limit.
    - Also `d(g^m x, g^n x) = |g^{n−m}x|_x ≤ |n − m| d(gx, x)`.
  - **Gromov's classification**, their Section 3.A, attributed to [Gro87, 3.1]:
    - "horocyclic if it is unbounded and has no hyperbolic element";
    - "lineal if it has a hyperbolic element and any two hyperbolic elements have the same endpoints";
    - "non-elementary and focal if it has a hyperbolic element, is not lineal and any two hyperbolic
      elements have a common endpoint";
    - "general type if it has two hyperbolic elements with no common endpoint".
    - Together with "bounded", these cases are exhaustive by definition, and every non-elementary case
      has a hyperbolic element by definition.
  - **Their Proposition 3.1.** "The action of Γ is bounded if and only if ∂X_Γ is empty; horocyclic if
    and only if ∂X_Γ is reduced to one point; ... lineal if and only if ∂X_Γ consists of two points;
    ... focal if and only if ∂X_Γ is uncountable and Γ has a fixed point ξ in ∂X_Γ; ... of general type
    if and only if ∂X_Γ is uncountable and Γ has no finite orbit in ∂X."
    - Its proof is a "Sketch of proof", ending "The other verifications are left to the reader".
  - **Coboundedness gives full limit set (elementary).** Suppose every point is within `r` of `G·o`,
    and `y_i → u`. Choose `g_i` with `d(g_i o, y_i) ≤ r`.
    - Then `(g_i o|y_i) ≥ d(y_i,o) − r`, and `d(y_i,o) ≥ (y_i|y_j) → ∞`.
    - So `(g_i o|y_j) ≥ min{(g_i o|y_i), (y_i|y_j)} − δ → ∞`, hence `g_i o → u`, and `Λ(G) = ∂X`.
  - **Items 3 and 4 follow**, given items 1 and 2.
    - `∂X ≅ S^1` is uncountable, so by Proposition 3.1 the action is focal or of general type.
    - General type is excluded by the BFFZ ping-pong quote and the absence of free subgroups.
    - So `G` fixes some `ξ`, and some hyperbolic `g` exists.
    - By the BFFZ quote, `g` fixes exactly two boundary points. `ξ` is one of them.
  - **Still unverified.**
    - Items 1 and 2: the non-proper boundary theory, above all `∂X ≅ S^1` with the Gromov-product
      topology.
    - The proofs behind Proposition 3.1 and the ping-pong statement. Only their statements were read.
- **Third pass (2026-09-16, same lane): Das–Simmons–Urbański, arXiv:1409.2155v7 (28 Jun 2016).**
  The PDF was fetched and its text extracted on 2026-09-16. It works without properness throughout.
  - Route `cobounded-qi-h2-focal-via-dsu-classification` quotes its classification of isometries and
    groups (Theorems 6.1.4 and 6.2.3, Proposition 6.2.14), the Busemann derivative formula
    (Proposition 4.2.16), and the ping-pong lemma with the free-subgroup step of the proof of
    Proposition 10.5.4.
  - Parabolic groups are excluded by the bound `|p − q| ≤ 18δ` of
    `busemann-null-isometries-have-no-boundary-contraction` and coboundedness. Lineal groups are
    excluded by `two-boundary-fixed-points-block-cobounded-qi-h2-actions` applied to an index-at-most-2
    subgroup. General type is excluded by the absence of free subgroups.
  - Remaining hole at the time of this pass: `geodesic-spaces-qi-to-h2-have-circle-gromov-boundary`, the
    circle boundary for a non-proper `X`. It was closed later the same day by the direct route
    `qi-h2-circle-boundary-via-quantitative-morse-lemma`. The route also rests on the statements, not the
    proofs, of the quoted DSU results.
