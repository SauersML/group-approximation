---
rg: 2
id: quadratic-breakpoint-psl2z-groups-satisfy-boone-higman
kind: claim
title: Every finitely generated group of piecewise PSL_2(Z) homeomorphisms of the projective line with rational and quadratic irrational breakpoints, including every finitely generated subgroup of Monod's H(Z), embeds in a finitely presented simple group
distinct_from:
  lodha-moore-groups-embed-in-lodha-circle-group: that is the Lodha--Moore groups, whose pieces lie in PGL_2(Z[1/2]) and whose breakpoints are rational, inside Lodha's circle group; this is piecewise PSL_2(Z) with quadratic irrational breakpoints, inside a periodic germ extension of V.
  lodha-circle-group-is-finitely-presented-and-simple: that imports Lodha's piecewise projective simple group; this uses only his Cantor model of Thompson's T, and not the group S.
---

**ESTABLISHED** by `quadratic-breakpoint-psl2z-groups-satisfy-boone-higman-proof` (lane proof, not
independently reviewed). No priority is claimed. An arXiv search on "piecewise projective" and
"simple" found no statement of this kind.

**Statement.**
- Let `PP_Z` be the group of homeomorphisms `g` of `P^1(R) = R ∪ {∞}` for which there are
  finitely many breakpoints, each in `Q ∪ {∞}` or a real quadratic irrational, such that `g`
  agrees with an element of `PSL_2(Z)` on each complementary arc.
- Then every finitely generated subgroup `H ≤ PP_Z` embeds in the finitely presented simple group
  `G_Π'` of `periodic-germ-extensions-of-v-are-virtually-simple`, for a finite set `Π` that depends
  on `H`.
- So every such `H` satisfies the Boone--Higman conjecture.

**Examples.**
- **Thompson's `T`.** It is the case of rational breakpoints only (Lodha's model).
- **Monod's group `H(Z)`.** Its elements are the piecewise `PSL_2(Z)` homeomorphisms whose
  breakpoints are fixed points of hyperbolic elements of `PSL_2(Z)` (Monod, arXiv:1209.5229; the
  definition was not re-read at source). Every real quadratic irrational is such a fixed point. So
  `H(Z) ≤ PP_Z`, and every finitely generated subgroup of `H(Z)` embeds in a finitely presented
  simple group.

**Scope.**
- This is about finitely generated subgroups. `PP_Z` itself is not finitely generated, since its
  breakpoints meet infinitely many `PSL_2(Z)`-orbits.
- The proof covers every subgroup whose breakpoints lie in finitely many `PSL_2(Z)`-orbits.
