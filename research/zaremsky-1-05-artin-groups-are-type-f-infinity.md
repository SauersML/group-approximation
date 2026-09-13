---
rg: 2
id: zaremsky-1-05-artin-groups-are-type-f-infinity
kind: claim
title: "Zaremsky Problem 1.5 resolved: are all Artin groups of type F_infinity?"
root: true
distinct_from:
  artin-groups-satisfy-boone-higman: that is the Boone--Higman embedding problem for Artin groups with solvable word problem; this is the finiteness question for all Artin groups, about classifying spaces with finite skeleta, and says nothing about simple overgroups.
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 5, verbatim:
"Are all Artin groups of type F∞?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-1-05-by-yes` requires `every-artin-group-is-type-f-infinity`.
- **No**: `zaremsky-1-05-by-no` requires `some-artin-group-is-not-type-f-infinity`.

Never write a `requires: []` route into this claim.

**Reading.** An Artin group is
`A_Γ = ⟨ S | prod(s,t; m_st) = prod(t,s; m_st) whenever m_st < ∞ ⟩`
for a finite set `S` and a Coxeter matrix `m_st ∈ {2, 3, …, ∞}` (`s ≠ t`), where
`prod(s,t;m)` is the alternating word `sts…` of length `m`. "Type F_n" presupposes
finite generation, so `S` is finite. Every such group is finitely presented, so
type `F_2` is automatic. A group is of type `F_∞` when it has a `K(G,1)` with
finitely many cells in each dimension.

**Relation to the K(π,1) conjecture.** For every finite Coxeter graph the Salvetti
complex is a finite CW complex with fundamental group `A_Γ`, homotopy equivalent to
the orbit space of the complexified hyperplane complement. The K(π,1) conjecture
(`artin-group-k-pi-1-conjecture`) says this space is aspherical. It implies that every
Artin group is of type F, hence of type `F_∞`. The route
`artin-type-f-infinity-via-k-pi-1-conjecture` records this. Type `F_∞` is weaker, so a
"yes" answer might be reached without the conjecture.

**Known cases of the K(π,1) conjecture** (abstracts checked 2026-09-13; exact theorem
statements are imported in separate citation nodes):

- spherical type: P. Deligne, Invent. Math. 17 (1972);
- FC type, and dimension ≤ 2: R. Charney and M. W. Davis, J. Amer. Math. Soc. 8 (1995);
- large type: H. Hendriks (1985), contained in the dimension-2 case;
- affine type: G. Paolini and M. Salvetti, arXiv:1907.11795, Invent. Math. (2021);
- rank three: E. Delucchi, G. Paolini and M. Salvetti, arXiv:2206.14518, Geom. Topol.
  28 (2024);
- a large class of tree diagrams, and a class with cycles: J. Huang, arXiv:2305.16847,
  Invent. Math. (2024);
- 3-dimensional hyperbolic type except one example, quasi-Lannér type up to dimension 4,
  complete bipartite diagrams: J. Huang, arXiv:2405.12068;
- every Artin group of dimension 3: J. Huang and P. Przytycki, arXiv:2509.06914
  (preprint, September 2025);
- reduction: E. Godelle and L. Paris, arXiv:1007.1365, Math. Z. 272 (2012): if every
  free-of-infinity parabolic subgroup satisfies the conjecture, so does the group.

Here the dimension of `A_Γ` is the largest size of a subset `T ⊆ S` generating a finite
Coxeter group. Taking the preprint of Huang–Przytycki at face value, every Artin group of
dimension at most 3 is of type F, and dimension 4 is the first open dimension.

## Attempts

- 2026-09-13, lane z1-05-artin-kpi1: the K(π,1) route. Import the known classes and the
  Godelle–Paris reduction with verified statements, assemble the largest class they give,
  then attack dimension 4.
- 2026-09-13, lane z1-05-artin-direct: type `F_∞` without the K(π,1) conjecture.
