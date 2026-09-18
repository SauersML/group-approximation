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

- hyperbolic cyclic type: T. Haettel and J. Huang, Duke Math. J. 174 (2025); locally reducible
  (spherical parabolic subgroups of dimension ≤ 2 or of type `A_3`): R. Charney (2004).

Here the dimension of `A_Γ` is the largest size of a subset `T ⊆ S` generating a finite
Coxeter group. Taking the preprint of Huang–Przytycki at face value, every Artin group of
dimension at most 3, and every Artin group on at most 4 generators, is of type F. So
dimension 4 and rank 5 are the first open cases.

## Attempts

- 2026-09-13, lane z1-05-artin-kpi1: the K(π,1) route.
  - Verified imports of the known classes and of two reductions: Godelle–Paris
    (`artin-k-pi-1-reduces-to-free-of-infinity-parabolics`) and Huang–Przytycki
    (`artin-k-pi-1-reduces-to-triangle-free-diagrams`).
  - Every Artin group on at most 4 generators satisfies the conjecture and is of type F
    (`artin-groups-of-rank-at-most-four-satisfy-k-pi-1`, through the preprint).
  - Assembly: the conjecture holds when every maximal free-of-infinity subset spans a group
    that satisfies it (`artin-k-pi-1-from-maximal-free-of-infinity-subsets`).
  - First uncovered almost spherical cases: the four compact hyperbolic Coxeter 4-simplex
    groups with tree diagrams (`compact-hyperbolic-4-simplex-artin-groups-satisfy-k-pi-1`).
- 2026-09-13, lane z1-05-artin-direct: type `F_∞` without the K(π,1) conjecture.
  - Reduced to free-of-infinity graphs (`artin-type-f-n-reduces-to-free-of-infinity-graphs`).
  - `F_{k+1}` holds iff the first nonvanishing `π_k(Sal)` is finitely generated
    (`artin-type-f-k-plus-1-iff-salvetti-pi-k-fg`).
  - Brown's criterion on Deligne or Artin complexes needs connectivity at the level of the
    K(π,1) conjecture (`deligne-connectivity-iff-artin-complex-connectivity`).
  - No independent route was found.
- 2026-09-17, sw-100 (scale-shifter): finiteness length is monotone on induced subgraphs.
  - The Godelle–Paris retraction lifts to a 1-Lipschitz retraction `A_Γ → A_T` on word
    metrics, so type `F_n` passes down to standard parabolic subgroups
    (`artin-type-f-n-passes-to-standard-parabolic-subgroups`). This corrects the scope of the
    dead attempt "Subgroups, quotients, retractions": finite generation of homotopy modules
    is lost, but the group-level property is not.
  - Two-sided reduction: `fl(A_Γ) = min fl(A_X)` over maximal free-of-infinity `X`
    (`artin-f-n-iff-maximal-free-of-infinity-parabolics-f-n`). A counterexample, if any, has a
    free-of-infinity minimal one of rank at least 5 whose proper parabolic subgroups are `F_∞`,
    and failure is upward closed.
