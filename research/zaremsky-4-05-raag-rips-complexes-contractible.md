---
rg: 2
id: zaremsky-4-05-raag-rips-complexes-contractible
kind: claim
title: "Zaremsky Problem 4.5 resolved: is the Rips complex of every RAAG with the standard word metric contractible at large scale?"
root: true
distinct_from:
  zaremsky-4-03-rips-complex-of-zn-contractible: that root is the same question for the free abelian groups Z^n only, the case where the defining graph is complete; this root asks it for every finite defining graph
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 4, Problem 5,
verbatim: "(Added 10/2/24): Is the Rips complex of any RAAG with the
standard word metric contractible for large enough Rips parameter?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-4-05-by-yes` requires `every-raag-is-rips-type-r`.
- **No**: `zaremsky-4-05-by-no` requires `some-raag-is-not-rips-type-r`.

Never write a `requires: []` route into this claim.

**Reading.** `Γ` is a finite simplicial graph and `A_Γ` its right-angled
Artin group, marked by the standard generating set `V(Γ)`. The word metric
is the combinatorial (`l^1`) metric on the vertex set of the universal cover
of the Salvetti complex, a CAT(0) cube complex whose 1-skeleton is the Cayley
graph. The Rips complex `R_r(A_Γ)` has a simplex for every finite set of
diameter `≤ r`. "Contractible for large enough Rips parameter" means type R in
the sense of Li–Sánchez Saldaña (arXiv:2608.24279): a marked group `(G,S)` is
of type R if there is `r_0` with `R_r(G,S)` contractible for every
`r ≥ r_0`. The metric takes
integer values, so the open and closed conventions differ by a shift of 1.
"Any RAAG" means every finite `Γ`, with `r_0` allowed to depend on `Γ`.

The generating set matters. For the cubical generating set (products of
pairwise commuting standard generators) the Cayley graph is the thickening of
the CAT(0) cube complex, and Chalopin–Chepoi–Genevois–Hirai–Osajda
(arXiv:2002.06895) prove that CAT(0) cubical groups are Helly through that
thickening (theorem number not re-read here). The question is about the
standard (`l^1`) generators. There balls do not have the Helly property: the
radius-1 balls around the four corners of a unit square in `Z^2` pairwise
intersect and have no common point.

**Known cases (imports and corollaries, all on this graph):**

- `Γ` complete, `A_Γ = Z^n`: Virk, arXiv:2405.09134, Theorem 5.1
  (`rips-complexes-of-integer-lattices-are-contractible`).
- `Γ` triangle-free (dimension ≤ 2): Li–Sánchez Saldaña, arXiv:2608.24279,
  Theorem 1.5 (`triangle-free-raags-are-rips-type-r`).
- Closure under graphs of groups with finite edge groups, hence free
  products: arXiv:2608.24279, Theorems 1.3 and 1.4
  (`rips-type-r-closed-under-finite-edge-group-splittings`). So every RAAG
  whose connected components are cliques or triangle-free graphs is of type R
  (`raags-with-clique-or-triangle-free-components-are-type-r`).
- Scale 2 only: `VR_2(A_Γ)` is contractible for triangle-free `Γ`
  (Hulbert–Zaremsky, arXiv:2608.25614, Theorem B;
  `triangle-free-raag-vr2-is-contractible`).

- Complete multipartite `Γ` (products of free groups `F_{n_1} × ⋯ × F_{n_k}`,
  e.g. `F_2 × F_2 × F_2` and `Z^2 × F_2`): contractible for `t ≥ k(k+1) − 1`,
  proved on this graph 2026-09-13, UNREVIEWED
  (`complete-multipartite-raags-are-rips-type-r`). Combined with free products:
  `raags-with-multipartite-or-triangle-free-components-type-r`.

Open as of 2026-09-13: every connected `Γ` that contains a triangle and is not
complete multipartite. The smallest is the triangle with a pendant vertex,
`A_Γ = Z × (Z^2 * Z)`.

## Attempts

- 2026-09-13 (z4-05-raag-rips): imported the known cases above. Working on
  dimension ≥ 3 through Virk's local crushing (arXiv:2405.09134, Definition
  3.6 and Theorem 3.7), with crushing sets that leave geodesic intervals
  toward the base point. Details are in `every-raag-is-rips-type-r`.
