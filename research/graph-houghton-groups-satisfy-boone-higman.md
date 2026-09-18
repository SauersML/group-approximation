---
rg: 2
id: graph-houghton-groups-satisfy-boone-higman
kind: claim
title: The graph Houghton groups of Hill–Kwak–Udall–West embed in finitely presented simple groups
distinct_from:
  aut-free-groups-satisfy-permutational-boone-higman: that is Boone–Higman for each Aut(F_n) (BFFHZ); this asks for one finitely presented group that contains every Aut(F_n) at once, which would reprove that theorem.
  houghton-groups-embed-in-thompson-v: that settles the classical Houghton groups; this asks the same for the graph Houghton groups, which are not commensurable with them.
artifacts:
  - research/artifacts/gq-bh-openq-lists.md
---

**OPEN.** T. Hill, S. Kwak, B. Udall and J. West, *Asymptotically rigid mapping class
groups of infinite graphs*, arXiv:2508.21264v1 (28 Aug 2025), "Open questions",
TeX l.297:

> One might ask whether the Boone--Higman conjecture for the graph Houghton group is
> true, which would yield a new proof of the Boone--Higman conjecture for
> $\Aut(F_n)$, recently established in [BFFHZ]. More broadly, one may ask whether the
> Boone--Higman conjecture holds for all Houghton-type groups.

**The groups.**
- `B(g,h,r)` is the group of asymptotically rigid proper homotopy classes of a graph
  `Γ_r` with `r` ends, all accumulated by loops (TeX l.344–430).
- `B(g,h,r)` is of type `F_{r-1}` but not `FP_r` (Theorem `thm:finitenessGraphHoughton`).
- The pure subgroup `PB_r`, for `r ≥ 3`, has an explicit finite presentation on
  `h_2, …, h_r, σ, τ, η` (Theorem `thm:PBrPresentation`), and it contains `Aut(F_n)`
  for every `n`.
- For `r ≥ 3` it is a finitely presented group with solvable word problem
  (§`sec:WordProblemDF`). So it is a genuine Boone–Higman input.

**Status of the wider question ("all Houghton-type groups").**
- **Classical Houghton groups:** settled on main, since they embed in `V`
  (`houghton-groups-embed-in-thompson-v`).
- **Other types:** the braided, surface, handlebody, doubled-handlebody and graph
  Houghton groups are pairwise non-commensurable (their Theorem
  `thm:MainThm_NonCommensurable`). Boone–Higman is not recorded on main for any of them.

**Natural routes.**
1. **Zaremsky's criterion** (`twisted-brin-thompson-finite-presentation-criterion`).
   Find a faithful action of `PB_r`, or of a finitely presented overgroup, with finitely
   many orbits on 2-subsets and finitely generated point stabilizers.
2. **The Cantor-graph group.** The asymptotically rigid group of the graph with a
   Cantor set of ends is `F_∞` (same theorem). Embed `B(g,h,r)` in it, and treat that
   group, as for the surface case (Funar–Kapoudjian, Aramayona et al.).
3. **The BFFHZ relative-automorphism action**
   (`relative-automorphism-action-is-highly-transitive`). Adapt it to the
   compactly supported part, which is a direct limit of relative automorphism groups of
   free groups, extended by the loop shifts `h_i`.

## Attempts

**Attempt 1 (bh-graph-houghton, 09-18): route 3 carried out, reduced to one finiteness gate.** Route
`graph-houghton-bh-via-eventually-rigid-g-automorphisms` (lane proofs, not reviewed):
- **The embedding.** PB_r embeds in the group P_G(r) of eventually rigid G-automorphisms of G * F(X), using a lift
  based at the end e_1 (`graph-houghton-groups-embed-in-eventually-rigid-g-automorphisms`). The surface and
  braided Houghton groups embed the same way, modulo cited faithfulness.
- **The action.** For G finitely generated, infinite, simple and MIF, P_G(r) acts on the finitely supported
  homomorphisms to G. The action is faithful and highly transitive, with finitely generated stabilizers
  (`eventually-rigid-g-automorphism-groups-act-with-type-a-except-fp`).
- **What is left.** Only finite presentation of P_G(r), recorded as the OPEN node
  `eventually-rigid-g-automorphism-groups-are-finitely-presented`. A G-relative Armstrong–Forrest–Vogtmann presentation
  with bounded-support relators would suffice (lane sketch there).

Lesson for general BH: BFFHZ's Hom_G action localizes to asymptotically rigid actors. For every Houghton-type
Aut-group, only finiteness is left; the transitivity side is inherited from finite rank.
