---
rg: 2
id: chordal-graph-products-of-finite-groups-have-lp
kind: claim
title: Graph products of finite groups over chordal graphs are virtually free, hence their full C*-algebras have the LP
artifacts:
  - research/artifacts/enders-shulman-ffw-llp-sources-2026-08-21.md
distinct_from:
  chordal-partial-positive-operator-matrices-lift: that lifts chordal-pattern partial positive operator matrices through a C*-quotient (Paulsen--Rodman); this is a group-theoretic LP theorem for chordal graph products, proved by clique separators and Bass--Serre theory, with no matrix completion anywhere.
  chordal-abelian-graph-products-hs-stable: that imports Hilbert--Schmidt stability of chordal graph products of abelian (possibly infinite) vertex groups; this proves the lifting property of the full C*-algebra for finite vertex groups, a different conclusion on a different class, by virtual freeness rather than stability.
  triangle-colimit-llp-reduces-to-relator-local-splitting: that handles genuine triangles of groups whose colimit crushes an infinite partial amalgam onto a finite vertex group; this settles the right-angled shadow, where all clique-poset legs are injective and the chordal case is tree-like.
---

Let `X` be a finite graph, `(G_v)` nontrivial finite vertex groups,
and `G_X` the graph product (free product of the `G_v` modulo
`[G_u, G_v] = 1` for each edge `uv`).

**THEOREM.**

```text
(a) If X is chordal (every cycle of length >= 4 has a chord), then
    G_X is finitely generated virtually free, and C*(G_X) has the
    lifting property (LP), hence the LLP.                        (CG1)

(b) Sharpness at the square: if X contains an induced 4-cycle
    (1,2,3,4), then G_X contains G_{C_4} = (G_1 * G_3) x (G_2 * G_4)
    and in particular Z x Z, so G_X is not virtually free; if
    moreover (|G_1|-1)(|G_3|-1) >= 2 and (|G_2|-1)(|G_4|-1) >= 2,
    then G_X contains F_2 x F_2, so establishing the LLP (or LP) for
    C*(G_X) would answer Fournier-Facio--Willett Question 1.6
    positively.  The first non-chordal graph is already
    question-hard.                                               (CG2)
```

Proof: `chordal-finite-graph-products-virtually-free-proof`.  The
virtual-freeness statement in (a) is due to Lohrey--Sénizergues,
*When is a graph product of groups virtually-free?*, Comm. Algebra 35
(2007), 617-621 (cited at statement level; their PDF was unreachable
this session, and the route below is deliberately self-contained, so
nothing here rests on the citation).  The LP consequence does not
appear in Fournier-Facio--Willett arXiv:2603.18456v2: their chordal
results (Example 4.30, Remark 4.31, both read at source) concern
right-angled Artin and Coxeter groups only, via free derived
subgroups.  The LP input is Enders--Shulman arXiv:2403.12224
Corollary 4.6 (finitely generated virtually free groups are LP;
source-verified).

**Scope remarks.**

1. **Non-chordality does not force failure.**  The pentagon of
   `Z/2`'s — the graph product over `C_5` with all vertex groups of
   order 2 — is the reflection group of the right-angled hyperbolic
   pentagon (Coxeter relations `r_i^2`, `(r_i r_{i+1})^2`, nothing
   else), which acts properly cocompactly on `H^2`, hence is
   virtually a closed orientable hyperbolic surface group (Selberg
   plus the orientation subgroup), hence virtually a limit group.
   By Fournier-Facio--Willett Theorem 1.2(iv) (limit groups are LP)
   and Corollary 4.1 (countable virtually LP groups are LP), it HAS
   the LP.  So the chordal/non-chordal boundary is not an LP
   boundary; (CG2) shows it is a *hardness* boundary.
2. **The first genuinely open pentagon.**  `C_5` with some vertex
   group of order `>= 3` (the chamber-transitive lattices on
   Bourdon-type right-angled hyperbolic buildings): every separator
   of `C_5` contains a non-edge, so every amalgam decomposition of
   `G_{C_5}` amalgamates over an infinite virtually free subgroup
   (e.g. `G_{C_5} = G_{path(2,3,4)... } *_{G_1 * G_4} ((G_1 * G_4) x
   G_5)` — both legs injective), where no published (L)LP permanence
   applies; and no `F_2 x F_2` hardness is available (`C_5` has no
   induced square, and the centralizer of `<G_1 cup G_3>` meets only
   the abelian `G_2`-direction, so the obvious commuting-free-pairs
   are absent).  Open in both directions; this is the
   finite-vertex-group analogue of Fournier-Facio--Willett Question
   1.7 (square-free RAAGs, "the first non-chordal example is the
   pentagon").
3. **Ladder to the program seam.**  Tree nerves of finite groups are
   LP (Enders--Shulman); chordal nerves are still tree-like (clique
   separators) — this node; cyclic nerves with all clique-poset legs
   injective (the pentagon of remark 2) are open; the Kac--Moody
   triangle adds the strictly harder feature that the colimit crushes
   an infinite partial amalgam onto a finite vertex group — a
   non-injective pushout leg — and
   `triangle-colimit-llp-reduces-to-relator-local-splitting` proves
   that crossing it is exactly a local-splitting problem.  Graph
   products can never exhibit that last feature: their clique-poset
   colimits have injective legs, which is why the right-angled shadow
   stops one rung below the triangle.
