---
rg: 2
id: dendrite-rearrangement-groups-are-finitely-presented
kind: claim
title: The rearrangement groups G_n of the Ważewski dendrites D_n are finitely presented
distinct_from:
  dendrite-rearrangement-group-g3-has-simple-commutator-subgroup: that proves the commutator subgroups [G_n, G_n] are simple for all n ≥ 3; this asks whether the groups G_n themselves are finitely presented.
artifacts:
  - research/artifacts/gq-bh-openq-lists.md
---

**ESTABLISHED (in the literature).** For every `n ≥ 3` the dendrite rearrangement
group `G_n` is of type `F_∞`, and in particular finitely presented.

- **Source:** D. Perego and M. Tarocchi, *Eventually self-similar groups acting on
  fractals*, arXiv:2412.04138v1 (Dec 2024), subsection "Finiteness Properties for
  Rearrangement groups": Lemma `lem.dendrites` and the corollary after Lemma
  `lem.airplane` (TeX l.2463–2540, read at source). The corollary gives type `F_∞`
  for every `G_n` and for the airplane group `T_A`. The authors say it "answers
  [dendrite, Question 3.7]", i.e. the question quoted below.
- **Status on main until 09-18:** this node was opened as OPEN from the question
  alone. Tarocchi's thesis (arXiv:2412.02339, TeX l.4362–4367) already announced
  the answer as upcoming work with Perego.

The question as printed: M. Tarocchi, *On Thompson groups for Ważewski dendrites*,
arXiv:2310.14660v3, TeX l.1079–1085:

> Now that we know that each $G_n$ is finitely generated, it is natural to ask the
> following question, which we do not investigate here.
> What further finiteness properties do dendrite rearrangement groups have? Are they
> finitely presented? Are they $F_\infty$?

The same question is in Tarocchi's thesis, arXiv:2412.02339, TeX l.5158–5163.

## How the proof goes, with one correction

Checked independently by lane bh-dendrite (not a review by anyone else).

- **Why Belk–Forrest does not apply directly.** Belk–Forrest's Theorem 4.1
  (arXiv:1510.03133, `thm:finfty`, read at source) needs, for every `m`, all but
  finitely many graphs of the graph family to have `m` collapsible subgraphs.
  - The star replacement graph of `𝒟_n` has the automorphism swapping `ι` and `τ`.
    So the graph family contains every orientation of every tree
    (Tarocchi, `rmk:undirected`).
  - Orient each tree towards a leaf. Then every internal vertex has an incoming
    edge, no star matches the directed replacement graph, and the descending link is
    empty. That happens at every rank.
- **The fix.** Perego–Tarocchi add the finitary automorphism `φ_n`, which swaps
  edges `1` and `n` of the star, as a self-similar tuple. Contractions then ignore
  orientation (their π-contractions). Equivalently, run Belk–Forrest's cube complex
  on graphs modulo the `ι ↔ τ` flip, using Tarocchi's undirected-edge convention
  (thesis, `sub.undirected.edges`).
- **The descending link.** Let `T` be an expansion tree with `k` internal vertices,
  each of degree `n`, and let `T°` be the subtree they span.
  - A star at an internal vertex `v` is contractible exactly when `v` has at most
    two internal neighbours. Its `n − 2` other neighbours must be leaves.
  - Such a `v`, with `j ≤ 2` internal neighbours, carries `C(n−j, 2−j)·(n−2)!`
    orientation-free characteristic maps.
  - Two contractions are compatible exactly when their centres are distinct and
    non-adjacent.
- **Correction to one sentence.** The proof of `lem.dendrites` says there are
  "precisely `(n−2)!` π-contractions for every internal vertex". That is not right:
  there are none when `v` has three or more internal neighbours, and `(n−1)!` when it
  has one. The lemma's conclusion survives:
  - The vertices of `T°`-degree at most 2 are at least `max(L, k − L + 2) ≥ (k+2)/2`
    in number, where `L` is the number of leaves of `T°`.
  - They span a union of paths, so at least `(k+2)/4` of them are pairwise
    non-adjacent.
  - Each characteristic map overlaps at most `3·C(n,2)·(n−2)!` others. So Belk–Forrest's
    uniformly-dense flag criterion (`thm:DenseConnectivity`, read at source) makes the
    descending link `(m−1)`-connected once `k` is large enough.
  - Stabilizers are automorphism groups of finite trees, and each rank sublevel has
    finitely many orbits of cells. Brown's criterion with Bestvina–Brady then gives
    `F_∞`.

## Boone–Higman

Nothing new: this is BH-neutral. `G_n ≤ V` (Tarocchi,
`prop:dendrite:Thompson:comparison`), and `V` acts with type (A) (the `P = ∅` case of
`ct-p-z-acts-on-the-nonnegative-integers-with-type-a`). So `G_n` and `[G_n, G_n]` lie in
`B_A` and embed in a finitely presented simple group by
`type-a-action-gives-boone-higman-for-subgroups`.

## What remains (OPEN): is the simple group [G_n, G_n] finitely presented?

`[G_n, G_n]` is finitely generated (Tarocchi, `thm:comm:fg`). It is simple for
`n ≥ 4` (Tarocchi, `thm:comm:simple`) and for `n = 3`
(`dendrite-rearrangement-group-g3-has-simple-commutator-subgroup`). Its abelianization
is computed through `Φ = Π × Δ : G_n → Z/2 ⊕ Z` (Tarocchi, `thm:commutator`), where `Δ`
is the sum of the endpoint derivatives over all rational endpoints.

- **Reduction.** `[G_n, G_n]` has index 2 in `N = ker Δ`. Since `G_n` is `F_∞`,
  Bieri–Renz (recalled, not re-read) gives: `N`, hence `[G_n, G_n]`, is `F_m` exactly
  when both `[Δ]` and `[−Δ]` lie in `Σ^m(G_n)`. Finite generation already gives `Σ^1`.
- **Calibration, heuristic only.** On Tarocchi's copy `H ≅ F` acting on an arc
  between two rational endpoints, `Δ` restricts to `χ_0 + χ_1` up to sign. This
  matches Tarocchi's values `Φ(g_0) = (0,0)` and `Φ(g_1) = (0,−1)`. In `F`,
  `ker(χ_0 + χ_1)` is finitely generated but not finitely presented, because
  Bieri–Geoghegan–Kochloukova show `Σ^2(F)^c` is the convex hull of
  `Σ^1(F)^c = {[χ_0], [χ_1]}` (recalled). Σ-invariants do not restrict to subgroups,
  so this suggests, but does not show, that one sign of `Δ` fails `Σ^2`.
- **Why it matters:**
  - A yes would give finitely presented simple groups of dendrite type, possibly of type
    `F_∞`, inside `V`.
  - A no would give finitely generated simple subgroups of `V` that are not finitely
    presented.
  - Either way it is BH-neutral.

## Lesson for general BH

In a Stein–Farley / Brown proof of finite presentation (the G3g "rigid ⇒ fp" step of the
master route), quotient the complex by each cell's local symmetry first, here the
`ι ↔ τ` flip. Otherwise a relabelling that the group can undo creates fake descending-link
minima at every height. These look like a failure of local rigidity but are only an
artifact of the complex. After quotienting, a tree-shaped rule passes by the elementary
count that at least half the vertices of a finite tree have degree at most 2.

Process lesson: this printed question had been answered by its own author ten months
before the node was opened, and the thesis announced it. Check the author's later arXiv
listing before opening a node for a printed question.
