---
rg: 2
id: gkmp-amalgam-product-mf-permanence
kind: claim
title: Gao-Kunnawalkam-Manzoor-Patchell MF permanence for product-amalgams with a separable edge
distinct_from:
  shulman-amalgam-mf-criterion: that gives a necessary-and-sufficient corona-embedding condition for a general amalgam; this is a checkable sufficient condition, requiring only that the edge subgroup be separable and one side residually finite, and it is the tool that handles the asymmetric product edge Shulman's symmetric theorem cannot.
  twisted-rope-edge-is-mf-under-relative-profinite-compatibility: that is this repository's bespoke finite-quotient theorem for a twisted HNN edge under a compatibility hypothesis; GKMP is a published theorem for an untwisted product-amalgam under separability, so neither statement formally subsumes the other.
artifacts:
  - research/artifacts/gkmp-2603-24502-verified.md
---

ESTABLISHED (literature import; verified from arXiv:2603.24502v5, D. Gao,
S. Kunnawalkam Elayavalli, A. Manzoor, G. Patchell, *A new source of purely
finite matricial fields*, 25--26 Mar 2026).

**Theorem 1.1.**  Let `G` be an MF group, `H < G` a **separable** subgroup
(`H = intersection_i H_i` with each `H_i` of finite index in `G`), and `L` a
residually finite MF group such that `G` or `L` is exact.  Then the
amalgamated free product

```text
G *_H (H x L)
```

is MF.  (The same statement holds for PMF and for PFF.)

**Corollary 1.2.**  If `G` is MF and `H < G` is separable, the group double
`G *_H G` is MF.

The proof is by a `C*`-free-independence / selflessness argument in
matrix ultraproducts (after Ozawa), not by finite quotients; exactness is a
stated hypothesis and enters through the tensor step `H x L`.  The paper
does not prove that this hypothesis is logically necessary.  Applications in the
paper: arbitrary graph products of exact residually finite MF groups are MF
(generalizing Magee--Thomas); fundamental groups of closed hyperbolic
`3`-manifolds and all virtually special groups are PFF.

**Trust surface.**  Abstract, introduction, Theorem 1.1, Corollaries
1.2--1.4 read this session from the arXiv HTML; transcription in the
artifact.  The internal proof (Sections 2--6) is not re-derived here.

## Exact scope for the compiler

At `L = Z`, Theorem 1.1 says that the central HNN extension
`<G,t | [t,h]=1, h in H>` is MF when `G` is MF and `H` is separable in `G`;
the second factor `Z` is residually finite, MF, and exact.  This is directly
relevant to the compiler's **outer detector** edge.

It does not settle the full positive branch.  The actual compiler in
`Higman/InjectedCompilerTower.lean` has a finite `tau_j` family followed by
the `d` and `sigma` basis-to-basis HNN edges before the central detector is
attached.  These are HNN extensions along nontrivial isomorphisms of free
subgroups, not product-amalgams.  GKMP proves neither their MF permanence nor
separability of the final transported detector subgroup in the completed
inner tower.  The paper itself cites separate work on HNN extensions as "in
preparation"; no HNN theorem occurs in Theorem 1.1.

Consequently the imported theorem reopens a useful product-edge route and
can close the last central edge under separability, but it does not supersede
the open free-edge wall in
[[fp-mf-completeness-wall-is-route-independent]] or establish finite-
presentation MF-completeness.
