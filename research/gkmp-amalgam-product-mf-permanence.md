---
rg: 2
id: gkmp-amalgam-product-mf-permanence
kind: claim
title: Gao-Kunnawalkam-Manzoor-Patchell MF permanence for product-amalgams with a separable edge
distinct_from:
  shulman-amalgam-mf-criterion: that gives a necessary-and-sufficient corona-embedding condition for a general amalgam; this is a checkable sufficient condition, requiring only that the edge subgroup be separable and one side residually finite, and it is the tool that handles the asymmetric product edge Shulman's symmetric theorem cannot.
  twisted-rope-edge-is-mf-under-relative-profinite-compatibility: that is this repository's bespoke finite-quotient theorem for one product edge; this is the published general theorem, proved by C*-free-independence / selflessness methods, and it is strictly stronger.
artifacts:
  - research/artifacts/gkmp-2603-24502-verified.md
---

ESTABLISHED (literature import; verified from arXiv:2603.24502v2, D. Gao,
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
matrix ultraproducts (after Ozawa), not by finite quotients; exactness is
essential and enters through the tensor step `H x L`.  Applications in the
paper: arbitrary graph products of exact residually finite MF groups are MF
(generalizing Magee--Thomas); fundamental groups of closed hyperbolic
`3`-manifolds and all virtually special groups are PFF.

**Trust surface.**  Abstract, introduction, Theorem 1.1, Corollaries
1.2--1.4 read this session from the arXiv HTML; transcription in the
artifact.  The internal proof (Sections 2--6) is not re-derived here.

## Why it is the missing permanence tool

The finite-presentation MF-completeness wall
([[fp-mf-completeness-wall-is-route-independent]]) is a product-edge
permanence question `Gamma *_S (S x Q)` that no finite-quotient method
settles ([[twisted-edge-over-amalgamated-product-base-is-mf]] only handles
the profinitely-compatible case).  Theorem 1.1 is exactly a permanence
theorem for `G *_H (H x L)`, i.e. for that product edge, with a checkable
hypothesis (`H` separable, one side exact) in place of profinite
compatibility.  It therefore directly targets the wall and supersedes the
pessimistic reading in
[[digit-edge-mf-is-a-free-entropy-model-uniqueness-question]]: the
free-entropy obstruction rules out a *soft distribution-matching* proof, but
Theorem 1.1 is a *hard* theorem that goes through anyway by free
independence, so the completeness is **not** known to be open in the
negative direction after all.
