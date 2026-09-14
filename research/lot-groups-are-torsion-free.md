---
rg: 2
id: lot-groups-are-torsion-free
kind: claim
title: Every LOT group is torsion-free
distinct_from:
  lot-complexes-with-vanishing-first-l2-betti-are-aspherical: that proves asphericity of a LOT complex from vanishing first L2-Betti number of its group; this is the open, weaker statement that the group never has torsion.
  contractible-2-complex-minus-a-cell-is-aspherical: that is the one-cell case of Whitehead's conjecture, which contains asphericity of every LOT complex and so implies this; this asks only for torsion-freeness of LOT groups.
  balanced-kervaire-failure-refutes-stable-ac-or-lot-torsion-free: that is the implication showing why this matters for Kervaire--Laudenbach; this is the open group-theoretic input.
artifacts:
  - research/artifacts/ideas-bridges-2-2026-09-14.md
---

**OPEN.** For every labelled oriented tree `Gamma`, the LOT group
`G(Gamma) = < V | iota(e) lambda(e) tau(e)^-1 lambda(e)^-1 (e an edge of Gamma) >`
(notation of `lot-complexes-with-vanishing-first-l2-betti-are-aspherical`) has no
nontrivial element of finite order.

**Status at source.** A. N. Barreto and E. G. Minian, *Local indicability of
groups with homology circle presentations*, arXiv:2308.07447v1, p. 2, verbatim:
"Local indicability of LOT groups is an open problem (that would imply asphericity
of the associated presentations). In fact, it is not even known whether all LOT
groups are torsion-free."

**Implied by.**
- Asphericity of every LOT complex. A finite aspherical 2-complex has a
  torsion-free fundamental group.
- Local indicability of every LOT group.
- Known local indicability cases (not re-read here beyond the abstract and
  introduction of Barreto--Minian and of M. A. Cerdeiro, *A class of locally
  indicable LOT groups*): LOTs whose Howie graphs `I(Gamma)` or `T(Gamma)` have
  at most one cycle (Barreto--Minian, Corollary 3.1), and LOTs of diameter at
  most 3 (Howie, as quoted there).

**Implies.** With `stable-andrews-curtis-conjecture`, the killing form of
Kervaire--Laudenbach over nonnegative deficiency, through the route
`kervaire-killing-form-via-stable-ac-and-torsion-free-lots`.
