---
rg: 2
id: amenable-base-makes-mikhailova-edge-co-amenable
kind: claim
title: An amenable base makes the Mikhailova edge co-amenable but non-amenable and non-separable in the product of free groups
distinct_from:
  mikhailova-coset-action-is-two-sided-q-action: that identifies the coset action and gives its soficity for an amenable base; this extracts the sharper fact that the edge is co-amenable, reducing the crux to a co-amenable (not merely sofic) edge.
  centralizing-hnn-sofic-via-regular-edge-centralizer: that records that the edge is non-separable, the residual-finiteness obstruction; this adds that the same edge is co-amenable when the base is amenable, an approximation-friendly property the no-go does not see.
---

ESTABLISHED (unreviewed).  Let `Q` be finitely presented and **amenable**,
`F = F(X)`, `phi : F ->> Q`, and `M = M_Q = {(u,v) : u =_Q v} <= F x F` the
Mikhailova subgroup.  Then, inside `H = F x F`:

- `M` is **co-amenable**: `ell^infinity(H/M)` carries an `H`-invariant mean;
- `M` is **non-amenable**: it contains the diagonal `{(u,u) : u in F} ~= F`, a
  nonabelian free group;
- `M` is **non-separable** whenever `Q` has unsolvable word problem
  (Mikhailova): membership in `M` is undecidable.

So `M` is simultaneously co-amenable, non-amenable, and non-separable in
`F x F` — an explicit such subgroup.

DERIVATION [[amenable-base-mikhailova-co-amenable-proof]].

## Consequence for the compiler crux

*Corrected 2026-09-13 (lane `ex2-free-wreath-amenable-sofic`).*  An earlier
version of this section had three errors. It said "an amenable action is
sofic", which is false ([[amenable-action-of-a-sofic-group-need-not-be-sofic]]).
It called the free lamps "the only remaining gap", although that gap is closed
in the literature. And it read the design as settling the compiler's positive
branch, although the compiler cannot use an amenable base. What is true:

- **The amenable-base rope is sofic.** `H *_M (M x Z) = Z wr^*_(H/M) H`
  ([[centralizer-hnn-is-free-generalized-wreath]]). The action
  `H curvearrowright H/M` factors through the amenable group `Q x Q`, so it is
  sofic (GKP Theorem 2.17 and Proposition 2.15(1)). GKP Theorem 3.7
  ([[gkp-free-generalized-wreath-soficity]]) already covers free lamps. So the
  rope is sofic, and so is its direct-sum companion (GKP Theorem 3.6). The
  same holds for every residually amenable base
  ([[separating-sofic-quotient-sets-make-an-action-sofic]], (C3)).
- **Co-amenability is not the reason.** Co-amenability of an edge does not by
  itself give a sofic coset action. The correct general statement also needs
  the stabilizer's action on the coset space to be sofic
  ([[co-amenable-induction-of-sofic-actions]]).
- **The compiler cannot use this design.** Its Mikhailova base is the Higman
  host `H_e`, which contains a free group on every branch. So the compiler's
  edge is never co-amenable and never has an amenable core quotient
  ([[compiler-rope-edge-is-not-co-amenable]]). There the first rope reduces to
  soficity of the two-sided action of `H_e`, pulled back to a product of free
  groups, and the second, twisted rope is a separate open step.
