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

By [[centralizer-hnn-is-free-generalized-wreath]] the compiler's inner rope is
the centralizing HNN `H *_M (M x Z) = Z wr^*_(H/M) H`.  With an amenable
Mikhailova base ([[mikhailova-coset-action-is-two-sided-q-action]]) the edge
`M` is co-amenable in `H`, i.e. the coset action `H curvearrowright H/M` is an
**amenable action**, and the lamps of the wreath are indexed by an amenable
`H`-set.  This is exactly the setting in which Følner sets exist in the lamp
index space `X = H/M`:

- for **abelian (direct-sum) lamps** it already gives soficity via the
  Gao--Kunnawalkam Elayavalli--Patchell wreath theorem (an amenable action is
  sofic), so `(bigoplus_(H/M) Z) x| H` is sofic;
- the **free lamps** of the actual rope (`(*_(H/M) Z) x| H`) are the only
  remaining gap: keeping the free-lamp syllables unreduced in the finite
  models is the sofic analogue of Ueda's reduced HNN normal form
  ([[centralizing-hnn-perturbed-edge-separation]]).

Thus, once the base is chosen amenable, the compiler's positive branch is not
"soficity over a non-amenable non-separable edge" but "soficity of a free-lamp
wreath over an amenable coset action" — a strictly cleaner target, with the
non-amenability and non-separability of `M` no longer able to obstruct the
approximation (they obstruct only residual finiteness).
