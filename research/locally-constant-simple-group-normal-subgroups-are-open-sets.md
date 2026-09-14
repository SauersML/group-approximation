---
rg: 2
id: locally-constant-simple-group-normal-subgroups-are-open-sets
kind: claim
title: Every normal subgroup of LC(Z,Q), for a Cantor space Z and a finite nonabelian simple group Q, is the group of functions supported in one open set
artifacts:
  - research/artifacts/sk-rigidity-intrinsic-reconstruction-2026-09-13-part1.md
---

Let `Z` be a Cantor space and `Q` a finite nonabelian simple group, and let `LC(Z,Q)` be the group of locally constant
maps `Z → Q` under pointwise multiplication. For `f ∈ LC(Z,Q)` put `supp f = {z : f(z) ≠ 1}`, which is clopen. For
open `O ⊆ Z` put `N_O = {f : supp f ⊆ O}`.

1. Every normal subgroup of `LC(Z,Q)` equals `N_O` for exactly one open set `O`.
2. The maximal normal subgroups are the groups `N_(Z∖{z})`, `z ∈ Z`. The hull–kernel topology on this set, with basic
   open sets `{N : M ⊄ N}` for normal `M`, is the topology of `Z`.
3. So every group isomorphism `α: LC(Z,Q) → LC(Z',Q')` is induced by a homeomorphism `h: Z → Z'` in the sense that
   `α(N_O) = N_(h(O))` for every open `O`.

Use: the space `X` is recovered from the diagonal subgroup `GL_3(LC(X,F_2)) = LC(X, GL_3(F_2))` of the elementary
group of a subshift crossed product (`subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`).

Credit: folklore level. No source was located; the check was only a grep of main.
