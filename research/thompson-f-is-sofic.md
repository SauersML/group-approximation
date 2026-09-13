---
rg: 2
id: thompson-f-is-sofic
kind: claim
title: Thompson's group F is sofic
refuted_by:
  - thompson-f-is-not-sofic
distinct_from:
  thompson-f-is-amenable: that is amenability, which implies this claim; a nonamenable F could still be sofic.
  thompson-v-is-sofic: that is soficity of V, which implies this claim because F <= V; the converse is not known.
---

**OPEN.** Thompson's group `F` embeds in the universal sofic group.

**Equivalent forms** (`thompson-f-sofic-iff-relator-system-unstable`):
- some almost-homomorphism of `F` has a fixed-point character with a regular component;
- there are `epsilon > 0` and permutation pairs `(A_n, B_n)` that satisfy both relators of `F` up to
  `delta_n -> 0` in normalized Hamming distance while `d(A_n B_n, B_n A_n) >= epsilon`.

Exact solutions commute, since finite quotients of `F` are abelian. So the second form must exploit the
error.
