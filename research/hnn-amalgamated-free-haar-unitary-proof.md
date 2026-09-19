---
rg: 2
id: hnn-amalgamated-free-haar-unitary-proof
kind: route
title: Britton normal form is amalgamated freeness; Voiculescu uniqueness of the amalgamated free product closes the converse
target: hnn-hyperlinearity-is-amalgamated-free-haar-unitary
requires: []
---

Notation as in the claim: `B = L(C) subset N = L(A)`, `G = A *_C (C x Z)`,
`L(G) = N *_B (B (x) L(Z))`.

**The HNN group factor is the amalgamated free product.**  `G` is the
amalgamated free product of groups `A *_C (C x <t>)`, and for group
amalgams the group von Neumann algebra is the tracial amalgamated free
product of the group factors over the common subgroup factor:
`L(A *_C D) = L(A) *_(L(C)) L(D)` with respect to the canonical
conditional expectations.  This is the von Neumann version of Britton's
lemma: a reduced word `x_1 y_1 ... x_m y_m` with `x_i in L(A) (-) L(C)`
and `y_i in L(D) (-) L(C)` is supported on group elements with reduced
length `>= 1` in the amalgam, so its `L(C)`-conditional expectation (the
projection of its coefficient function onto `C`) vanishes.  Here
`D = C x Z` and `L(D) = B (x) L(Z)`.

**(1) implies (2).**  Let `Phi : L(G) -> M` extend `iota`, and put
`k = Phi(u_t)`.  Then `k` is a unitary commuting with `Phi(B) = B`, and
`E_B(k^n) = Phi(E_(L(C))(u_t^n)) = 0` for `n != 0` because the
conditional expectation onto a subgroup factor kills group elements
outside the subgroup and trace-preserving embeddings intertwine
conditional expectations onto corresponding subalgebras.  Amalgamated
freeness of `N` and `W^*(B, k) = Phi(B (x) L(Z))` over `B` is the image
under `Phi` of the freeness inside `L(G)`.

**(2) implies (1).**  By Voiculescu's construction and uniqueness of the
amalgamated free product (Voiculescu, *Symmetries of some reduced free
product C*-algebras*, 1985; Voiculescu--Dykema--Nica, *Free random
variables*, Ch. 3), the joint distribution with respect to `tau` of two
subalgebras containing `B` that are free with amalgamation over `B` is
determined by their `B`-valued distributions.  Since `W^*(B, k) = B (x)
W^*(k)` with `k` Haar and `E_B(b k^n) = b tau(k^n)`, the `B`-valued
distribution of `W^*(B, k)` is that of `B (x) L(Z)`, and the `B`-valued
distribution of `N` is its own.  Hence `W^*(N, k) subset M` is
trace-preservingly isomorphic to `N *_B (B (x) L(Z)) = L(G)` by an
isomorphism sending `N` identically and `u_t` to `k`, which is the
required extension of `iota`.

**The hyperlinearity statement.**  `G` is hyperlinear iff `L(G)` embeds
trace-preservingly into a matrix ultraproduct (Radulescu); any such
embedding restricts to an embedding `iota` of `N` satisfying `(1)`.

**The hierarchy.**  Let `k` be as in `(2)` and `h in A - C`, so
`E_B(u_h) = 0`.  The word `k u_h k^* u_h^*` alternates between
`W^*(B,k) (-) B` (the letters `k`, `k^*`, since `E_B(k^(+-1)) = 0`) and
`N (-) B` (the letters `u_h`, `u_h^*`), so by amalgamated freeness its
`B`-expectation, hence its trace, is `0`.  Therefore `[k, u_h] != 1`
(`k` is a leak, contradicting `(RCC)`), and `[k, u_h]` is not a scalar
(a scalar commutator has trace of modulus `1`, contradicting projective
transfer).  This proves both implications in the hierarchy.

**Popa's theorem.**  The statement quoted in the claim is the main theorem
of arXiv:1308.3982 (abstract, verified 2026-08-21); its amenability
hypothesis on `B` is explicit.  The Brown--Dykema--Jung permanence cited is
Corollary 4.5 of arXiv:math/0609080, as already used by
`amenable-edge-hnn-hyperlinear-permanence-proof`.
