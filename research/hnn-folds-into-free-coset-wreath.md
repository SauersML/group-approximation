---
rg: 2
id: hnn-folds-into-free-coset-wreath
kind: claim
title: An HNN extension embeds in the free coset wreath product of any base-injective quotient
distinct_from:
  sl2-centralizer-hnn-is-free-coset-wreath: that is an isomorphism for one centralizer HNN, where the associated map is the identity; this is an embedding for an arbitrary associated isomorphism, through any quotient injective on the base.
  sofic-coset-action-makes-amalgam-double-sofic: that folds a symmetric amalgamated double onto its vertex group; this folds an HNN extension with arbitrary associated isomorphism into a quotient, and has a local form.
artifacts:
  - research/artifacts/hnn-fold-free-coset-wreath-2026-09-11.md
---

ESTABLISHED (written proof). Let `G = <B, t | t^(-1) c t = phi(c), c in C>`
and let `rho: G -> H` be a homomorphism. With `X = H/rho(C)` and `o = rho(C)`,

    Phi(b) = rho(b),     Phi(t) = z_o rho(t)

defines a homomorphism `G -> Z wr^*_(H action X) H = (*_(x in X) <z_x>) rtimes H`.
It is injective whenever `rho` is injective on `B`.

The image of a reduced form `b_0 t^(e_1) ... t^(e_k) b_k` is a freely reduced
word of length `k` in the `z_x` times `rho(g)`. There is a local form: `Phi` is
injective on a finite set once `rho` keeps its finitely many inner syllables
out of `rho(C)` or `rho(C')`, as appropriate, and keeps its single-syllable
elements nontrivial.

**Corollary.** If for every finite subset of `G` there is such a `rho` into a
sofic group `H` whose coset action `H action H/rho(C)` is sofic, then `G` is
sofic.
