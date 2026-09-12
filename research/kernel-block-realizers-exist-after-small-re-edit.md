---
rg: 2
id: kernel-block-realizers-exist-after-small-re-edit
kind: claim
title: Every sofic approximation of an extension by a Kazhdan kernel with sofic-invisible quotient can be re-edited so that every element has blockwise inner realizers
distinct_from:
  kernel-block-realizers-need-no-centralizer-factor: that removes the centralizer factor from realizers when they exist; this shows they always exist after an o(|X_n|) re-edit of an enlarged generating set, so their existence is no restriction.
  leavitt-cover-regular-realizer-models-iff-residually-finite: that shows realized approximations with regular kernel blocks exist exactly when the cover is residually finite; this produces realized approximations with alternating block groups from any sofic approximation.
  kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient: that shows the ambient group preserves the kernel's blocks; this uses that invariance to realize every element inside alternating block groups.
  bounded-blockwise-inner-realizers-fail-off-kernel: that excludes realizers of bounded length; this shows unbounded realizers exist in every sofic approximation after re-editing.
---

**ESTABLISHED.** Let `1 -> N -> G -> Q -> 1` be exact with `G` countable, `N`
infinite and Kazhdan with finite symmetric generating set `S`, and every
homomorphism `Q -> S_U` trivial. Let `sigma_n : G -> Sym(X_n)` be any sofic
approximation along `U`. Then there are:

- a finite symmetric generating set `S+ ⊇ S` of `N`;
- permutations `s~` of `X_n` for `s in S+`, each agreeing with `sigma_n(s)` off
  `o(|X_n|)` points, whose `S+`-graph is a disjoint union of blocks `B` with a
  uniform Cheeger constant;

such that, along `U`:

1. **Alternating block groups.** The blocks with
   `Pi+_B = <s~|_B : s in S+> >= Alt(B)` carry all but `o(|X_n|)` points.
2. **Every element is realized.** For every `g in G` there are block-preserving
   permutations `p_n`, acting on each block by an element of `Pi+_B`, with
   `sigma_n(g) = p_n` off `o(|X_n|)` points. In the notation of
   `kernel-block-realizers-need-no-centralizer-factor`, `sigma(G) <= Pi+`, with
   trivial centralizer factors.

The approximation `sigma_n` is not changed, only the edited kernel generators
and the generating set they are read on.

Derivation: `kernel-block-realizers-re-edit-proof`.

**Consequence.** Blockwise inner realizers of unbounded length add no
information to a sofic approximation. A contradiction derived from "`sigma_n`
is a sofic approximation whose elements are realized on the kernel blocks" is a
contradiction derived from `sigma_n` alone. For the Leavitt cover
(`hyperbolic-kazhdan-cover-of-leavitt-unit-group`, quotient with only trivial
sofic morphisms by `leavitt-unit-group-has-only-trivial-sofic-morphisms`), the
realized regime is populated iff the cover is sofic. So the unbounded case of
the realizer hinge on `relative-normalization-modulo-kazhdan-kernel` is exactly
the whole question.

**Scope.** It uses Kun's blocks, block invariance and Jordan's theorem. Property
(T) of `G` is not used and nothing about soficity follows. Realizer words here
are long: by `inner-realizers-are-at-least-half-the-sofic-radius` they are at
least half the sofic radius.
