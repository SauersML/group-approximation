---
rg: 2
id: o2-free-range-projection-homotopy-iff-halving
kind: claim
title: The halving homotopy in O_2 * C(T) is equivalent to a homotopy between the range projections of two free copies of O_2
distinct_from:
  trivial-unit-class-lxi-iff-universal-halving-homotopy: that claim proves the unitary forms (K1-injectivity of O_2 * O_2, the [1] = 0 case of LXI, the halving homotopy); this one adds the projection and C([0,1])-algebra forms and the structure of the halving map on the component group.
  o2-free-circle-halving-homotopy: that is the open homotopy statement itself; this is an established equivalence that does not decide it.
artifacts:
  - research/artifacts/k1-halving-projection-form-2026-09-13.md
---

Let `U = O_2 *_C C(T)`, with Cuntz generators `s_1, s_2` and free unitary `z`, and `D = O_2 *_C O_2`,
with inclusions `iota_1, iota_2`. The following are equivalent.

1. `U` is K1-injective. Equivalently, every unital properly infinite algebra with `[1] = 0` is.
2. `s_1 s_1^* ~_h z s_1 s_1^* z^*` in `U`. Equivalently, `iota_1(s_1s_1^*) ~_h iota_2(s_1s_1^*)` in `D`.
3. Some projections `p, q in O_2`, both different from 0 and 1, satisfy `iota_1(p) ~_h iota_2(q)` in `D`.
4. The C([0,1])-algebra `{f in C([0,1], D) : f(0) in iota_1(O_2), f(1) in iota_2(O_2)}` has a projection
   other than 0 and 1.

These are the `[1] = 0` analogues of Blanchard--Rohde--Rordam (arXiv:0704.1554) Proposition 4.3 and
Theorem 5.5 (iv), (v), with `O_2` in place of `O_infty`.

Two structural facts come with the equivalence.
- Let A be unital with a Cuntz pair, and `G = U(A)/U^0(A)`. The halving map `phi[w] = [s_1 w s_1^* + s_2s_2^*]`
  is an idempotent endomorphism of G. Its kernel is `N = ker(G -> K_1(A))`, and its image is isomorphic to
  `K_1(A)`. So `G = N ⋊ K_1(A)`, and A is K1-injective iff `phi = id`.
- The O_2 analogue of BRR Proposition 5.4 is false. The unital embeddings `s_k -> s_k` and `s_k -> z s_k z^*`
  of `O_2` into `U` are not homotopic, because their relating unitary `z rho(z^*)` has class `-[z] ≠ 0` in
  `K_1(U) = Z`. So a proof of the halving homotopy has to move range projections. It cannot go through
  homotopies of `O_2` embeddings.
