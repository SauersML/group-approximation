---
rg: 2
id: o2-free-circle-halving-homotopy
kind: claim
title: In O_2 * C(T) the free unitary is homotopic to its halving
distinct_from:
  trivial-unit-class-lxi-iff-universal-halving-homotopy: that claim proves equivalences among three statements; this is the universal statement itself, still open.
artifacts:
  - research/artifacts/lxi-halving-homotopy-and-extensions-2026-09-12.md
---

In the full unital free product `U = O_2 *_C C(T)`, with Cuntz generators `s_1, s_2` and free unitary `z`,
the unitaries `z` and `s_1 z s_1^* + s_2 s_2^*` lie in the same path component of `U(U)`.

By `trivial-unit-class-lxi-iff-universal-halving-homotopy` this is equivalent to K1-injectivity of
`O_2 * O_2`, and to K1-injectivity of every properly infinite unital algebra with trivial unit class.
It follows from STW Problem LXI (route `o2-free-circle-halving-homotopy-from-lxi`).

## Attempts

- Eckmann--Hilton: on `π_0(U(A))` the Θ-sum and multiplication satisfy interchange, orthogonal halvings
  commute, and the two halvings are rotation-homotopic. The claim is exactly the unit axiom for the
  Θ-sum, and nothing in that structure forces it.
- Paths through isometries from `1` to `s_1` do not exist in norm, because `1 - tt^*` cannot jump. Any
  homotopy must pass through unitaries not of the form `C_t(z)`.
- The BRR commutator criterion needs a projection `p` with `p` and `1-p` properly infinite and full and
  `||[z^*C(z), p]|| < 1`. The `stw61-*` maximal-commutator theorems in the Toeplitz free-product model
  indicate that such projections are not available from explicit mixed families. No obstruction to the
  homotopy itself is known.
