---
rg: 2
id: k2-central-in-steinberg-groups-of-leavitt-resolvent-ring
kind: claim
title: For N >= 5 the kernel K_2(N,R_L) of St_N(R_L) -> E_N(R_L) is central
distinct_from:
  one-steinberg-group-contains-every-gl-n-q: that uses centrality of K_2(4,M_m(Q)) over the fields Q, which is classical; this asks for centrality of K_2(N,R_L) over the noncommutative, non-IBN ring R_L itself.
  faithful-pair-finite-steinberg-actions-need-noncentral-k2: that is the implication this hypothesis feeds; this is the hypothesis.
---

**ESTABLISHED** through `k2-central-in-steinberg-groups-via-k2-stability`, which cites item 3 of
`leavitt-resolvent-k2-stability-holds` (lane gq-infinite-primes). That is a lane proof, not independently
reviewed. Let `R_L` be the ring of `leavitt-resolvent-ring-is-fp-and-contains-q`
and let `N >= 5`. Then `K_2(N,R_L) = ker(St_N(R_L) -> E_N(R_L))` is contained in
the centre of `St_N(R_L)`.

## What is known

- **Stably, yes.** For every ring the stable `K_2(R)` is central in `St(R)`
  (Kervaire; Milnor, *Introduction to Algebraic K-Theory*, Theorem 5.1, recalled,
  not re-read).
- **Unstable criteria in the graph do not apply.** The input cited in
  `one-steinberg-group-contains-every-gl-n-q` is Voronetsky, arXiv:2004.08551.
  Its criterion is "central if n >= sr(A) + 2". No finite bound on the stable
  rank of `R_L` is recorded here. `R_L` fails IBN: `R_L ≅ R_L^2` through its
  Leavitt pair. The commutative and module-finite centrality theorems are not
  known here to cover `R_L`.

## Sufficient conditions

- **Injective stability.** Suppose the stabilization map
  `St_N(R_L) -> St(R_L)` is injective. Then `K_2(N,R_L)` maps into the central
  subgroup `K_2(R_L)`. Its elements then commute with the image of `St_N(R_L)`,
  so by injectivity they commute in `St_N(R_L)`.
- **A matrix-ring shift.** The Leavitt pair gives a ring isomorphism
  `R_L ≅ M_2(R_L)`, and hence `St_N(R_L) ≅ St_N(M_2(R_L))`. Comparing this with
  the block map to `St_(2N)(R_L)` is one possible route to injective stability.
  It has not been attempted.

## Consequence

With `faithful-pair-finite-steinberg-actions-need-noncentral-k2`, this claim
gives `steinberg-leavitt-resolvent-groups-have-no-type-a-action`.

## Attempts

- **2026-09-18 (lane gq-infinite-primes): proved, subject to review.** `leavitt-resolvent-k2-stability-holds`,
  item 3. For every `N >= 3`, `K_2(N, R_L) = j(K_2(N-1, R_L))` is central (by padded centrality and the refinement
  isomorphisms), and `K_2(N, R_L) ≅ Q^x`.
