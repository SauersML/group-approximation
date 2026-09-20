---
rg: 2
id: fpbs-uniform-kesten-law-from-uniform-l2
kind: route
title: The uniform l2 conjecture on X_(k,eta) gives the uniform Kesten law through derived-series towers of the kernel
target: fpbs-uniform-kesten-law-residually-amenable-pairs
requires: [fpbs-uniform-l2-gap-marked-groups, fpbs-l2-gap-transfers-to-kesten-normal-gap]
---

SUFFICIENT route.

Let `(M, delta)` be the constants of `fpbs-uniform-l2-gap-marked-groups` at
`(k, eta)`. Let `(Gamma, N)` be a pair as in the target, with tower `(N_j)`.

- By item 2 of `fpbs-l2-gap-transfers-to-kesten-normal-gap`, the marked
  quotients `Gamma/N_j` lie in `X_(k,eta)` for all large `j`.
- The uniform conjecture therefore gives
  `||T^(G_j)_(p_c(G_j)+delta)|| <= M` for all large `j`.
- Item 1 of the same claim, the transfer lemma, gives `chi^N <= M` on
  `[0, p_c(G) + delta]`.

The same argument, restricted to pairs with `w = e` in `Gamma`, derives the
cylinder form of the target from `fpbs-uniform-l2-gap-short-relator-cylinders`.
It uses item (T4) of `fpbs-l2-gap-transfers-to-kesten-normal-gap-proof`.

**Consequence for the graph.** Every route through
`fpbs-uniform-l2-gap-marked-groups` passes through this target. A
counterexample to the target is a counterexample to that route.
