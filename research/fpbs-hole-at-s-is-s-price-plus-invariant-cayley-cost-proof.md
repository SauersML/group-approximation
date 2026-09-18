---
rg: 2
id: fpbs-hole-at-s-is-s-price-plus-invariant-cayley-cost-proof
kind: route
title: Approximate by conjugates, back up unconnected generator edges, read subgraphings as invariant percolations, and squeeze with the Gaboriau bound
target: fpbs-hole-at-s-is-s-price-plus-invariant-cayley-cost
requires:
  - burton-kechris-cost-usc-and-maximum-action
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - fpbs-cost-is-limit-of-cayley-subgraphing-costs
  - fpbs-graphing-cost-betti-cycle-dimension-identity
  - fpbs-invariant-cayley-cost-literature-status
artifacts:
  - research/artifacts/fpbs-fixed-s-price-split-2026-09-17.md
---

Written derivation, Sections 1–4 of the artifact.

1. **(H1).**
   - Given a generating subgraphing of `Phi_S^a` with sets `A_t`, let `D_t^N` be the set of points not joined to
     their `t`-neighbour by an `E`-path of length `<= N`. It is a finite Boolean combination of translates of the
     `A_u`, and `mu(D_t^N(a)) -> 0`.
   - Burton–Kechris Theorem 2.3 gives conjugates `c_n` of `a'` converging weakly to `a`. There, keep the edges from
     `A_u` and back up the `t`-edges at `D_t^N(c_n)`.
   - The result generates, and its cost tends to `c + sum_t mu(D_t^N(a))`.
   - `a ≼ a_inf` is maximality, and `b ≼ a` is Abért–Weiss.
2. **(H2).**
   - A generating subgraphing, read at the root, is an invariant connected spanning subgraph with the same expected
     degree.
   - Conversely, an invariant connected spanning subgraph joined with iid gives a free action whose root-edge sets form
     a generating subgraphing.
   - Then apply (H1).
3. **(H3).**
   - `1 + beta_1 <= C(a) <= C_sub^a(S)` by the cost–Betti identity.
   - (G) of `fpbs-cost-is-limit-of-cayley-subgraphing-costs` turns the hole into `C_sub^b(S) = 1 + beta_1`.
   - That value squeezes every `C_sub^a(S)` by (H1), and (H2) identifies `c_inv(S)`.
   - Burton–Kechris Theorem 7.1 (`C(a_inf) = cost(Gamma)`) gives the Beringer–Pete–Timár consequence.
4. **(H4).** `fpbs-invariant-cayley-cost-literature-status` gives `c_inv(S) = 1`. With `1 + beta_1 <= c_inv(S)`, this
   forces `beta_1 = 0`, so (P2) holds.

This is dependency bookkeeping over a written deduction, not a formal verification.
