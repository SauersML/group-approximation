---
rg: 2
id: synchronous-cores-in-out-v-have-order-at-most-two
kind: claim
title: An element of Out(V) whose core transducer is synchronous is trivial or the bit flip, so every element of order at least three is asynchronous
distinct_from:
  v-normalizer-rsgs-contract-iff-finite-outer-order: that shows V ⋊ ⟨t⟩ is non-contracting for t of infinite outer order; this shows its local actions are then not tree automorphisms, so Scott's theorem on Röver--Nekrashevych groups does not apply to its full closure through that structure.
  out-v-contains-the-root-problem-for-the-full-2-shift: that identifies the Lipschitz part L_2 with the inert shift automorphisms; this concerns the smaller synchronous part, which has order at most two.
artifacts:
  - research/artifacts/gq-gq-infinite-primes-out-v-reading.md
---

**ESTABLISHED** through `synchronous-cores-in-out-v-have-order-at-most-two-proof`. Lane proof
(bh-higman-classic), elementary modulo Hedlund's theorem, not independently reviewed. Hedlund
was not read at source; the reading notes record that Bleak--Cameron--Olukoya
(arXiv:2004.08478) reprove `Aut(X_2^N, σ_2) ≅ C_2`. No priority claimed; the statement is
close to the one-sided part of BCO.

## Statement

Call a transducer *synchronous* if every transition outputs exactly one letter. Let
`t ∈ N(V)`, and suppose the core of `t` (its element of `O_2 ≅ Out(V)`) is synchronous.
Then that core is the one-state identity or the one-state bit flip `c`. So the class of `t`
in `Out(V)` has order at most 2.

## Consequence

If `t ∈ N(V)` has order at least 3 in `Out(V)`, then the local actions of `t` at long paths
(its core states) are not automorphisms of the binary tree, since some transition outputs
a word of length other than 1. So `[[V ⋊ ⟨t⟩]]` is not, through this structure, the
Röver--Nekrashevych group `V_2(H)` of a self-similar group `H` of tree automorphisms. Scott's
theorem (fp self-similar `H` ⇒ fp `V_2(H)`), which motivates Question 1.4 in BBMZ, and its
Skipper--Witzel--Zaremsky extension therefore do not apply to it directly. Whether
`[[V ⋊ ⟨t⟩]]` is abstractly isomorphic to some Röver--Nekrashevych group is not addressed.
