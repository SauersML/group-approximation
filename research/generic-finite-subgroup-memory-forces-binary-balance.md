---
rg: 2
id: generic-finite-subgroup-memory-forces-binary-balance
kind: claim
title: An injective binary automaton whose memory contains a generically placed finite subgroup has a balanced rule
distinct_from:
  three-address-binary-injective-rules-are-balanced: that treats memory size three, where an involution is forced and the placement condition is checked outright; this treats any finite subgroup inside a memory of any size under two explicit coset and privacy conditions.
  invariant-output-automata-have-only-nonlinear-decoders: that concerns outputs invariant under a finite subgroup acting on the memory; this concerns a finite subgroup contained in the memory, with no symmetry of the output assumed.
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `generic-finite-subgroup-memory-forces-binary-balance-proof`.

Let `G` be a group and `tau` an injective automaton on `{0,1}^G` with memory `M`. Suppose `M`
contains a finite subgroup `K` with `|K| >= 2`, placed generically:
- **(G1)** distinct elements of `M \ K` lie in distinct left cosets `mK` and in distinct right
  cosets `Km`;
- **(G2)** the blocks outside `K` that read `K` have context sites that are pairwise disjoint and
  disjoint from `K(M \ K)`.

Then the rule of `tau` is balanced.

**Why.**
- By (G1), each outside block reads `K` at exactly one address, and the blocks in `K` have private
  contexts.
- An unbalanced binary rule has an insensitive context at every address. So a perturbation on `K`
  can be hidden from every outside block.
- Injectivity then makes the map `u -> (mu((u(hk))_k, r_h))_(h in K)` a bijection of `{0,1}^K` for
  every choice of contexts. That balances `mu` on every `K`-slice.

**For design.** Hosts such as `R^x` and `V` are full of finite subgroups. A biased binary design can
use such a subgroup in its memory only through coincidences that break (G1) or (G2).

Artifact, Section 3, Proposition 9.
