---
rg: 2
id: rokhlin-entropy-is-the-largest-partition-bounded-invariant
kind: claim
title: Rokhlin entropy is the largest isomorphism invariant bounded by the Shannon entropy of every generating partition
distinct_from:
  bernoulli-rokhlin-entropy-maximal-for-every-group: that is the open lower bound for Bernoulli Rokhlin entropy; this proves every partition-bounded invariant is at most Rokhlin entropy, so saturating any such invariant on Bernoulli shifts already proves that lower bound.
  strict-automaton-lowers-bernoulli-rokhlin-entropy: that converts a strict automaton into small generating partitions of amplified Bernoulli shifts; this shows no other partition-bounded invariant offers an easier lower bound to combine with that deficit.
artifacts:
  - research/artifacts/conjugacy-invariants-and-partition-bounds-2026-09-12.md
---

Call an isomorphism invariant `I` of ergodic measure-preserving actions of a countable group `G`
*partition-bounded* when `I(G ↷ (Z, zeta)) <= H_zeta(Q)` for every countable generating partition
`Q`. Then:
1. Rokhlin entropy `h^Rok` is partition-bounded.
2. Every partition-bounded `I` satisfies `I <= h^Rok`.
3. If a partition-bounded invariant attains `log |A|` on the Bernoulli shift `A^G`, then
   `h^Rok(A^G) = log |A|`.

Examples: sofic entropy for a fixed sofic approximation, and the f-invariant over free groups.

**Consequence for Gottschalk.** In every proof architecture that combines a lower bound for a
partition-bounded invariant on amplified Bernoulli shifts with a partition-level deficit forced by
strictness, the lower-bound step implies Bernoulli Rokhlin maximality (INF) on that group. The
deficit step is `strict-automaton-lowers-bernoulli-rokhlin-entropy`. So INF is the unavoidable
target of all such architectures.

The deficit cannot be a comparison of invariants of the image measure:
`measure-conjugacy-invariants-cannot-certify-surjectivity` makes those equal.

Proof: Section 2 of the linked artifact. It is elementary: take the infimum over generating
partitions.
