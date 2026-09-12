---
rg: 2
id: fpbs-priority-composite-fixed-price
kind: claim
title: Fixed price one for composite-order profiles with divergent detour sums
root: true
---

**Statement.** Choose any integers n_i>=13 for i>=1 with sum_i t^(n_i-1) = infinity for every t in
(0,1), and put G_n = <a,b | (a b^i)^(n_i)=1, i>=1>. Theorem 5.1 of the finite-priority note: every
free p.m.p. action of G_n has cost one. No primality and no pairwise coprimality of the n_i is needed,
which is what distinguishes this from the prime-order family. Section 5.5 gives the accounting: keep
T_b on all of X at cost one, and for each finite k and eta>0 the disjoint supports of sizes n_i-1
supply a restriction T_a|U with

    C({T_b, T_a|U}) <= 1 + integral_0^1 product_{i<=k} (1-t^(n_i-1)) dt + eta.

The divergence hypothesis drives the product to zero pointwise, dominated convergence kills the
integral, and the infinite-class lower bound gives equality. No ergodicity assumption and no Bernoulli
extension is used.

**Proof location.** `research/artifacts/fpbs/finite-priority.md`, Sections 5.1 through 5.5;
response 42.

**Imported inputs.** Gruber-Sisto, arXiv:1408.4488v3, Lemmas 2.15 and 2.17, for the isometric convex
embedding of the labelled relator circles and the connectedness of their intersections, which is what
replaces the prime-order argument for exact orders and trivial intersections. Sapir, arXiv:1012.1325v4,
Theorem 3.7. Gaboriau, arXiv:1011.2294v1. All three identifiers resolve.

**Finite-replay evidence.** `research/artifacts/fpbs/finite-priority-checks.json` via
`scripts/replay_priority.py`: 51,532 exact assertions, 25,984 finite-priority cases over the regular
S_3 action with all 203 partitions, ties included, and 33,882 deleted-edge instances. The file has no
top-level status field; `finite-priority-audit.json` records the same total as passing.

**Evidence level.** Written deduction with named published inputs and a passing finite replay of the
priority-deletion accounting. Not refereed, not formally verified. Its audit records that prior broad
claims are retained as provenance and not independently revalidated, so this result does not inherit
their risk.

The status records a written deduction or cited input, not independent mathematical verification.
