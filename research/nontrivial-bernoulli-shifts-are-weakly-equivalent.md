---
rg: 2
id: nontrivial-bernoulli-shifts-are-weakly-equivalent
kind: claim
title: Any two nontrivial finite-alphabet Bernoulli shifts over a countably infinite group are weakly equivalent
distinct_from:
  fpbs-aw-finite-pattern-input: that is the finitary label-selector form of Abert-Weiss Theorem 1, worded for a Bernoulli parameter; this is the consequence that Bernoulli shifts with different bases, including bases of arbitrarily small entropy, are weakly equivalent to each other.
  fpbs-bernoulli-maximal-cost: that says a Bernoulli action attains the maximal cost; this is weak equivalence of all nontrivial Bernoulli shifts, which makes every weak-equivalence invariant, cost included, blind to the base.
artifacts:
  - research/artifacts/weak-invariant-blindness-for-bernoulli-rokhlin-entropy-2026-09-12.md
---

**ESTABLISHED.** Let `G` be countably infinite. Any two Bernoulli shifts `G ↷ (k^G, λ^G)` and
`G ↷ (k'^G, λ'^G)` with finite alphabets and non-point-mass base measures are weakly equivalent in
Kechris's sense.

Proof: Lemma 1.1 and Proposition 2.2 of the artifact. Nontrivial Bernoulli shifts are free.
Abért–Weiss, Theorem 1 (arXiv:1103.1063v2, quoted verbatim in
`nontrivial-bernoulli-weak-equivalence-proof`), puts every Bernoulli action weakly inside every free
action. Theorem 1 itself records the case of free factors of i.i.d. processes; this node is the case
of Bernoulli shifts, with freeness proved.
