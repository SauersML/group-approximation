---
rg: 2
id: fpbs-sc-fixed-price-family
kind: claim
title: Every free action of the explicit abundance family has cost exactly one
root: true
---

**Statement.** Fix I>=1 and for each i>=I a prime p_i>=13 with sum_{i>=I} q^(p_i-1) = infinity for
every 0<q<1. Put G(p,I) = <a,b | (a b^i)^(p_i)=1, i>=I>. Theorem 1(4) of the small-cancellation note:
in every essentially free p.m.p. action on a standard probability space, and for every epsilon>0,
there is a measurable A with mu(A)<epsilon such that T_b on X together with T_a restricted to A
generate the whole orbit relation. Hence every such action has cost exactly one. The abundance
hypothesis holds whenever p_i = o(log i), so the torsion orders may tend to infinity and the group
need not have bounded exponent.

**Proof location.** `research/artifacts/fpbs/small-cancellation-family.md`, Section 4, using the
finite detour lemma of Section 2 and the algebra of Section 3; response 38.

**Imported inputs.** Sapir, arXiv:1012.1325v4, Theorem 3.7 (Greendlinger lemma, with the symmetrized
relator set treated as a set of distinct words so that proper powers are allowed). Gaboriau,
arXiv:1011.2294v1, for the aperiodic cost lower bound. Both identifiers resolve.

**Finite-replay evidence.** `research/artifacts/fpbs/small-cancellation-checks.json` via
`scripts/replay_small_cancellation.py`; `small-cancellation-audit.json` records 143,311 exact
assertions and 5,440 finite labelings passing. That audit also lists seven infinite steps the replay
does not test, among them all relator lengths and indices, measurable finite partitions, and the cost
infimum limit.

**Evidence level.** Written deduction with named classical inputs and a passing finite replay of the
word combinatorics and the repair probabilities. Not refereed, not formally verified. This is a family
theorem about an explicitly presented class, not universal Fixed Price.

Status records a written deduction or imported theorem, not independent mathematical verification.
