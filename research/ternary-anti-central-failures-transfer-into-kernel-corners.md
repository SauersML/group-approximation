---
rg: 2
id: ternary-anti-central-failures-transfer-into-kernel-corners
kind: claim
title: Every direct-finiteness failure of the ternary anti-central summand transfers into a kernel corner as an invisible pair
distinct_from:
  ternary-anti-central-pairs-visible-or-invisible: that normalizes a pair by one group translate into a visible or an invisible form; this maps every pair into the kernel corner of a Klein idempotent, so the invisible form is universal.
  ternary-anti-central-kernel-has-klein-idempotents: that exhibits the kernel idempotent; this uses it with a level-two amplification to embed the whole summand into its corner.
artifacts:
  - research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md
---

With `q = eps_- E`, `E = [1]+[h1]+[h2]+[h1h2]` from
`ternary-anti-central-kernel-has-klein-idempotents`, put

    delta4(g) = sum_(|gamma|=2) S[gamma] g T[gamma],     mu(x) = delta4_*(x) E.

Then `mu : S_- -> q S_- q` is an injective unital ring homomorphism into the evaluation kernel:
`mu(eps_-) = q` and `pi mu = 0`. Its ingredients:
* `delta4` is an injective homomorphism of `G` commuting with the constants `h1, h2`;
* `H` meets `delta4(G)` only in `1`, because the only scalars of `delta4(G)` are `1` and `-1`,
  and `-1` is not in `H`.

So a pair `c a = eps_- != a c` gives the invisible pair `A = (eps_- - q) + mu(a)`,
`C = (eps_- - q) + mu(c)`, with `C A = eps_- != A C` and both factors in `eps_- + K_-`.

Consequently the following are equivalent:
* `S_-` is not directly finite;
* `F_3 eps_- + K_-` is not directly finite;
* some pair over `eps_-` has its defect in the kernel.

In particular `ternary-anti-invariant-swap-corner-is-full` implies
`ternary-anti-central-kernel-unitization-not-directly-finite`. This is the ternary analogue of
the binary universality of the invisible half, which lane `gk-l2-invisible` proved over `F_2`.

This is the instance `(q,d) = (3,2)` of `leavitt-identity-factor-failures-transfer-into-kernel-corners`.
Level two is the least level for this host.

Proof: Section 4 of the artifact.
