---
rg: 2
id: fp-direct-limit-of-quotients-equals-a-finite-stage
kind: claim
title: A finitely presented direct limit of a sequence of quotients of a free group equals one of its finite stages
---

**ESTABLISHED** (proof in `fp-direct-limit-of-quotients-equals-a-finite-stage-proof`).

Let `F` be a free group of finite rank, `K_1 <= K_2 <= ...` normal subgroups of
`F`, and `K = U_i K_i`. If `G = F / K` is finitely presented, then `K = K_i` for
all sufficiently large `i`, so `G = F / K_i` as marked groups.

**Use for Zaremsky Problem 1.11.** Iterative constructions of infinite torsion
groups kill more and more elements and pass to the limit. By this claim, the
limit can be finitely presented only if some finite stage is already the limit
group, and so already torsion. This is the precise form of the remark by
Ol'shanskii–Sapir (arXiv:math/0208237, p. 3) that "there is no hope to construct
finitely presented examples as such limits". It is also the mechanism of the
second proof of Theorem 4.1 in Bartholdi–Grigorchuk–Šunić (arXiv:math/0510294,
p. 52). See `hyperbolic-limit-torsion-groups-are-not-finitely-presented`.
