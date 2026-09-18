---
rg: 2
id: rf-decidable-groups-embed-in-decidable-fg-branch-groups
kind: claim
title: Every finitely generated residually finite group with solvable word problem embeds in a finitely generated branch group with solvable word problem
distinct_from:
  efrf-groups-frattini-embed-in-efrf-branch-groups: that proves this for effectively residually finite (EFRF^+) inputs; this is the question for all decidable residually finite inputs, where Rauzy's non-effective groups are the only open case.
  rf-higman-embedding-for-decidable-groups: that asks for a finitely presented residually finite overgroup and is refuted by Rauzy; this asks for a finitely generated branch overgroup with solvable word problem, which need not be effectively residually finite.
artifacts:
  - research/artifacts/gq-bh-openq-lists.md
---

**OPEN.** A. Bishop and E. Schesler, arXiv:2509.12161v2, TeX l.212–214:

> Does every finitely generated residually finite group $G$ with solvable word problem
> embed in a finitely generated branch group with solvable word problem?

## Where the question is open (lane reformulation; elementary)

1. **Effective inputs are settled.** If `G` is `EFRF^+`, the answer is yes, by
   `efrf-groups-frattini-embed-in-efrf-branch-groups` (Bishop–Schesler Theorem B). For
   recursively presented groups, `EFRF^+` is the same as `EFRF` plus solvable word
   problem.
2. **Non-effective inputs force non-effective hosts.** A finitely generated subgroup of
   an `EFRF` group is `EFRF` (Rauzy, Fact 4). So if `G` is decidable and residually
   finite but not `EFRF`, every finitely generated host `Γ ⊇ G` is not `EFRF`. Such
   `G` exist: Rauzy's Dyson-type groups `L(A)`, arXiv:2002.02540, Theorem 2. These are
   amalgams of two lamplighter groups over the lamps indexed by a recursive,
   profinitely closed, not effectively closed set `A ⊂ Z`.
3. **So the question is equivalent to its non-effective case.** A positive answer
   requires finitely generated branch groups with solvable word problem that are not
   effectively residually finite.
4. **A route to a negative answer.** Suppose every finitely generated branch group with
   solvable word problem were `EFRF`. Then `L(A)` embeds in no finitely generated branch
   group with solvable word problem, and the answer is **no**.

## Evidence (lane remark, heuristic)

The classical uncountable families of branch groups have solvable word problem
exactly when their defining data are computable. These are the Grigorchuk groups
`G_ω` (Grigorchuk 1984) and spinal groups over computable data. In those cases the tree
action is computable, so the group is `EFRF`. No finitely generated branch group with
solvable word problem and non-computable level quotients is known to this lane.

## Lesson for general BH

Branch groups are a candidate "intermediate universal class" for the residually
finite part of Boone–Higman. On effective inputs they are one (Bishop–Schesler). This
question asks whether the class stays universal once effectiveness of residual
finiteness is dropped.
- **If the answer is no:** effective residual finiteness is intrinsic to branch
  groups, which is a Rubin-type rigidity statement in algorithmic form. Then branch
  hosts can never absorb Rauzy-type inputs.
- **For BH itself:** Rauzy-type inputs are no obstruction, because simple hosts are
  never residually finite.
