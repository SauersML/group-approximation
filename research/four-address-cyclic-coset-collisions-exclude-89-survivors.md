---
rg: 2
id: four-address-cyclic-coset-collisions-exclude-89-survivors
kind: claim
title: Indicators of cyclic subgroups collide with constants and exclude 89 of the 195 surviving unbalanced binary four-address rules over every group
distinct_from:
  binary-four-address-single-flip-balance-census: that excludes rules by finite perturbations (single invisible flips) and leaves 195 survivors; this excludes 89 of those survivors by infinite-support collisions, tau(1_U) = tau(0) for a cyclic subgroup U, which no finite perturbation detects.
  binary-four-address-injective-automata-have-balanced-rules: that is the full four-address balance claim, still open; this shrinks its surviving rule list from 195 to 106 classes.
  binary-three-address-strict-automata-are-linear: that uses a coset background at three addresses, where the pattern is decided by membership in one coset; this shows that at four addresses the patterns of 1_U are the block indicators of the left-coset partition of the memory, so the test reduces to a finite check over coarsenings.
artifacts:
  - experiments/gottschalk-four-address-coset-collisions-2026-09-17/coset.py
  - experiments/gottschalk-four-address-coset-collisions-2026-09-17/coset.json
  - experiments/gottschalk-four-address-coset-collisions-2026-09-17/control.py
  - experiments/gottschalk-four-address-coset-collisions-2026-09-17/control.out
---

**ESTABLISHED (computer assisted)** by `four-address-cyclic-coset-collisions-proof`.

Notation is from `binary-four-address-single-flip-balance-census`. Let `M = {m_0 = 1, m_1, m_2, m_3}` be distinct
elements of a group `G`, `mu : {0,1}^4 -> {0,1}`, and `tau(x)(g) = mu((x(g m_i))_i)`.

**Lemma (cyclic-coset collision).** Let `U <= G` be a subgroup and let `pi_U` be the partition of `{0,1,2,3}` with
`i ~ j` iff `m_i^-1 m_j in U`. Write `1_C` for the indicator pattern of a block `C`.
- If `mu(1_C) = mu(0000)` for every block `C` of `pi_U`, then `tau(1_U) = tau(0)`.
- If `mu(1 - 1_C) = mu(1111)` for every block `C`, then `tau(1 - 1_U) = tau(1)`.

Either way `tau` is not injective.

*Proof.* Coordinate `i` of the pattern of `1_U` at `g` is `[g m_i in U] = [g in U m_i^-1]`. The right cosets
`U m_i^-1` and `U m_j^-1` are equal iff `m_i^-1 m_j in U`, and are disjoint otherwise. So the pattern at `g` is
`1_C` when `g` lies in the coset `U m_i^-1` for the indices `i` in `C`, and `0000` when `g` lies in none of them.
Under the first hypothesis, every value of `tau(1_U)` is `mu(0000)`, which is the constant value of `tau(0)`.
The second case is the first for the complemented rule. QED.

**Theorem.** Of the 195 rule classes that survive the single-flip census, 89 are not injective over any group.
So an injective, unbalanced, binary four-address automaton over any group has one of 106 explicit rule classes,
listed in `coset.json` (`kept_blocking`).

**Why a finite check suffices.** Apply the lemma with `U = <m_i^-1 m_j>`. Suppose the realized quotient partition
of the twelve ordered pairs coarsens a blocking partition `P`. Then `pi_U` merges `k` with `l` for every pair
`(k, l)` whose quotient is `m_i^-1 m_j` or its inverse in `P`. The group may merge more. If `pi_U` has one block,
then `M` lies in `U`, so `<M>` is cyclic and the census already excludes the rule. So `P` is **killed** when some
pair `(i, j)` makes one of the lemma's conditions hold on every coarsening of this forced partition except the
one-block partition. A rule is excluded when all of its blocking partitions are killed.

**The strongest single-flip candidate falls.** Rule `7913` is `P1094` of the census artifact, on the placement
`{1, a, b, ba}` with table group `F_2`. It has no invisible single or two-site perturbation. It outputs `1` on
`0000, 1100, 1010, 0110, 1110, 1001, 0101, 1101, 0011`. `coset.py` kills all six of its blocking partitions. On
`P1094` the kill can be checked by hand.
- Take `U = <a>` and assume `b` is not in `<a>`. Otherwise `<M> = <a>` is cyclic.
- The left `U`-cosets split `M` into `{1, a}` and `{b, ba}`.
- The patterns of `1_U` are therefore `1100`, `0011` and `0000`, and `mu` equals `1` on all three.
- Hence `tau(1_<a>) = 1 = tau(0)`.

This collision has infinite support whenever `a` has infinite order, which explains why the finite-perturbation
search found no witness for this rule.

**Counts** (`coset.json`).

| status | rule classes |
|---|---|
| survivors in | 195 |
| excluded by coset collisions | 89 |
| still open | 106 |

- Of the 132 rules that the uncontrolled perturbation search `dflip3.json` left open, 61 are excluded here.
- Adding the 63 uncontrolled closures of that search would leave 71 open rules.
- The 28 excluded rules that `dflip3.json` had also closed now have a controlled exclusion.
- Also accepting invisible single flips on the coset background (`coset.py ... flip`) excludes no further rule.
