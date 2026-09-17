---
rg: 2
id: relative-countable-eg-gives-eg-for-aleph-one-groups
kind: claim
title: The relative Eilenberg--Ganea statement for countable pairs implies the Eilenberg--Ganea conjecture for all groups of cardinality at most aleph_1
distinct_from:
  eilenberg-ganea-conjecture: that is the absolute conjecture; this is a conditional statement propagating a relative countable statement up one cardinal.
  continuous-free-chain-unions-have-gd-two: that is the unconditional special case in which every intermediate group is free, where the relative step is Lemma 1 there.
artifacts: []
---

**ESTABLISHED** through `relative-countable-eg-gives-eg-for-aleph-one-groups-proof`. Unreviewed. Only the stated direction is proved.

## The relative statement REG_ω

Let `H ≤ G` be countable groups with `cd G ≤ 2` and `pd_{ZG} I_{G/H} ≤ 1`, where `I_{G/H} = ker(Z[G/H] → Z)`. Let `K` be any 2-dimensional `K(H,1)`. Then there is a 2-dimensional `K(G,1)` containing `K` as a subcomplex, with the inclusion inducing `H ≤ G`.

- **The hypothesis is necessary.** Suppose `K ⊆ X` with both complexes 2-dimensional and aspherical, and let `p: X̃ → X` be the universal cover. Then `C_*(X̃, p^{-1}K)` is a free `ZG`-complex in degrees `0..2` whose only homology is `I_{G/H}` in degree 1. So `pd I_{G/H} ≤ 1`.
- **Without the pd hypothesis the statement fails.** Take `T^2` in a Klein-bottle group: the two lifts to the double cover would give disjoint cellular 2-cycles representing `±` the same class of `H_2 ≅ Z`.
- **REG_ω with `H = 1` is countable EG.** So REG_ω is at least as strong as EG for countable groups.

## Claim

REG_ω implies that every group `G` with `|G| ≤ ℵ_1` and `cd G = 2` has `gd G = 2`.

## Inverter reading

Suppose EG fails. Consider a counterexample of minimal cardinality. If that cardinality is `ℵ_1`, then REG_ω fails for some countable pair `G_α ≤ G_{α+1}` of subgroups of it.

The pair has two forced properties:
- `pd I_{G_{α+1}/G_α} ≤ 1`;
- `G_α` is not free, by `continuous-free-chain-unions-have-gd-two`.

The proof supplies both through the elementary-submodel club lemma: for any cd-2 group, every step of an elementary-submodel filtration satisfies the pd condition.

So an uncountable counterexample reduces to a failure of the *relative* problem for countable groups with a non-free base.

## Limits of the reduction

- **No converse is known.** EG does not obviously give REG_ω: the given `K` is arbitrary.
- **The argument stops at `ℵ_1`.** At `ℵ_2`, the successor step needs REG for pairs of size `ℵ_1`. Proving that would require amalgamating the countable extensions coherently, and this is where the argument stops.
