---
rg: 2
id: almost-all-one-relator-groups-satisfy-boone-higman
kind: claim
title: Almost every one-relator group with at least three generators embeds in a simple group of type F_infinity, and so does every one-relator group meeting the Sapir--Spakulova or Brown criteria
distinct_from:
  one-relator-groups-satisfy-boone-higman: that is the full open problem (BBMZ Problem 5.3(9)); this settles it with probability tending to 1 for at least three generators, and for explicit criteria, not for every one-relator group.
  ascending-hnn-of-free-groups-satisfy-boone-higman: that is the embedding theorem for ascending HNN extensions of free groups; this combines it with Sapir--Spakulova's theorem that generic one-relator groups embed in such extensions.
  drutu-sapir-group-satisfies-boone-higman: that is one two-generator one-relator group; this is a generic statement plus explicit criteria covering many one-relator groups.
artifacts:
  - research/artifacts/gq-bh-bh-free-05-ascending-hnn.md
---

**ESTABLISHED** through `almost-all-one-relator-groups-bh-proof`. Lane proof
(bh-free-05). It composes one literature import, read at source, with `ascending-hnn-of-free-groups-satisfy-boone-higman`. Not
independently reviewed. No priority is claimed; the search was bounded to the arXiv API.

## Statement

Say `G` is BH+ if `G` embeds in a simple group of type `F_∞` and in a finitely presented
group with an action of type (A). Then `G` satisfies `boone-higman-conjecture` and the
permutational form.

1. **Generic.** Let `k >= 3`. In each of the random models NR, CR and IC of
   M. Sapir and I. Špakulová, *Almost all one-relator groups with at least three generators
   are residually finite*, arXiv:0809.4693v2 (J. Eur. Math. Soc. 13 (2011)), the probability
   that the random `k`-generator one-relator group of complexity `r` is BH+ tends to `1`
   as `r -> ∞`.
2. **Explicit criteria.** A one-relator group `<x_1, ..., x_k | R>` is BH+ whenever it meets
   any of the following:
   - (SS1) the exponent sum of `x_k` in `R` is `0` and the maximal Magnus `x_k`-index of
     `x_1` is unique (their TeX label `thm1`);
   - (SS2) some hyperplane touches the trace of `R` in `Z^k` (their `lm4`);
   - (Br) `k = 2`, `R` is cyclically reduced and not in `[F_2,F_2]`, and one of the two
     supporting lines of the trace `w`, parallel to its endpoint `(m,n)`, meets `w` in
     one simple vertex or one simple edge. By K. S. Brown's Theorem 4.4, as quoted by SS
     (their `lm0`), `G` is then itself an ascending HNN extension of a finitely generated
     free group.
3. **Subgroups.** Every finitely generated subgroup of such a group is BH+.

## Scope

- BBMZ arXiv:2306.16356v3, Problem 5.3(9), asks for all torsion-free one-relator groups, and
  Linton--Nyberg-Brodda Problem 1.8.6 asks the same. Neither is settled here.
- Two generators. SS report Monte-Carlo evidence, from Borisov--Sapir and from
  Dunfield--Thurston, that about 94% of two-generator one-relator groups are ascending HNN
  extensions of free groups. They also report Dunfield--Thurston's observation that the
  probability is bounded away from `1`. Only (Br) is claimed here; no probability is claimed.
- Not covered: one-relator groups that embed in no ascending HNN extension of a free group.
  For example `baumslag-gersten-group-satisfies-boone-higman` stays OPEN, since that group
  is not residually finite.
