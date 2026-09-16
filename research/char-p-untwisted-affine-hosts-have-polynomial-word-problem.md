---
rg: 2
id: char-p-untwisted-affine-hosts-have-polynomial-word-problem
kind: claim
title: Finitely generated subgroups of untwisted affine hosts over elementary abelian p-groups have polynomial word problem and exclude a KMS group
distinct_from:
  commutative-algebra-affine-groups-have-polynomial-word-problem: that bounds affine groups of modules over commutative algebras over finite fields; this carries the bound, through linearization, to Zaremsky's self-similar affine hosts over characteristic-p rings that need not be commutative, and to every untwisted affine host over an elementary abelian p-group.
  kms-groups-avoid-commutative-algebra-affine-hosts: that excludes a KMS group from affine groups over commutative algebras of positive characteristic; this excludes it from the characteristic-p self-similar affine hosts over non-commutative rings, a special case of the non-commutative hosts that node lists as surviving.
  char-p-untwisted-self-similar-affine-groups-are-linear: that is the linearization over F_p[[t]]; this is its word-problem consequence and the exclusion of hard inputs.
artifacts:
  - research/artifacts/fp-self-similar-hard-wp-swarm-2026-09-16.md
---

**ESTABLISHED** by `char-p-untwisted-affine-hosts-polynomial-wp-proof`. No novelty
is claimed. Not independently reviewed.

## Statement

**Setting.** As in (b) of `char-p-untwisted-self-similar-affine-groups-are-linear`:
- `A` is an elementary abelian `p`-group;
- `ν: A -> A` is injective, with `A/νA` finite and `∩_k ν^k A = 0`;
- `Γ <= Aut(A)` has a finite-index subgroup that commutes with `ν`.

**Conclusions.**
1. Every finitely generated `H <= A x| Γ`, with finite generating set `B`, has word
   problem over `B` decidable in time `C*l^C + C`. The constant `C` depends on `H`
   and `B`. The algorithm is only claimed to exist, not to be computable from
   `(A, ν, Γ)`.
2. All these word problems lie in the single class `F(g)`, `g(n) = 2^n`, of `(UWB1)`
   in `uniform-wp-bound-excludes-bh-universal-targets`.
3. The Kharlampovich--Myasnikov--Sapir group `G` of
   `kms-groups-avoid-commutative-algebra-affine-hosts` embeds in no such `A x| Γ`.

## What it covers

- `R^n x| Γ` for every `Γ <= GL_n(R)`, where `R` is a unital ring of characteristic
  `p`, commutative or not, satisfying the hypotheses of
  `principal-ideal-affine-groups-are-self-similar`. This is every characteristic-`p`
  instance of Zaremsky's Example 4.7.
- Every self-similar `A x| Γ` from Zaremsky's Corollary 4.5 over an elementary
  abelian `p`-group whose twist `γ -> φγφ^(-1)` satisfies (d) of the linearity node,
  for instance a twist of finite order, or conjugation by an element of `Γ`.

## Meaning for `fp-self-similar-groups-with-arbitrarily-hard-word-problem`

- No finitely generated group that embeds in such a host beats `T(n) = 2^n`. As a family, these
  self-similar hosts cannot witness the hole. By
  `complexity-bounded-host-classes-are-not-universal`, they are also not universal
  hosts for groups with solvable word problem.
- Attempt 2 of the hole dismissed Zaremsky's affine hosts by appeal to linearity.
  That dismissal is now proved in characteristic `p`. In characteristic `0` and in
  exponent `p^m` with `m >= 2` it is still unproved for non-commutative rings.
- Among Corollary 4.5 hosts `A x| Γ` over elementary abelian `p`-groups, a hard
  witness has to use a twist not covered by (d) of the linearity node. There the
  linear parts act by infinite-state `F_p`-linear transducers (artifact, §6). This
  says nothing about self-similar groups that are not such hosts, and it does not
  cover non-abelian `A`, exponent `p^m` with `m >= 2`, or characteristic `0`.
