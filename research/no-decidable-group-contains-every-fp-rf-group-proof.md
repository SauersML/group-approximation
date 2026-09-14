---
rg: 2
id: no-decidable-group-contains-every-fp-rf-group-proof
kind: route
title: A single decidable host has a recursive word-problem time bound, so the uniform-bound exclusion applies to it
target: no-decidable-group-contains-every-fp-rf-group
requires: [uniform-wp-bound-excludes-bh-universal-targets]
artifacts:
  - research/artifacts/sk-wp-host-2026-09-13.md
---

Let `U = ⟨T⟩` have solvable word problem, decided by a total algorithm `A`.
- Let `t(n)` be the largest running time of `A` over all words of length at most `n`. It is recursive: run `A` on the
  finitely many such words. It is also non-decreasing.
- The word problem of `U` lies in `F(t)`, with constant `C = 1`.
- So the class `{U}` satisfies the hypothesis of `uniform-wp-bound-excludes-bh-universal-targets` with `g = t`.

That claim gives a finitely presented residually finite group that embeds in no member of `{U}`, i.e. not in `U`.

The excluded group is supplied through `kms-arbitrarily-hard-fp-rf-groups` inside that claim's route. It is a
finitely presented residually finite group whose word problem is not in `F(t)`, whereas every finitely generated
subgroup of `U` has word problem in `F(t)` up to the substitution constant.
