---
rg: 2
id: kms-fp-rf-groups-with-arbitrarily-large-depth
kind: claim
title: Finitely presented residually finite groups have depth functions exceeding any recursive function
distinct_from:
  kms-arbitrarily-hard-fp-rf-groups: that imports the Kharlampovich-Myasnikov-Sapir theorem on word-problem time complexity; this imports their separate theorem on the depth function, a bound on sizes of separating finite quotients that the time-complexity theorem does not give.
artifacts:
  - research/artifacts/sk-wp-host-2026-09-13.md
---

**ESTABLISHED by literature import.** Let `G = ⟨X⟩` be finitely generated. Its depth function `ρ_G(n)` is the least
number such that any two words `w ≠_G w'` of length at most `n` are separated by a homomorphism to a group `H` with
`|H| ≤ ρ_G(n)` (Bou-Rabee; independent of `X` up to the natural equivalence).

For every recursive function `f` there is a finitely presented residually finite group `G`, solvable of class three,
with `ρ_G(n) > f(n)` for all `n`. The word problem of `G` can moreover be taken at least as hard as membership in any
prescribed recursive set.

Consumer: `recursive-lef-growth-hosts-miss-some-fp-rf-group`.

DERIVATION
kms-fp-rf-groups-with-arbitrarily-large-depth-citation
