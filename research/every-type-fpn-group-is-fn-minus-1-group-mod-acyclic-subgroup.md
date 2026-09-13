---
rg: 2
id: every-type-fpn-group-is-fn-minus-1-group-mod-acyclic-subgroup
kind: claim
title: "Every group of type FP_n is a quotient of a group of type F_{n-1} by an (n-1)-acyclic normal subgroup, for every n"
distinct_from:
  every-type-fpn-group-is-of-type-fhn: that claim asks for a geometric model, a free cocompact (n-1)-acyclic complex; this asks for an algebraic presentation of G as Q/P with Q of type F_{n-1} and P acyclic through degree n-1
  fn-groups-mod-acyclic-normal-subgroups-are-type-fhn: that claim is the proved step from such a presentation to FH_n; this asks whether such a presentation always exists
---

For every `n ≥ 1` and every group `G` of type `FP_n` there are a group `Q` of
type `F_{n−1}` and a surjection `Q → G` whose kernel `P` has
`H̃_i(P; ℤ) = 0` for `0 ≤ i ≤ n−1`.

This implies `every-type-fpn-group-is-of-type-fhn` through
`fn-groups-mod-acyclic-normal-subgroups-are-type-fhn`.
- At `n = 3` the two statements are equivalent, by
  `type-fh3-iff-fp3-and-superperfect-kernel-over-fp-group`.
- At general `n`, the converse would need a finite Kan–Thurston theorem
  (attributed to Baumslag–Dyer–Heller 1980, not checked). So treat this claim
  as a translation of Problem 1.4 into group theory, not as a new reduction.

## Attempts

- `n ≤ 2`: true for `n = 1` (any `Q`). For `n = 2` the kernel must be
  perfect: take a finitely presented `Q` whose relators generate the relation
  module; the kernel `P` has `H_1(P) = H_1` of the `G`-cover, which is `0`.
- `n = 3` (superperfect kernel over a finitely presented group): the attempts
  in `research/artifacts/zp-fpn-fhn-2026-09-13-part2.md` §8. Each dies:
  - killing perfect finitely normally generated subgroups works only if the
    `H_2` classes are supported on finitely generated perfect subgroups;
  - amalgamating superperfect groups adds `⊕_G H_1(A)`;
  - gluing acyclic groups along surface subgroups adds `⊕_G H_1(Σ)`;
  - universal central extensions are not finitely presented in general.
