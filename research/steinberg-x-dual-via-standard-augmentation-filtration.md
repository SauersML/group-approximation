---
rg: 2
id: steinberg-x-dual-via-standard-augmentation-filtration
kind: route
title: Triangularize the modular X dual with a standard augmentation or PBW filtration
target: steinberg-x-plus-incidence-dual-is-surjective
requires:
  - steinberg-zero-marginal-space-is-biaffine-circulation
---

Filter the defining-characteristic Steinberg block by the global group
augmentation ideal, a local Jennings filtration of the opposite unipotent,
or the corresponding PBW/Hasse degree.  Try to make the outer root
coefficients triangular and prove that the leading symbol of `X^*` is a
unit modulo incidence-dual endpoint potentials.

This route is invalidated by
`steinberg-standard-augmentation-filtration-firewall`.
The global filtration is nonseparated, the local root filtrations are not
preserved by `A,B`, and an explicit zero-marginal quotient class jumps from
degree three to degree `p-1` under the actual row.  A genuinely new
two-sided filtration or direct block Bezout identity is not ruled out.
