---
rg: 2
id: leavitt-24k-feasibility-vanishes
kind: claim
title: Every 24k relative-unitary defect infimum vanishes
distinct_from:
  binary-leavitt-hyperlinear-iff-24k-feasible: that is the proved equivalence between this statement and hyperlinearity of the unit group; this is the matrix statement itself, which is open.
  leavitt-24k-feasibility-has-a-uniform-gap: that is the opposite branch, a positive uniform lower bound for one relation set; exactly one of the two holds and neither is proved.
  binary-leavitt-unit-group-hyperlinear: that is the group-level question; this is its explicit finite-dimensional optimization form, with both finite factors frozen and one relative unitary as the only unknown.
artifacts:
  - research/artifacts/leavitt-24k-relative-unitary-reduction-2026-09-08.md
---

**OPEN.**  In the notation of `binary-leavitt-hyperlinear-iff-24k-feasible`,
show that

```text
Delta_m = 0    for every m,
```

i.e. that for every `m` and every `eps > 0` there are `k >= 1` and
`U in U(24k)` with `||pi_(k,U)(r) - I||_(2,24k) < eps` for all `r in T_m`.
By that criterion this is equivalent to hyperlinearity of the binary Leavitt
unit group, and by `hyperlinear-nonsofic-from-leavitt-unit-group` it would
produce a hyperlinear nonsofic group.

## Attempts

- **No construction of the relative unitaries is offered.**  The frozen
  factors are explicit and the relation sets are computable, so this is a
  concrete finite-dimensional feasibility question at each `m`, but no
  family `U_k` is known even for the first nontrivial relation set beyond the
  exact model of `leavitt-24k-first-relation-has-exact-finite-model`, which
  satisfies one relation and is not a model of `H`.
- **Fixed dimensions are excluded, for a reason that is an input.**  For each
  fixed `k`, exact zeros of the objectives over the nested `T_m` would have a
  common point by compactness, giving a homomorphism `H -> U(24k)` with `c`
  nontrivial; every subgroup of `U(24k)` is MF by constant sequences, so this
  contradicts the supplied obstruction that homomorphisms from `H` to MF
  groups are trivial.  Hence for each `k` some `m(k)` already has a strictly
  positive minimum, and a successful family must leave every finite set of
  dimensions.  This says nothing about the infimum over all `k`.
- **The first relation forces a large commutator but does not block this.**
  `(LR2)` keeps the commutator of the two frozen factors at distance
  `1/sqrt 2 - o(1)`, so `U = I` and every nearly commuting `U` fail; the
  `GL_3(F_8)` model shows a solution of that single constraint exists.
- **Deferred:** the honest status is that neither branch has been attacked
  here.  The value of the reduction is that an attack is now a matrix
  problem with a `24k`-dimensional unknown rather than a group problem.
