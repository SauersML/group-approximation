---
rg: 2
id: laminar-defects-localize-to-a-nonsofic-overfilled-star
kind: claim
title: A nonpositive-trace laminar combination contains one overfilled star that occurs in no sofic group
distinct_from:
  sofic-amalgam-finite-subgroup-idempotent-traces-are-strict: that proves positivity when the whole configuration occurs in a sofic group; this localizes a failure to a single parent with its children, so only that star's subgroups need a sofic realization, and records the overfilled shape the star must have.
  leavitt-units-have-laminar-finite-subgroup-defect: that is the open existence question for a zero-class laminar defect in the binary Leavitt unit group algebra; this is an established necessary condition on any candidate, over any group and any prime.
  nested-two-finite-subgroup-idempotents-have-strict-rank: that is the one-child case, where the gap is strict at every join; this treats parents with several orthogonal children over further subgroups, where the gap can only close through a cycle of intersections.
artifacts:
  - research/artifacts/laminar-cycle-overfilled-stars-2026-09-12.md
---

**ESTABLISHED** (route `laminar-defects-localize-to-overfilled-star-proof`; verified by `w4-vf-linear-b`,
Section 31 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`, 1dc81f2a24).

Let `G` be any group, `p` a prime, `S = F_p[G]`, and `F` a laminar family of idempotents `x_i` in
`M_n(F_p[H_(s(i))])` over finite subgroups `H_s <= G`, with atoms `alpha_y = y - sum_(z in C(y)) z` for
`y in {1} u F`. Let `d` be a nonzero idempotent in the span of `1` and `F` with `t_p([d S^n]) <= 0`, for
instance a balanced combination.

Then some nonzero atom `alpha_y <= d` has an **overfilled star**:
- its children `z_1, ..., z_m` are pairwise orthogonal, lie below `y` (or `I_n`), and do not sum to it;
- `r(z_1) + ... + r(z_m) >= r(y)`, although each `r(z_i) < r(y)`, so `m >= 2`;
- the finite subgroups carrying `y` and the `z_i` have no compatible realization in any sofic group: no
  sofic group contains isomorphic copies of them that agree on pairwise intersections and meet exactly in
  the images of those intersections (Theorem 2.6 of
  `research/artifacts/finite-subgroup-combination-defects-2026-09-12.md`);
- in particular their nontrivial pairwise intersections contain a cycle, so the star uses at least three
  distinct finite subgroups, and the children use at least two.

**Consequences.**
- **Local search.** Candidates for `leavitt-units-have-laminar-finite-subgroup-defect` are decided one
  star at a time. A star inside a common finite subgroup, or inside any sofic subgroup, is dead.
- **Thompson hosts.** An overfilled star whose subgroups all lie in Thompson's `V <= R^x` certifies that `V`
  is not sofic.
- **Constants.** Stars built from constants at finitely many prefix levels are dead, because they lie in
  one finite subgroup.
