---
rg: 2
id: amenable-recursive-groups-have-recursive-expander-profile
kind: claim
title: A finitely generated amenable recursively presentable group has recursively bounded short-expander profile, so no single amenable subgroup of a finitely presented group carries expander growth past every recursive bound
distinct_from:
  recursive-amenable-classes-have-uniform-folner-bounds: that is Cavaleri's recursive Følner bound; this transfers it to the short-expander profile through a coset-averaging inequality, which is what kills the single-subgroup form of the short-expander route to E.
  torsion-amplifies-to-kazhdan-expanders-over-group-rings: that builds a finitely generated group with solvable word problem whose short-expander profile escapes every recursive bound; this shows no amenable such group exists, so that group's non-amenability is forced.
---

**ESTABLISHED** by `amenable-recursive-groups-have-recursive-expander-profile-proof`
(lane proof; one import, the landed Cavaleri node; not independently reviewed;
no priority claimed). The coset-averaging inequality is the one of the w10 lane
node `short-expander-subgroups-force-folner-growth` (not on this branch). It is
re-proved in the route, so nothing here depends on w10.

**Statement.** Let `H = <X>` be finitely generated, amenable and recursively
presentable. This holds, for instance, when `H` is a finitely generated subgroup
of a group with solvable word problem, and so for every finitely generated
amenable subgroup of a finitely presented simple group.

1. **Coset averaging.** For every rational `δ > 0` and `L >= 1`,
   `F_(H,X)(⌈2L^2/δ⌉) > X^δ_(H,X)(L) / 2`. This uses only amenability of `H`,
   not recursive presentability.
2. **Kill.** `X^δ_(H,X)` is recursively bounded for every rational `δ > 0`.

Here `F` is the Følner function of `recursive-amenable-classes-have-uniform-folner-bounds`,
and `X^δ` is the profile of
`finiteness-decidable-iff-finite-subgroup-profile-recursive`.

**Class kill for the short-expander route to E.**
- *Invariant:* Cavaleri's recursive Følner bound for one recursively presentable
  amenable group.
- *Failing step:* asking one amenable subgroup to contain short finite expanders
  past every recursive bound.
- *Consequence:* witnesses must vary with `U`, as in
  `fp-simple-amenable-subgroups-beat-every-recursive-folner-bound`. By item 4 of
  `folner-separators-of-boone-higman`, they must also not form a certified
  family.
- *What survives:* the single-host, varying-subgroup form. Its host-level gate is
  `fp-simple-short-expander-profiles-escape-recursive-bounds`.
