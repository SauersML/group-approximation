---
rg: 2
id: simple-group-width-over-all-finite-simple-groups-proof
kind: route
title: Split the finite simple groups into bounded rank, alternating, special linear and isometry families
target: simple-group-width-over-all-finite-simple-groups
requires: [simple-group-relator-width-in-finite-simple-targets, simple-group-psl-width-is-finite-field-linear-soficity, simple-group-classical-width-finite-field-linear-soficity, sofic-implies-linear-sofic-over-every-field]
---

`G = <X | R>` is infinite, finitely presented and simple.

**(i) => (ii).**
- **Not sofic.** A sofic group is `F_2`-linear sofic (`sofic-implies-linear-sofic-over-every-field`),
  hence linear sofic over finite fields. So (i) makes `G` nonsofic.
- **The families.** By the classification of finite simple groups, every nonabelian finite simple group
  is one of:
  - a sporadic group, or a group of Lie type of rank at most `8` (all exceptional types are here):
    bounded by (A) of `simple-group-relator-width-in-finite-simple-targets`, with no hypothesis;
  - an alternating group: bounded by (B) of the same node, since `G` is nonsofic;
  - `PSL_n(q)` of any rank: bounded by item 1 of `simple-group-psl-width-is-finite-field-linear-soficity`,
    under (i);
  - `PSp_n(q)`, `PSU_n(q)` or `PΩ^+-_n(q)` of any rank: bounded by
    `simple-group-classical-width-finite-field-linear-soficity`, under (i).
- **Abelian targets.** `Q = Z/p` is covered because `G` is perfect: `a_x = prod_r r(a)^(c_(x,r))`, so
  `w <= max_x sum_r |c_(x,r)|`.
- **The constant.** `K` is the maximum of the constants.

**(ii) => (iii).** For a bi-invariant length, `l(a_x) <= K max_r l(r(a))` by the triangle inequality and
conjugation invariance. So relator lengths tending to `0` force every generator length to `0`, which
contradicts `l(g_0(a)) >= 1`.

**(iii) => (i).** If `G` is linear sofic over finite fields, the proof of (iii) => (i) in
`simple-group-psl-width-is-finite-field-linear-soficity-proof`, Section 6, builds weak models into
`PSL_(3 n_i)(q_i)` with length `rho/(3 n_i)`. These groups are finite simple.
