---
rg: 2
id: left-orderable-non-sofic-via-relative-kazhdan-defect-criterion
kind: route
title: Replace property (T) by the relative property (T) of abelian subgroups that ordered groups carry
target: left-orderable-non-sofic-group
requires: []
---

**DEAD.**

*The plan.*  Left-orderable groups are not known to contain infinite Kazhdan
subgroups, but they do contain relatively Kazhdan pairs, such as
`(F_2 x| Z^2, Z^2)` acting on the interval.  So prove a version of
`sofic-groups-kill-rigid-compression-defects` in which `(G, Gamma)` only has
relative property (T), with `Gamma` abelian and infranormal.  Then feed a
left-orderable pair into the integer-lamp wreath of
`left-orderable-non-sofic-via-integer-lamp-rigid-pair`.

*Where it dies.*  The relative criterion is false, already inside
left-orderable groups.  `relatively-kazhdan-amenable-pairs-allow-sofic-defects`
gives a residually finite locally indicable `G = Z[1/p]^2 x| (F_0 x <pI>)`
with `(G, Z^2)` relatively Kazhdan and `Z^2` infranormal and not normal.
Its integer-lamp wreath is sofic, by Alekseev--Bradford's amenable-stabilizer
theorem and Gao--Kunnawalkam Elayavalli--Patchell, yet carries a nontrivial
defect.  The mechanism consumes the rigidity of `Gamma` itself.  An amenable
`Gamma` has hyperfinite sofic approximations, and the coset action with
amenable stabilizers is sofic.  Nothing is left for a defect to contradict.

*What survives.*  The variant that also asks `G` to be Kazhdan is not refuted.
Any left-orderable instance of it contains an infinite left-orderable Kazhdan
group (`infinite-left-orderable-kazhdan-group`).
