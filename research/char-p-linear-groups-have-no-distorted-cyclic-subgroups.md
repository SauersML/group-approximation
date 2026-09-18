---
rg: 2
id: char-p-linear-groups-have-no-distorted-cyclic-subgroups
kind: claim
title: In a finitely generated linear group over a field of positive characteristic every infinite cyclic subgroup is undistorted
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that root's obstruction O4 uses exponentially distorted unipotents of GL_2(Z[1/2]) to exclude VA and its subgroups as hosts in characteristic zero; this shows that no linear group of positive characteristic has a distorted cyclic subgroup, so O4 never applies there.
---

**ESTABLISHED** by `char-p-linear-cyclic-subgroups-undistorted-proof`
(elementary; lane-proved, not independently reviewed; presumably folklore, no
priority claimed).

## Statement

Let `K` be a field of characteristic `p > 0`, `Γ <= GL_n(K)` finitely
generated, and `g in Γ` of infinite order. Then `k ↦ g^k` is a quasi-isometric
embedding `Z -> Γ`: there is `c > 0` with `|g^k|_Γ >= c|k|` for all `k`.

## Consequence for hosts

By Burillo--Felipe, arXiv:2605.09763v1, Corollary 5, as quoted in
`gl-n-q-embeds-in-fp-simple-group` (O4), "VA does not contain any group with
cyclic subgroups that are distorted." By this claim that obstruction never
excludes a group linear over a field of positive characteristic. In
particular it does not exclude `GL_2(F_q(t))` from `VA` or `V`.

In characteristic zero `GL_2(Q)` contains `BS(1,2)`, with exponentially
distorted unipotents. So O4 is a characteristic-zero obstruction: its source is
exactly the infinite order of unipotent elements.

DERIVATION
char-p-linear-cyclic-subgroups-undistorted-proof
