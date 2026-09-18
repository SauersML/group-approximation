---
rg: 2
id: complexity-graded-universal-decidable-hosts-exist
kind: claim
title: For every recursive time bound T some decidable finitely generated group contains every group with word problem in F(T)
refuted_by:
  - no-decidable-group-contains-every-polynomial-dehn-fp-group
distinct_from:
  no-decidable-group-contains-every-fp-rf-group: that excludes one decidable host for a class with no common complexity bound; this asks for one decidable host per complexity bound, the survival that claim left open.
  complexity-bounded-host-classes-are-not-universal: that constrains what a time-bounded host can contain; this asked for hosts whose own bound may exceed T, which that theorem permits.
---

**REFUTED.**  The statement: for every recursive `T` there is a finitely
generated group `U_T` with solvable word problem that contains a copy of every
finitely generated group whose word problem lies in `F(T)`, the languages
decidable in time `C T(Cn) + Cn + C`.  An exact-time variant, with `C = 1`, is
refuted with it.

It was the first of two prerequisites in
`boone-higman-via-complexity-graded-universal-inputs`.  It passes the complexity
count of `complexity-bounded-host-classes-are-not-universal`, since `U_T` may
have a far larger bound than `T`, and is therefore not excluded by any existing
wall.

It fails at `T(n) = 2^((n+1)^37)`, already for finitely presented members with
Dehn function `≼ n^18` (`no-decidable-group-contains-every-polynomial-dehn-fp-group`).
A decidable `U_T` would decide the halting problem by a homomorphism search over
the effective BORS family `H_e`.  It fails for every recursive `T` that
eventually dominates `2^(c n^36)` for each `c`.  For small `T` the question
depends on whether an effective halting family fits under `T`, and this lane
did not settle it.  The route dies regardless.
