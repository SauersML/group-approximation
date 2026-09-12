---
rg: 2
id: kl-counterexample-screening-by-local-subgroup-structure
kind: route
title: Screen the Leavitt unit group for a violation by what sits inside it
target: kl-violating-equation-over-leavitt-unit-group
requires: []
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

The natural first move when asked whether a specific group violates
Kervaire--Laudenbach: look at its subgroups.  `R^x = L_(F_2)(1,2)^x` has an
unusually explicit local structure — finite chart groups, transvections, a
virtually free source, a prefix-code normal form — so one hopes to find a
local feature that either forces a violation or rules one out, and to search
only among words supported on it.

Dead by `kl-counterexample-absorbs-any-countable-group`: if any
counterexample exists at all, then for every countable `A` there is a
counterexample whose coefficient group contains a copy of `A`.  So no
criterion of the form "contains / does not contain a copy of `A`" can
distinguish groups that admit a violation from groups that do not, and a
screen built out of local subgroup data has no possible verdict.

**What survives the demolition.**  Properties of the whole group that are not
inherited from countable subgroups — hyperlinearity above all, which really
does exclude violations (`kervaire-laudenbach-holds-for-hyperlinear`) and is
not of the "contains a copy of" form.  Also the explicit local structure
itself, which remains the reason this group is a reasonable place to compute
at all; what dies is only the idea that the subgroups decide the question.
