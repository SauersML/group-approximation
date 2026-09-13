---
rg: 2
id: infinite-left-orderable-kazhdan-group-from-aut-f4
kind: route
title: A left-orderable finite-index subgroup of the Kazhdan group Aut(F_4) answers Navas's Question 3
target: infinite-left-orderable-kazhdan-group
requires: [aut-f4-has-left-orderable-finite-index-subgroup, aut-f4-has-property-t]
---

Let `Delta` be a left-orderable subgroup of finite index in `Aut(F_4)`.
- `Aut(F_4)` has property (T) (`aut-f4-has-property-t`).  Property (T) passes to finite-index subgroups, so `Delta` is Kazhdan.
- `Aut(F_4)` is infinite, since it contains `Inn(F_4) ~= F_4`.  So `Delta` is infinite.

So `Delta` is an infinite left-orderable Kazhdan group.  ∎

This gives a concrete finitely presented family on which Navas's question is
open and the standard obstructions do not apply; see the Attempts of
`aut-f4-has-left-orderable-finite-index-subgroup`.
