---
rg: 2
id: leavitt-tower-outside-sofic-permanence-closure-proof
kind: route
title: Apply the fixed-host closure theorem to the binary unit group inside the tower
target: leavitt-tower-outside-sofic-permanence-closure
requires:
  - leavitt-unit-group-is-simple-fa-nonsofic
  - leavitt-surjunctivity-tower
  - sofic-permanence-closure-omits-simple-fa-nonsofic-groups
artifacts:
  - research/artifacts/gottschalk-other-hosts-2026-09-12.md
---

## Direct proof

Set `Sigma = R^x = L_{F_2}(1,2)^x`.

1. `Sigma` is a finitely presented simple property-FA nonsofic group
   (`leavitt-unit-group-is-simple-fa-nonsofic`), so it is a group of the kind the
   closure theorem excludes.
2. `leavitt-surjunctivity-tower` gives `Sigma = R^x <= A^x` for every d-ary
   `A^x = L_{F_2}(1,d)^x` over `F_2`. Thus `R^x` and every `A^x` contain a copy
   of `Sigma`.
3. `sofic-permanence-closure-omits-simple-fa-nonsofic-groups`: the class
   `D_Sigma` of groups with no subgroup isomorphic to `Sigma` contains every
   sofic group and is closed under subgroups, directed colimits, extensions,
   graphs of groups and marked limits. A group containing `Sigma` is not in
   `D_Sigma`, hence is not built from sofic groups by those operations.

Therefore neither `R^x` nor any d-ary `A^x` over `F_2` is produced by a
permanence argument from sofic groups; each needs a direct cellular-automaton
argument. `V` is excluded from this conclusion because `V <= R^x` places `V`
below `Sigma`, not above it, and no such `Sigma` is known inside `V`.
