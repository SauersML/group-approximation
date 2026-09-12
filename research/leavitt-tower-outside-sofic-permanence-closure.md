---
rg: 2
id: leavitt-tower-outside-sofic-permanence-closure
kind: claim
title: The binary and d-ary Leavitt unit groups lie outside the sofic-permanence closure and need a direct automaton argument
distinct_from:
  sofic-permanence-closure-omits-simple-fa-nonsofic-groups: that is the abstract closure theorem for the class avoiding a fixed simple FA nonsofic group; this applies it to the concrete Leavitt tower and draws the consequence for the surjunctivity search.
  leavitt-surjunctivity-tower: that records the group embeddings V <= R^x <= A^x and the monotonicity of surjunctivity; this records that two of the three are outside the sofic-permanence closure.
  leavitt-unit-group-nonsurjunctive: that seeks the injective non-surjective automaton; this says a permanence argument from sofic groups cannot substitute for one.
artifacts:
  - research/artifacts/gottschalk-other-hosts-2026-09-12.md
---

ESTABLISHED. Take `Sigma = R^x = L_{F_2}(1,2)^x`, which is a finitely presented
simple property-FA nonsofic group (`leavitt-unit-group-is-simple-fa-nonsofic`).
By `leavitt-surjunctivity-tower`, `R^x <= A^x = L_{F_2}(1,d)^x` for every
`d >= 2` over `F_2`. So both `R^x` and every such `A^x` contain a copy of
`Sigma`, and by `sofic-permanence-closure-omits-simple-fa-nonsofic-groups` they
lie outside the closure `D_Sigma` of the sofic groups under subgroups, directed
colimits, extensions, graphs of groups and marked limits.

Consequence for the census. No permanence argument that starts from sofic groups
and uses those operations -- including the landed
`finitary-split-extension-surjunctivity-permanence`,
`graph-folds-over-surjunctive-groups-are-surjunctive`,
`lef-lamp-graph-wreaths-are-surjunctive` and the wreath and double theorems --
can produce `R^x` or `A^x`. Deciding their surjunctivity requires a direct
cellular-automaton argument on the group itself, in either direction.

Scope. This does not apply to `V` at the bottom of the tower: `V` does not
contain `R^x` (the inclusion runs `V <= R^x`), and no finitely presented simple
FA nonsofic subgroup of `V` is known, so `V` is not excluded from the closure by
this obstruction. Likewise the Fournier-Facio group
(`fournier-facio-outside-surjunctivity-permanence`) contains no known such
`Sigma` -- its simple subgroups are the torsion-free Burger-Mozes or Hyde-Lodha
factors, which are not known nonsofic -- so the obstruction is silent there too,
and its surjunctivity is open for the separate reason recorded in that node. The
obstruction bites exactly at the groups that literally contain the first nonsofic
group `R^x`.
