---
rg: 2
id: osin-group-times-z-has-bvc
kind: claim
title: The product of a torsion-free two-conjugacy-class group with Z has property BVC and maps onto Z
---

Let `O` be a finitely generated torsion-free group with exactly two conjugacy classes
(`osin-torsion-free-two-conjugacy-class-groups-exist`). Then `G = O × Z`:

- is finitely generated and torsion-free, and not virtually cyclic;
- maps onto `Z`;
- has property BVC, with witness `<(g,1)>`, `<(g,0)>`, `<(1,1)>` for any `g != 1`.

**Why it matters for Zaremsky 1.7.** Even for groups with infinite abelianization, the finite
presentation hypothesis of the von Puttkamer–Wu conjecture
(`finitely-presented-bvc-groups-are-virtually-cyclic`) cannot be dropped. Also, the uniform
fiber bound `bvc-bounds-conjugacy-classes-in-fibers-of-maps-to-z` holds here (`R(id^m) = 2`)
without virtual cyclicity. So any proof for finitely presented groups with positive first
Betti number must use finite presentation beyond conjugacy counting.

Credit: von Puttkamer–Wu, arXiv:1704.05304, Theorem III(b), already give a finitely
generated torsion-free `H ⋊ Z` with (bCyc) (equivalently BVC, since the group is
torsion-free). This node records the simplest instance, with a two-line proof.
