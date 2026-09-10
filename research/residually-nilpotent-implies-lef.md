---
rg: 2
id: residually-nilpotent-implies-lef
kind: claim
title: Every residually nilpotent group is LEF, with no finite generation hypothesis
---

Every residually nilpotent group is LEF.  Equivalently, every finite subset of a
residually nilpotent group embeds multiplicatively into a finite group.

The finitely generated case is the familiar one — a finitely generated
residually nilpotent group is residually finite — but the statement needs no
finite generation at all, because LEF is a local property and residual
nilpotence is subgroup-closed.  The uncountable and non-finitely-generated
residually nilpotent groups are LEF for the same reason the finitely generated
ones are residually finite.

Two consequences used elsewhere:

* Residual nilpotence cannot be a source of LEF failure.  Any construction that
  wants a non-LEF group has to break residual nilpotence first, so a non-LEF
  target is never reachable by refining a residually nilpotent tower.
* Combined with `fp + LEF => rf` (Vershik--Gordon), a finitely presented
  residually nilpotent group is residually finite.  So a finitely presented
  group that is residually nilpotent and not residually finite does not exist,
  which closes off one route to finitely presented non-LEF examples.
