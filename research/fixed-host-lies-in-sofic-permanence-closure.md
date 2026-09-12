---
rg: 2
id: fixed-host-lies-in-sofic-permanence-closure
kind: claim
title: The fixed Gottschalk tester host is built from sofic groups by the landed surjunctivity permanence theorems
refuted_by:
  - fixed-host-outside-sofic-permanence-closure
---

**REFUTED.**

Statement: the host `U` of `gottschalk-surjunctivity-fixed-two-generator-tester`
lies in the class `S_0` generated from sofic groups by:
- subgroups;
- directed colimits;
- finitary split extensions over members
  (`finitary-split-extension-surjunctivity-permanence`);
- graph folds into members (`graph-folds-over-surjunctive-groups-are-surjunctive`);
- LEF-lamp graph wreaths over members (`lef-lamp-graph-wreaths-are-surjunctive`).

## Attempts

- *Decompose `U` along its construction*: enumerated free product, two-generator
  compression, Higman embedding, compression. The input of every step already
  contains every finitely presented group, so there is no base of sofic pieces
  to start from.
- *Refuted* by `fixed-host-outside-sofic-permanence-closure`. `U` contains the
  Leavitt unit group, a finitely presented simple nonsofic Kazhdan group, and
  every member of `S_0` avoids such a group.
