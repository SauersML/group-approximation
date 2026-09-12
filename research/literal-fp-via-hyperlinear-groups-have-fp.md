---
rg: 2
id: literal-fp-via-hyperlinear-groups-have-fp
kind: route
title: The literal group inherits the factorization property from the generic hyperlinear upgrade
target: literal-group-factorization-property
requires: [hyperlinear-groups-have-factorization-property]
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

`E` is sofic (`literal-group-sofic`), hence hyperlinear
(`Sofic.isHyperlinear_of_isSofic`, Lean `LiteralSoficAssembly.markedGroup_isHyperlinear`).
If every hyperlinear group has the factorization property, so does `E`.

This is the generic route, and it is not expected to close: see the
obstruction recorded on the premise.  A proof specific to `E` would not pass
through here.
