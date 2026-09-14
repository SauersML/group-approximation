---
rg: 2
id: universal-rf-host-via-lef-ultraproduct-words
kind: route
title: The universal residually finite host through the LEF family host, with no Wilson step
target: universal-simple-kazhdan-lef-groups-exist
requires: [simple-kazhdan-lef-host-for-recursive-lef-groups]
artifacts:
  - research/artifacts/sk-universal-lef-host-a-2026-09-13.md
---

This route is independent of `wilson-countable-rf-into-two-generator-rf-groups`. It uses the 2-generator LEF lemma and the lamplighter host behind `simple-kazhdan-lef-host-for-recursive-lef-groups`.

- **(a)** Countable residually finite groups are LEF. So a countable set of countable residually finite groups is a countable set of countable LEF groups, and part (a) of `simple-kazhdan-lef-host-for-recursive-lef-groups` gives one infinite f.g. simple Kazhdan LEF host.
- **(b)** Recursively presented f.g. residually finite groups are recursively presented f.g. LEF groups, so part (b) of the same claim contains them all in one host. This includes the finitely presented residually finite groups and the f.g. linear groups, recursively presented as recorded in `universal-simple-kazhdan-lef-groups-exist-proof`. □
