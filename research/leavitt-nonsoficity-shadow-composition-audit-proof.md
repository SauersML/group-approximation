---
rg: 2
id: leavitt-nonsoficity-shadow-composition-audit-proof
kind: route
title: Compare the macroscopic MF shadow with both Kazhdan nonsoficity derivations
target: leavitt-nonsoficity-does-not-close-macroscopic-mf-branch
requires:
  - simple-torsion-groups-have-a-macroscopic-mf-dichotomy
  - openai-leavitt-unit-nonsofic
  - universal-leavitt-el4-nonsofic
---

The dichotomy supplies exactly an operator-norm asymptotic representation
whose normalized Hilbert--Schmidt shadow is faithful.  It supplies no finite
permutation action or sofic chart.  Inspecting the two routes proving binary
Leavitt nonsoficity shows that both obtain the missing expanding finite action
charts from the Kazhdan expander decomposition.  Deleting that step leaves no
consumer for the faithful HS shadow.  Hence the direct composition is not a
Property-`(T)`-free proof; it requires the new converter stated in the target.

