---
rg: 2
id: hilbert-hotel-cstar-total-invisibility-proof
kind: route
title: Combine total Hilbert-hotel radical with nonamenability
target: hilbert-hotel-cstar-total-invisibility
requires:
  - hilbert-hotel-model-full-mf-radical
  - full-mf-radical-cstar-reflection
artifacts:
  - research/hilbert-hotel-cstar-total-invisibility.md
---

The Hilbert-hotel theorem gives `Rad_MF(H)=H`.  The group is nontrivial and
cannot be finite, since every finite group is MF.  It has property `(T)`;
an amenable discrete Kazhdan group is finite.  Hence `H` is nonamenable.

Apply `full-mf-radical-cstar-reflection`.  Its maximal conclusion identifies
the intersection of all MF-target kernels with the augmentation ideal.  Its
reduced conclusion says every MF-target homomorphism is zero.  The canonical
trace on `C*_r(H)` is faithful, and its matrix amplifications are faithful,
so `C*_r(H)` remains stably finite independently of the MF-reflection
collapse.
