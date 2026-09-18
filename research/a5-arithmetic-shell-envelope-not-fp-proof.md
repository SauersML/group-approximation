---
rg: 2
id: a5-arithmetic-shell-envelope-not-fp-proof
kind: route
title: A finitely presented envelope would force a finitely presented near group, which the tree abelian-rank bound excludes
target: a5-arithmetic-shell-envelope-is-not-finitely-presented
requires:
  - shell-envelope-fp-forces-fp-germ-group
  - arithmetic-a5-near-group-is-not-finitely-presented
  - a5-free-product-has-simple-arithmetic-shell-envelope
artifacts:
  - research/artifacts/shell-envelope-germ-necessity-2026-09-18.md
---

P = A_5*A_5 is finitely generated and infinite, so `shell-envelope-fp-forces-fp-germ-group`
applies to its bijective-base enumeration nu. If E_nu were finitely presented,
R_nu would be finitely presented. `arithmetic-a5-near-group-is-not-finitely-presented`,
item 4, proves that R_nu is not finitely presented for exactly this enumeration.
Hence E_nu is not finitely presented.
