---
rg: 2
id: fp-simple-full-mf-radical-via-titz-witzel
kind: route
title: A Titz Mite-Witzel simple Kazhdan lattice has full MF radical
target: fp-simple-full-mf-radical-group
requires: [titz-witzel-simple-kazhdan-cat0-lattices-exist, simple-kazhdan-groups-have-full-mf-radical]
---

Let `K` be one of the five Titz Mite--Witzel finite residuals
`Gamma^_i^q`, recorded in `titz-witzel-simple-kazhdan-cat0-lattices-exist`.
That claim records that `K` is **finitely presented**: it has finite index in
the finitely presented lattice `Gamma_i^q`, and a finite-index subgroup of a
finitely presented group is finitely presented. It also records that `K` is
infinite, simple, torsion-free and Kazhdan.

`simple-kazhdan-groups-have-full-mf-radical` applies to every countable
infinite simple Kazhdan group, which gives `Rad_MF(K) = K`.

So `K` is a finitely presented simple group with full MF radical, and it is
moreover torsion-free. `∎`

This route uses only claims that were established before 2026-09-11. It was
missed when the target was opened. See the correction section on the target.
