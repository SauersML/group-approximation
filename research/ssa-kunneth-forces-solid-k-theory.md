---
rg: 2
id: ssa-kunneth-forces-solid-k-theory
kind: claim
title: Strongly self-absorbing algebras satisfying Kunneth have solid K-theory rings
artifacts:
  - research/artifacts/stw99-xv-solid-ring-reduction-2026-08-30.md
---

Let `D` be a strongly self-absorbing C\*-algebra satisfying the
Künneth short exact sequence for the pair `(D, D)`.  Then:

1. `K_1(D) = 0` (this part is unconditional: the approximately inner
   flip plus `K_1`-injectivity, which is automatic since SSA algebras
   are `Z`-stable by Winter and `Z`-stable algebras are `K_1`-bijective
   by Jiang).
2. The tensor multiplication makes `K_0(D)` a commutative unital ring
   whose multiplication map `K_0(D) ⊗_Z K_0(D) → K_0(D)` is an
   ISOMORPHISM — a *solid ring* in the sense of Bousfield--Kan.
3. By the Bousfield--Kan classification of solid rings, `K_0(D)` is
   `Z[J^{-1}]` (a localization of `Z`), `Z/n`, a product
   `Z[J^{-1}] × Z/n` with compatible support, or a colimit of such;
   if `K_0(D)` is torsion-free, it is exactly `Z[J^{-1}]`.

Consequently, on the torsion-free locus, STW Problem XV holds: the
`K`-theory `(Z[J^{-1}], 0)` is realized by the known strongly
self-absorbing algebra `M_{J^∞}` (and `(0,0)` by `O_2`, `(Z,0)` by
`Z` or `O_∞`).  In particular the Künneth problem IV yields Problem
XV for all `D` with torsion-free `K`-theory
(`stw99-iv-implies-xv-torsion-free`), and any counterexample to XV
satisfying Künneth must carry `K_0`-TORSION arranged in a solid ring —
the sharpest constraint on record for hypothetical exotic strongly
self-absorbing algebras.
