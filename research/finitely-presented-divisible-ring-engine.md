---
rg: 2
id: finitely-presented-divisible-ring-engine
kind: claim
title: A six-generator finitely presented nonzero ring inverts every integer, so torsion-free finitely presented rings embed unitally in finitely presented Q-algebras
distinct_from:
  ring-simple-envelope-characteristic-obstruction: that refutes simple envelopes for coefficient rings of mixed characteristic such as Z/6Z; this shows that characteristic zero with full divisibility can be arranged inside a finitely presented ring, so divisibility is not itself an obstruction to finitely presented characteristic-zero hosts.
  char-zero-algebra-unit-hosts-exclude-unipotents: that excludes unipotent-containing simple unit hosts over rings of bounded divisibility; this builds finitely presented rings of unbounded divisibility (Q-algebras), which lie outside its hypothesis (D).
artifacts:
  - experiments/char-zero-projective-host-screens-2026-09-17/divisible_ring_engine_model.py
---

**ESTABLISHED.** Let `D` be the unital ring with generators
`s, t, w, v, b, a` and the seven relations

- R1 `st = ts = 1`
- R2 `vw = 1`
- R3 `s(wv)t = 1 - wv`
- R4 `b(wv) = (wv)b`
- R5 `vbw = b + 1`
- R6 `b(1 - wv) = 1 - wv`
- R7 `ab = 1`

Then:

1. `D` is nonzero. The canonical map `Q -> D` is a unital embedding with image in `Z(D)`. So `D` is a finitely presented ring that is a `Q`-algebra.
2. **Coproduct corollary.** Let `R` be a finitely presented unital ring whose additive group is torsion-free. Then the coproduct `R *_Z D` of `Z`-algebras is finitely presented, it is a `Q`-algebra, and `R -> R *_Z D` is injective.

In particular, for every finitely presented group `H`, `Z[H]` embeds unitally in a finitely presented `Q`-algebra.

**Scope.** This is a calibration of a necessary screen. Suppose `PEL_4(L)` is simple and `Z[H] ⊆ L`. Then `L` is simple by [[projective-elementary-simplicity-forces-simple-ring]], and so `Q ⊆ Z(L)`. This claim shows that this forced divisibility is compatible with finite presentation. It says nothing about simplicity or about the group-theoretic clauses. The construction is elementary and probably folklore; no novelty is claimed.
