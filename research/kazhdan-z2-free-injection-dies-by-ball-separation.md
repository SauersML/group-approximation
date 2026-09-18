---
rg: 2
id: kazhdan-z2-free-injection-dies-by-ball-separation
kind: route
title: Invert the injection to get a Lipschitz map into T×Z^2, bound its ball separators by the centroid slab, and contradict superquadratic Kazhdan ball separation
target: kazhdan-orbits-never-inject-boundedly-into-z2-times-free
requires:
  - tree-times-zk-images-have-polynomial-ball-separators
  - kazhdan-schreier-graphs-have-superquadratic-ball-separation
---

Suppose that `φ : Z → Z^2×F_d` is injective with bounded left displacement.

1. By item 2 of the slab lemma, `bsep_(Sch(G,Z,S))(D) = O(D^2)`.
2. The second prerequisite says `bsep(D)/D^2 → ∞`.

These contradict each other. ∎

Each prerequisite can fail on its own.
- The first is proved.
- The second is the whole content. A Kazhdan Schreier graph with polylogarithmic ball separators would
  refute it, but it would not by itself answer the need YES: T×Z^2-embeddability is strictly stronger than
  small ball separation.
