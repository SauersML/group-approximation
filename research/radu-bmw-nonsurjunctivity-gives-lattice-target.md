---
rg: 2
id: radu-bmw-nonsurjunctivity-gives-lattice-target
kind: route
title: A strict automaton on Radu's BMW lattice is a strict automaton on a cocompact lattice in a product of two trees
target: strict-automaton-on-lattice-in-product-of-trees
requires:
  - radu-bmw-lattice-nonsurjunctive
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
artifacts:
  - research/artifacts/radu-lattice-strict-automaton-screens-2026-09-12.md
---

## Why sufficient

- `radu-bmw-lattice-embeds-in-titz-witzel-kernel` says `Gamma_R` acts simply transitively on the
  vertices of a product of two 3-regular trees.
- The action is free on vertices, so it is faithful. Vertex stabilizers are trivial, so the image
  in `Aut(T_3) x Aut(T_3)` is discrete. There is one vertex orbit, so it is cocompact. So `Gamma_R`
  is a cocompact lattice in a product of two trees.
- A strict automaton on `Gamma_R` is therefore exactly what
  `strict-automaton-on-lattice-in-product-of-trees` asks for.
