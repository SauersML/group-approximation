---
rg: 2
id: labbe-torus-tiling-algebra-has-no-scale-one-module
kind: claim
title: For every finite-index lattice, the scale-1 torus tiling algebra of Labbé's Wang shift over F_q has no nonzero finite-dimensional module
distinct_from:
  labbe-torus-tiling-algebra-has-scale-one-module: that is the positive polarity; this is its negation
  labbe-wang-shift-crossed-product-is-not-exactly-matricial: that is the ring statement; this is its equivalent scale-1 form via labbe-ring-matricial-iff-scale-one-torus-module
  labbe-wang-shift-crossed-product-is-finitely-presented: that asks for quantum rigidity (all operator local tilings commute) at large scale; this asks only that no finite-dimensional module exists at scale 1 on any finite torus
artifacts:
  - research/artifacts/labbe-covariant-tower-inflation-2026-09-16.md
---

**OPEN.** Let `Ω_U` be Labbé's 19-tile Wang shift and `q` a prime power. For every finite-index `Λ ≤ Z^2`,
`𝒯_(1,Λ)(Ω_U, F_q)` has no nonzero finite-dimensional module. The algebra is defined by relations (T1)–(T3) at
scale `1`, as in `labbe-torus-tiling-algebra-has-scale-one-module`.

**Payoff.** `LC(Ω_U,F_q) ⋊ Z^2` would not be exactly matricial (`labbe-ring-matricial-iff-scale-one-torus-module`).
It would be a simple, finitely generated, stably finite ring with a rank model but no exact model.

## Attempts

- **Firewalls available at scale 1.** Any module is contextual, has both axis periods `>= 6`, and is noncommutative
  inside every narrow rational strip (see the Attempts of `labbe-torus-tiling-algebra-has-scale-one-module`). None of
  these excludes a module on a torus that is long in both directions.
- **Obstructions may use any fixed scale (swarm-labbe-wang-shift-crossed-produ, 2026-09-16, unreviewed).** By
  `morphism-towers-double-covariant-tiling-scales` with `ω^2`, restriction and descent, a scale-`1` module yields
  torus modules at every scale over `F_q`. So it suffices to show that for some fixed `D` no torus carries a nonzero
  `𝒯_(D,Λ)(Ω_U,F_q)`-module. Such an argument may use the pairwise legality at radii `2..7` of
  `labbe-ball-legality-is-pairwise-at-radii-two-to-seven`.
- **Through finite presentation.** A positive answer to `labbe-wang-shift-crossed-product-is-finitely-presented`
  refutes exact matriciality (the target's Attempts, via `matricial-aperiodic-sft-rings-are-not-quantum-rigid`), hence
  gives this claim by `labbe-ring-matricial-iff-scale-one-torus-module`. That question is open.
