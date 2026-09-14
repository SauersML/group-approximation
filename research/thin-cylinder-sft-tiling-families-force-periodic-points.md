---
rg: 2
id: thin-cylinder-sft-tiling-families-force-periodic-points
kind: claim
title: A quantum tiling family of a Z^2 SFT periodic along an axis with period at most 4D+1 exists only if the SFT has a point with that period
distinct_from:
  sft-tiling-module-dimensions-and-periods-must-diverge: that bounds the sup-diameter of a period torus from below, so only one axis must be long; this forbids short periods along either axis, on any vector space
  torus-quantum-tilings-decide-matriciality-of-sft-rings: that equates exact matriciality with torus modules at every scale; this restricts which tori can carry such modules
artifacts:
  - research/artifacts/sk-labbe-matricial-thin-cylinders-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Ω ⊆ A^(Z^2)` be an SFT with forbidden patterns in `B_r`, let `D >= r`, and let `1 <= L <= 4D+1`. Take any field and any vector space. Then a nonzero scale-`D` family (axioms (Q1)–(Q3) of `sft-crossed-product-fp-iff-quantum-rigid`) that is `(0,L)`-periodic exists iff `Ω` has a point with period `(0,L)`. The same holds for `(L,0)`.

**Consequences for free `Ω`.**
- `𝒯_(D,Λ)(Ω,k) = 0` whenever `Λ` contains `(0,L)` or `(L,0)` with `L <= 4D+1`.
- A witness torus for `torus-quantum-tilings-decide-matriciality-of-sft-rings` therefore has both axis periods `>= 4D+2`. The known bound gives only one.
- In a covariant family, no `U_i^ℓ` with `ℓ <= 4D+1` centralizes the family.
- Over `F_q^d`, the family needs `q^(d^2) > 4D+2`.
- For Labbé's `Ω_U` (`r = 1`) at `D = 3`, witnesses need tori of at least `14 × 14` in both directions.

**Mechanism.**
- On a torus of circumference `<= 4D+1`, whole columns commute, so column patterns form commuting partitions of unity.
- An ordered product over a long run of columns expands `1` into terms that each contain an illegal window, and those terms vanish.
- The mechanism is one-dimensional and says nothing about tori that are long in both directions.

Route: `thin-cylinder-sft-tiling-families-force-periodic-points-proof`.
