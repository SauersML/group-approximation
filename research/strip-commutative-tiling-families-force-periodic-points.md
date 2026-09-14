---
rg: 2
id: strip-commutative-tiling-families-force-periodic-points
kind: claim
title: A periodic quantum tiling family of a Z^2 SFT that commutes inside every narrow strip along a rational direction forces a periodic point
distinct_from:
  thin-cylinder-sft-tiling-families-force-periodic-points: that assumes an axis period at most 4D+1, which makes narrow strips commute automatically; this assumes only narrow-strip commutativity, for any period and every rational direction, at strip width depending on r and not on D, with an explicit run length for aperiodic SFTs
  torus-quantum-tilings-decide-matriciality-of-sft-rings: that equates exact matriciality with torus modules at every scale; this constrains the noncommutation any such module must contain
artifacts:
  - research/artifacts/sk-labbe-2d-strip-contextuality-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `Ω ⊆ A^(Z^2)` is an SFT with forbidden patterns in `B_r`.
- `e = (p,q)` is primitive, `ℓ_e(z) = q z_1 − p z_2`, and `m_e = r(|p|+|q|)`.
- `E_a(z)` is a nonzero family of idempotents on a vector space over any field, periodic along `Le` for some `L >= 1`.
- It satisfies partitions of unity (Q1) and vanishing of illegal `r`-ball products (Q3_r) whenever their factors commute.
- Every scale-`D` family with `D >= r` (`sft-crossed-product-fp-iff-quantum-rigid`) qualifies, by descent.

**Theorem.**
1. Suppose `E_x(z)` and `E_y(z')` commute whenever `|ℓ_e(z) − ℓ_e(z')| <= 2m_e`. Then `Ω` has a point with period `Le`.
2. Suppose `Ω` has no periodic point. Then every run of `|A|^(2m_e L) + 2m_e` consecutive `ℓ_e`-levels contains a noncommuting pair on levels of the run at `ℓ_e`-distance `<= 2m_e`.
3. Conversely, a point with period `Le` gives a classical family with these commutations.

**Special case.** For `e = (0,1)` and `L <= 4D+1`, the hypothesis of 1 holds automatically for scale-`D` families. This recovers the (⇒) direction of `thin-cylinder-sft-tiling-families-force-periodic-points`.

**Mechanism.**
- Levels are commuting blocks.
- An ordered product over a long run of levels kills every term containing an illegal window.
- König's lemma turns legal words of every length into a periodic point; pigeonhole pumping gives the explicit run length.

Route: `strip-commutative-tiling-families-force-periodic-points-proof`.
