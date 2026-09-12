---
rg: 2
id: radu-bmw-lattice-amalgam-splittings-proof
kind: route
title: Bass–Serre theory on both tree actions of Radu's lattice gives the two amalgam splittings
target: radu-bmw-lattice-splits-as-amalgams-of-virtually-free-groups
requires:
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
artifacts:
  - research/artifacts/radu-lattice-binary-algebra-splittings-2026-09-12.md
---

## Why sufficient

Artifact Section 1, Theorem A and Corollary A′.

* **Vertical tree `T_v = Gamma_R/A`.**
  * The first-level action of `A` on the root's neighbours is `c -> (x z)` with `a, b` trivial, so the
    edge orbits are `{y}` and `{x, z}`.
  * `y` and `x` invert their edges, with setwise stabilizers `P_y` and `E_x`.
  * Subdividing gives the quotient segment `m_y -- o -- m_x`, with half-edge groups `A` and `A_ev`.
* **Horizontal tree `T_h = Gamma_R/V`.**
  * The first-level action of `V` is onto `S_3`, so there is one edge orbit.
  * `a` inverts its edge, with stabilizer `E_a`, and the quotient is `o -- m_a` with half-edge group `V_a`.
* **Checks.** The Euler characteristic is `1/4` from both splittings and from the complex. The
  algebra statement is the group-algebra functor applied to the pushouts.
