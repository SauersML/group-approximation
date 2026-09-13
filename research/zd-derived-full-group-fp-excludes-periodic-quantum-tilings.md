---
rg: 2
id: zd-derived-full-group-fp-excludes-periodic-quantum-tilings
kind: claim
title: If the derived full group of a free minimal Z^2 SFT is finitely presented, its local tiling algebras have no nonzero finite-dimensional module at large scale, so periodic quantum tilings refute finite presentation
distinct_from:
  periodic-quantum-tilings-refute-quantum-rigidity: that shows a finite-dimensional module of the local tiling algebra refutes quantum rigidity, hence finite presentation of the crossed-product algebra; this shows the same modules refute finite presentation of the derived full group, through the unit map and Malcev's theorem.
  zd-derived-full-group-fp-forces-finite-type: that uses classical colourings with legal small windows, which exist only for non-SFTs; this uses operator-valued periodic families, which may exist for aperiodic SFTs and have classical periodic points as their one-dimensional case.
  sft-crossed-product-fp-iff-quantum-rigid: that characterizes finite presentation of the crossed-product algebra by commutation of all operator families; this is a consequence of finite presentation of the group, proved without rigidity and weaker in form.
artifacts:
  - research/artifacts/labbe-periodic-quantum-tilings-obstruct-fp-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Statement.** Let `X ⊆ A^(Z^2)` be a free minimal subshift of finite type and
`G = D([[Z^2 ~ X]])`. If `G` is finitely presented, there is `D_0` such that for every `D >= D_0`
and every field `k`, the local tiling algebra `A_D(X, k)` of `sft-crossed-product-fp-iff-quantum-rigid`
has no nonzero finite-dimensional module.

**Consequence.** Suppose that for every `D` some nonzero finite-dimensional space carries a periodic
quantum tiling of `X` at scale `D`: idempotents `E_a(z)`, periodic under a finite-index lattice,
satisfying (Q1)–(Q3) of that claim. Then `G` is not finitely presented. Over a finite field these
tilings are exactly the finite-dimensional modules (`periodic-quantum-tilings-refute-quantum-rigidity`,
item 2).

**Mechanism.**
- The units `U_s = sum_v chi[kappa_(s^(-1)) = v] u^v` of the rule 3-cycles have bounded length.
  Every relator of `G` becomes an identity of bounded length in the crossed product, and the local
  presentation already satisfies such identities (Lemma 1.2 of the ring artifact). So `G` maps to
  the units of `A_D`.
- A finite-dimensional module gives a finitely generated linear quotient of the infinite simple group
  `G`. By Malcev that quotient is trivial.
- The bounded identity `chi[pi] (U_s - 1) chi[pi] = -chi[pi]` then kills every cylinder idempotent,
  so the module is zero.

**Calibration.** For an infinite minimal `Z`-subshift, periodic points of Markov approximations give
one-dimensional families, and the same proof gives Matui's theorem that `D([[phi]])` is never
finitely presented (artifact, Remark 2.2). For an aperiodic `Z^2`-SFT the one-dimensional families
are periodic legal tilings and do not exist. The only obstruction of this kind that can survive is a
contextual operator-valued tiling.

**Why it matters.**
- It gives a refutation mechanism for `labbe-shift-derived-full-group-is-finitely-presented` that
  uses no colouring with defects and no LEF: the route `labbe-not-fp-via-periodic-quantum-tilings`.
- Any positive proof must exclude contextual periodic quantum tilings of Labbé's tiles at large
  scale, a finite-dimensional part of `labbe-wang-shift-crossed-product-is-finitely-presented`.

Route: `zd-derived-full-group-fp-excludes-periodic-quantum-tilings-proof`.
