---
rg: 2
id: atlas-a4-root-energy-ellipse-ceiling
kind: claim
title: One ellipsoidal scalar in square-root four-cycle energies beats the 19243 wall
distinct_from:
  atlas-a4-joint-weighted-cycle-ceiling: that target leaves five positive weights existentially quantified; this target analytically eliminates all of them and retains only one nonlinear scalar of the four trace deficits.
  atlas-a4-anisotropic-four-cycle-ceiling: that target uses a fixed diagonal Cauchy budget; this target uses the exact triangle envelope and the optimized weighted S3 exchange rate.
---

For the normalized exact-regular A4 context-network sequence put

```text
x_ij(n)=sqrt(1-Re tau_n(V_n(tij))) >=0,
S_n=2x_01(n)+2x_23(n)+4x_30(n).
```

Prove the single scalar ceiling

```text
limsup_n [S_n^2 + S_n x_12(n) + x_12(n)^2] < 3/128.   (A4-ROOT-ELLIPSE)
```

This is the completely optimized form of the four-cycle-to-S3 contradiction.
Indeed `S_n^2` is the exact positive-word triangle upper budget for the
synthesized raw involution `t21`, while `x_12^2` is the budget for the directly
observed raw involution `t12`.  The cross term is precisely what remains after
optimizing the relative weights in the two-generator S3 Cayley gap.

The threshold uses the collision relation directly.  In the Leavitt quotient
necessity sequence `q_19243(U_n)->1`, so
`atlas-19243-relation-forces-s3-distance` gives the squared S3-distance floor
`1/32`; the optimized Cayley dual turns this into `3/128`.  The older
centrality-only route paid an unnecessary second occurrence of the collision
word and produced the weaker threshold `3/512`.

Equivalently,

```text
S_n^2+S_n x_12+x_12^2
 =(S_n+x_12/2)^2 + 3x_12^2/4,
```

so the target is literally membership in one fixed ellipse in the two aggregate
root-energy coordinates `(S_n,x_12)`.

## Attempts

- **Use the corrected shifted-double-coset compiler.**  The local A4
  centralizer-product theorem cannot be applied to the two raw chart alphabets
  as if they were already aligned: some same-chart packet pairs have product
  order `6`, others order `2`.  `atlas-a4-packet-centralizer-product-compiler`
  now fixes one exact packet alignment `R` and gives the correct constraints
  `C_a R C_b` / `C_b R C_a`.  Any holonomy or moment proof of this ellipse must
  be written in that shifted geometry.  The unshifted `C_a C_b` formulation is
  false.
- **Exploit the exact first-rank finite screen.**
  `atlas-a4-gl5-packet-collision-screen` exhausts all `9,999,360` relative
  positions in `GL5(F2)` for the standard embedded chart `A8`.  Exactly `202`
  satisfy all thirty A4 pair-cubes, distributed among chart-intersection sizes
  `20160`, `1344`, and `168`; collision `19243` is nonidentity on every one.
  Thus the first ambient-rank enlargement has no exact packet-plus-collision
  escape.  The three intersection sizes coincide with the chart/parabolic/core
  ladder and are a concrete guide for a finite-stratum or building-rigidity
  proof.
- **Search the ellipse directly.**  Do not introduce artificial Cauchy or S3
  weights in an SDP/SOS implementation.  Lift the four nonnegative root-energy
  variables and optimize this one positive quadratic form.
- **Exploit direction-selective collision control.**  A strong bound on `t30`
  is especially valuable because it enters `S_n` with coefficient `4`; `t01`
  and `t23` enter with coefficient `2`, while `t12` occupies the separate
  detector coordinate.
- **Use the shorter q14 directional wall when possible.**  The exact kernel
  word `q_14=(t23_(1)t23_(2))^2` becomes a two-syllable `t30` comparison after
  the fixed packet alignment.  `atlas-q14-forces-t30-covariance-floor` proves
  `liminf x_30^2>=1/2`, reducing the sufficient upper target to the separate
  one-coordinate claim `atlas-a4-t30-energy-ceiling-below-q14-wall`.  The
  ellipse remains a valid endpoint, but the one-coordinate route has much
  more numerical slack.
- **Use the two-context classical core as a dual guide.**  The exact packet
  audit already identifies two A4 contexts hitting every collision-perfect
  classical alignment.  Ask whether their matrix-valued residuals dominate the
  ellipse rather than reconstructing all thirty context gauges.
- **Treat the four rectangle holonomies as the only nonclassical variables.**
  After exact A4 qutrit normalization and the biclique tree gauges,
  `atlas-a4-packet-four-rectangle-normal-form` leaves one `K_(2,2)` and three
  `K_(2,4)` rectangle holonomies on multiplicity wires.  A proof may therefore
  target a fixed four-unitary trace inequality for collision `19243`, rather
  than the full `20160 k` relative chart unitary.
- **Return the escaping point.**  Failure of a finite SOS relaxation should
  output an approximate point `(S,x12)` outside the ellipse together with the
  multiplicity mode realizing it; that is a targeted new packet-search input.
