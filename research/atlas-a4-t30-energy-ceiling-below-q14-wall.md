---
rg: 2
id: atlas-a4-t30-energy-ceiling-below-q14-wall
kind: claim
title: The A4 packet and collision 19243 force aligned t30 root energy below one half
distinct_from:
  atlas-a4-root-energy-ellipse-ceiling: that asks for a much smaller two-coordinate ellipsoidal bound sufficient against the S3 wall; this asks only for one t30 coordinate below the stronger q14 wall.
  atlas-q14-forces-t30-covariance-floor: that is the established opposite lower bound supplied by a second kernel relation; this is the missing packet-plus-19243 upper estimate.
artifacts:
  - experiments/atlas_q14_t30_wall.py
  - experiments/atlas_triangle_19243_packet.py
  - experiments/atlas_a4_gl5_packet_screen.py
---

Let `U_n` be a normalized exact-regular A4 context-network sequence in the
fixed reference-aligned coordinates.  Assume that all thirty shortest A4
packet defects tend to zero and that

```text
||q_19243(U_n)-1||_2 ->0.                             (T30-19243)
```

With `h_n=rho_n(t30)`, prove

```text
limsup_n x_30(U_n)^2
 =limsup_n [1-Re tau_n(U_n h_n U_n^* h_n)] <1/2.      (T30-CEIL)
```

Equivalently,

```text
limsup_n ||U_n h_n U_n^*-h_n||_2^2 <1.
```

This is now the shortest A4 analytic endpoint.  The independent kernel
relation `q_14` forces the opposite lower bound `liminf x_30^2>=1/2`, so no
full S3 recovery or four-variable root ellipse is needed once `(T30-CEIL)` is
proved.

## Attempts and constraints

- **Collision 19243 is essential.**  The exact q14 audit finds `11` inner and
  `10` outer classical alignments satisfying both the thirty-relation packet
  and q14.  Therefore packet plus q14 cannot imply `(T30-CEIL)`.  The upper
  proof must use 19243 or another condition that excludes precisely these
  survivors.
- **The exact classical boundary is empty with 19243.**  Among the `30+30`
  packet-compatible A8 automorphism alignments, none satisfies 19243.  In the
  first rank enlargement, exactly `202` of `9,999,360` `GL5(F2)` positions
  satisfy the packet and again none satisfies 19243.  This supports a
  stability theorem but does not itself control arbitrary multiplicity.
- **Work in the shifted geometry.**  The local constraints are the shifted
  products `C_a R C_b` from
  `atlas-a4-packet-centralizer-product-compiler`, not unshifted products of
  centralizers.
- **Use the four holonomies.**  Tree gauge leaves only one `K_(2,2)` and three
  `K_(2,4)` rectangle holonomies.  A dimension-free inequality need only
  control the `t30` covariance through these four multiplicity unitaries and
  the 19243 residual.
- **Use the exact parabolic--C3 bridge.**
  `atlas-t30-is-one-parabolic-c3-bridge` proves
  `t30=(h6_2 k_0)^-1 z b(h6_2 k_0)` and hence
  `x30^2<=3E_PC3`.  The remaining upper estimate may therefore be attacked as
  the four-coordinate weighted ceiling
  `atlas-a4-parabolic-c3-bridge-energy-ceiling`, with threshold `1/6`.
- **A non-strict estimate is insufficient.**  The q14 wall is exactly `1/2`;
  the upper estimate must retain a positive strict margin after passage to a
  microstate subsequence.
