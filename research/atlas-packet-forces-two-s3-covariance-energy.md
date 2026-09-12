---
rg: 2
id: atlas-packet-forces-two-s3-covariance-energy
kind: claim
title: Collision 19243 forces a positive two-generator S3 covariance floor in every atlas microstate
artifacts:
  - experiments/atlas_19243_s3_gap.py
distinct_from:
  raw-swap-forces-two-s3-covariance-energy: that lower bound uses separation of the compiled raw source word; this bound is forced by the canonical atlas packet itself and needs no marked-word hypothesis.
  atlas-19243-centrality-forces-s3-distance: that gives distance from the S3 commutant; this converts that geometric distance into the exact two covariance coordinates used by the shortest collapse route.
  atlas-19243-relation-forces-s3-distance: that supplies the stronger distance wall when the collision relation itself tends to one; the present claim records both the packet-only and quotient-necessity energy consequences.
---

Use the notation of `atlas-two-s3-covariance-collapse`.  For a relative chart
unitary `U`, let

```text
a = ||U rho(h_a) U^*-rho(h_a)||_2,
b = ||U rho(h_b) U^*-rho(h_b)||_2,
delta = max_(s in bar_S) ||pi_U(s)-1||_2.
```

Let `L_19243` be the fixed normal-closure constant from
`atlas-19243-centrality-forces-s3-distance`.  Then every multiplicity satisfies

```text
a^2+b^2
 >= max(0,(sqrt(2)-L_19243 delta)/16)^2.               (19243-S3-E)
```

Consequently every sequence with canonical atlas packet defect tending to zero
has

```text
liminf (a_n^2+b_n^2) >= 1/128.                        (19243-S3-FLOOR)
```

Unlike the earlier raw-swap lower bound, this is an unconditional property of
the finite atlas feasibility problem itself.  Any proof that the same packet
forces `a_n^2+b_n^2 -> 0` therefore rules out finite atlas microstates outright;
no extra separating word is needed for the contradiction.

For the quotient-necessity sequence one has the stronger hypothesis

```text
epsilon_q=||q_19243(U)-1||_2 ->0.
```

Then `atlas-19243-relation-forces-s3-distance` and the same Reynolds--Poincare
estimate give

```text
a^2+b^2 >= max(0,(sqrt(2)-epsilon_q)/8)^2,             (19243-REL-S3-E)
liminf_n (a_n^2+b_n^2) >= 1/32.                        (19243-REL-S3-FLOOR)
```

The `1/128` floor remains the correct uniform statement when only the finite
atlas-packet defect is assumed; `1/32` is the relevant floor for microstates
pulled back from the Leavitt quotient.
