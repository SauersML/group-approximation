---
rg: 2
id: atlas-a4-gl5-two-holonomy-readout-proof
kind: route
title: Exhaust the 202 packet positions and count fixed vectors of the covariance cocycles
target: atlas-a4-gl5-two-holonomy-readout
requires:
  - atlas-a4-gl5-packet-collision-screen
  - atlas-t30-is-one-parabolic-c3-bridge
artifacts:
  - experiments/atlas_a4_gl5_packet_screen.py
  - experiments/atlas-a4-gl5-two-holonomy-profile.json
---

The packet screen enumerates `GL_5(F2)/GL_4(F2)` by its 496 complementary
line--hyperplane pairs and tests all 20,160 internal alignments in each coset,
using exact bit arithmetic.  It returns exactly 202 packet-compatible relative
positions.

For a relative position `U` and an embedded chart element `g`, its covariance
cocycle is

```text
kappa_U(g)=U g U^(-1) g^(-1).
```

In the permutation action on `F2^5 minus {0}`, normalized character equals the
fixed-vector fraction.  If `fix(x)` denotes the number of its 31 fixed nonzero
vectors, then exactly

```text
31 delta_U(g)^2=2(31-fix(kappa_U(g))),
31 epsilon_q(U)^2=2(31-fix(q_19243(U))).
```

The script constructs the canonical `c=hk` and `a=zb` directly from the
frozen packet/collision matrices, evaluates these integers for every survivor,
and obtains the joint histogram stored in the JSON artifact.  Comparing its
ten entries gives

```text
31 E_2HOL <= 5(31 epsilon_q^2)
```

entry by entry.  The entry `(160,32)` occurs 96 times, proving sharpness.
All operations are matrix multiplication, inversion, and fixed-vector counting
over `F2`; no floating-point comparison is involved.
