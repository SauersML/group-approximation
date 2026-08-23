---
rg: 2
id: balanced-controlled-whitehead-return-checksum
kind: claim
title: A balanced controlled Whitehead return is certified by one trace-square checksum
distinct_from:
  controlled-fine-reflection-superrank-orientation-law: that computes the two Reynolds ranks and the canonical balanced orientation; this computes the exact mixed-return leakage and its finite ordinary-word checksum.
  adjoint-reynolds-return-needs-one-overlap-moment: that gives the general nested-packet identity; this specializes it to the controlled fine-reflection packet, the fixed canonical gap 1/32, and an arbitrary Whitehead actuator.
  odd-leavitt-prefix-whitehead-transport: that transports the physical coarse prefix corner to its fine descendant; this shows exactly what stronger adjoint-range return would still have to be forced.
---

**ESTABLISHED.**  Use the notation of
`controlled-fine-reflection-superrank-orientation-law`.  On a finite marked
carrier let `R_P,R_G` be the adjoint Reynolds projections of the two-qubit
Pauli group `P` and its controlled-reflection extension `G`, and let `W` be
any unitary (in particular, the evaluated signed prefix Whitehead word from
`odd-leavitt-prefix-whitehead-transport`).  Normalize trace on the adjoint
matrix space by `dim(H_-)^2` and put

```text
Theta_W=tr_ad(R_P Ad(W)^* R_G Ad(W) R_P).               (BCW1)
```

If the orientation correlation is `mu`, then

```text
Theta_W <= (1+mu^2)/32,                                (BCW2)

||(I-R_G)Ad(W)R_P||_(2,ad)^2
  =1/16-Theta_W
  >=(1-mu^2)/32.                                      (BCW3)
```

In particular canonical marked microstates have `mu=o(1)` after packet
exactification, so **every** attempted Whitehead return leaks at least

```text
1/32-o(1)                                              (BCW4)
```

of normalized adjoint Hilbert--Schmidt mass.  This is independent of the
ambient matrix dimension and of the chosen actuator.

The leakage is a finite ordinary-word trace-square checksum.  For exact
packet tables,

```text
Theta_W
 =1/(|P|^2 |G|) sum_(p_1,p_2 in P, g in G)
   |tr(U(p_1) W^* U(g) W U(p_2))|^2.                  (BCW5)
```

Consequently, if a mixed Whitehead cell supplies a relation-ideal estimate

```text
Theta_W >= 1/16-K eta,                                 (BCW6)
```

where `eta` is a bounded sum of its normalized-HS word energies, then on
canonical marked microstates

```text
K eta >= 1/32-o(1).                                   (BCW7)
```

Thus the fixed superrank gap really can be converted into ordinary HS
holonomy energy; no pointwise return of the whole finite tables is needed.
The missing theorem is exactly `(BCW6)`.  The algebraic Whitehead covariance
of the physical prefix selectors does not imply it: physical corner
transport and adjoint commutant-range transport are different assertions.

