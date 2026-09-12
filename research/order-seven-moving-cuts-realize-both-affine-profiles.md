---
rg: 2
id: order-seven-moving-cuts-realize-both-affine-profiles
kind: claim
title: Exact order-seven moving cuts separately realize both incompatible affine selector profiles
artifacts:
  - research/order-seven-affine-profile-gauge-model-proof.md
distinct_from:
  moving-order-seven-stage-gauges-have-coboundary-drift: that allows arbitrary stage involutions with trivial cyclic product; this realizes exactly the two positive-sign fractions forced by the quarter and eighth native selector rows and includes their exact source/output rank equations.
  two-shared-gauge-selector-rows-have-an-affine-rank-obstruction: that forbids the two profiles when their reservoir involutions are conjugate on one carrier; this shows that an exact order-seven moving-cut telescope does not supply that conjugacy.
  six-ungauged-moving-squares-lock-seven-gauges: that kills the drift after independently authenticated ungauged parallel bridges are supplied; this model shows why using the native head itself as the parallel bridge leaves the square tautological.
---

**ESTABLISHED EXACT MOVING-GAUGE MODEL.**  There are two finite cyclic
moving-cut packets, one for each native selector row, with zero relation and
boundary defect, such that

```text
row 1: (r,q,theta)=(1/2,1/4,1/2),
row 2: (r,q,theta)=(1/4,1/8,5/6).                     (OAP1)
```

For row 1 take a reservoir of dimension `28`, partitioned into four
seven-cycles of a permutation `U_1`.  Let the involution `D_1` be negative
on respectively `4,4,4,2` coordinates of those cycles.  For row 2 take a
reservoir of dimension `48`, consisting of six seven-cycles of `U_2` and
six fixed coordinates.  Let `D_2` be negative on respectively
`2,2,2,2,0,0` coordinates of the cycles and positive on the six fixed
coordinates.  Then

```text
theta(D_1)=14/28=1/2,          theta(D_2)=40/48=5/6,  (OAP2)
product_(k=0)^6 U_i^kD_iU_i^(-k)=1.                  (OAP3)
```

The last identity holds because every seven-cycle contains an even number
of negative coordinates.  Put `D_(i,k)=U_i^kD_iU_i^(-k)`.  On seven equal
moving stage spaces let the native head carry stage `k` to `k+1` as

```text
C_(i,k)=M_i tensor D_(i,k),                            (OAP4)
```

where `M_i` is any fixed order-seven label unitary.  Equations `(OAP3)` and
`M_i^7=1` make the global head have exact seventh power one and make all
moving boundaries zero, while `D_(i,0)` is nontrivial.

Let `C_q` be a label reflection with negative fraction `q`.  The controlled
output `C_q tensor D_(i,0)` has negative fraction

```text
Phi_q(theta)=1-q+(2q-1)theta.
```

Equations `(OAP1)--(OAP2)` give exactly `1/2` in row 1 and `1/4` in row 2.
Thus source reflections of the prescribed fractions are unitarily
conjugate to the two controlled outputs.  Each native affine row and each
order-seven moving telescope is separately exact, but their initial gauges
have different positive spectral fractions and cannot be conjugate.

Using the native transition itself as a parallel bridge does not add an
equation: setting `R_(i,k)=C_(i,k)` makes

```text
C_(i,k+1)R_(i,k)=R_(i,k+1)C_(i,k)                     (OAP5)
```

an identity.  By contrast the genuinely ungauged choice
`R_(i,k)=M_i tensor 1` satisfies `(OAP5)` exactly only when
`D_(i,k+1)=D_(i,k)`.  Hence the ungauged typing in
`el20-six-moving-coefficient-square-bridges` is precisely the additional
content needed to rule out this model.

This is a finite gauge-layer countermodel to deriving common native row
authentication from the two actual seventh-power relations, zero moving
boundary, correct affine ranks, and head-powered mixed squares alone.  It
is not asserted to be a representation of the full EL20 coefficient
presentation, so a concrete six-bridge EL20 word table could still exclude
it.  No Property T, Kazhdan input, canonical trace, or literature theorem
is used.

DERIVATION
order-seven-affine-profile-gauge-model-proof
