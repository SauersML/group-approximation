---
rg: 2
id: prime-power-reynolds-column-does-not-tensor-over-reduction
kind: claim
title: The depth-two Reynolds column is not a passive tensor lift of the residue-field column
artifacts:
  - research/artifacts/passive-reynolds-p5-depth-two-fiber-audit-2026-08-23.md
distinct_from:
  constrained-reynolds-column-has-a-diagonal-scalar-shadow: that isolates the scalar column and leaves the deeper-ring behavior open; this rules out the simplest fiber factorization by an exact rank certificate.
  exact-passive-jacobian-is-two-reynolds-expectations: that identifies the full noncommutative column; this compares two scalar congruence depths and certifies a rank obstruction to tensoring.
---

**ESTABLISHED.**  Write

```text
Q_1=PSL_2(F_5),              Q_2=PSL_2(Z/25Z),
H_i=<h(2)> < Q_i,            N_i=<H_i,w>.               (PRT1)
```

For the scalar columns `C_i=C_(Q_i)` of `(DSS3)`, reduction modulo `5`
does **not** identify `C_2`, even after arbitrary input and output basis
changes, with a tensor lift

```text
C_1 tensor J,
J:C^25 -> C^125.                                      (PRT2)
```

The dimensions forced by reduction are

```text
|Q_1|=60,       |H_1|=2,       dim Ind_(N_1)^(Q_1) chi=15,
|Q_2|=7500,     |H_2|=10,      dim Ind_(N_2)^(Q_2) chi=375. (PRT3)
```

Thus an input fiber has dimension `25`, whereas each regular output fiber
has dimension `125`.  Exact integer calculation gives

```text
rank(C_1)=10,                    rank(C_2)>=346.         (PRT4)
```

For the first equality, if `G_1=C_1^*C_1`, direct integer multiplication
gives

```text
G_1^2=36G_1,                    Tr(G_1)=360,             (PRT5)
```

so `rank(G_1)=rank(C_1)=10`.  At depth two, exact Gaussian elimination
modulo `1000003` gives

```text
rank_(F_1000003)(C_2^*C_2)=346.                         (PRT6)
```

A nonzero minor modulo a prime is a nonzero integer minor, proving the
real-rank lower bound in `(PRT4)`.  But `(PRT2)` would imply

```text
rank(C_2)<=rank(C_1) dim(C^25)=250,
```

a contradiction.

The algebra explains why reduction is not passive.  The kernel of
`Q_2 -> Q_1` is the additive first congruence layer

```text
sl_2(F_5),
```

of order `5^3`, while `H_2 cap ker(Q_2 -> Q_1)` is only its diagonal line,
of order `5`.  The two remaining root directions form the `25`-point input
fiber.  Conjugation by either order-three chart element moves the diagonal
line to a different line in `sl_2(F_5)`.  Hence the two Reynolds
correspondences couple the residue-field incidence and the new root
coordinates rather than acting as one common identity fiber.

The numerical Moore--Penrose infinity norms are

```text
||C_1^dagger||_infinity = 0.6666666667,
||C_2^dagger||_infinity = 1.2640000000.                 (PRT7)
```

These values are diagnostic only.  The exact result is the failure of
fiber tensorization, not divergence: one depth increase cannot prove that
the Green norms are unbounded as `k -> infinity`.  The surviving scalar
frontier is therefore a genuinely coupled prime-power Hecke estimate.
