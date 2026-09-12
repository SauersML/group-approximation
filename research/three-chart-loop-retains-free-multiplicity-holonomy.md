---
rg: 2
id: three-chart-loop-retains-free-multiplicity-holonomy
kind: claim
title: A three-chart Bargmann loop retains an arbitrary multiplicity holonomy
distinct_from:
  two-sl3-shell-charts-have-a-rotated-flip-escape: That proves two charts and one full transporter are phase-blind; this identifies the first three-chart gauge invariant and proves that its value is still free.
  finite-projective-sector-groupoids-have-conjugate-absorbers: That cancels finite label cocycles; this computes the unrestricted multiplicity unitary left on a closed three-chart loop.
  raw-denominator-incidence-kills-off-diagonal-shell-orbit: That uses native arithmetic section identities to pin raw branches; this leaves those identities separate and treats abstract authenticated chart transports.
---

# A three-chart Bargmann loop retains arbitrary multiplicity holonomy

Let `(P_i^a)_i`, for `a=0,1,2`, be three equal-rank PVM charts on one finite
Hilbert space.  Suppose `T_ab` is a full chart transporter from chart `b` to
chart `a`:

```text
T_ab P_i^b T_ab^*=P_i^a.                                (BGL1)
```

The triangular return on the `i`-th corner is

```text
L_i=P_i^0 T_01 P_i^1 T_12 P_i^2 T_20 P_i^0.             (BGL2)
```

It is a unitary of the corner `P_i^0`.  Under arbitrary chart gauges
`G_a` preserving the corresponding PVM, with

```text
T_ab -> G_a T_ab G_b^*,
```

the loop changes only by conjugation:

```text
L_i -> G_0 L_i G_0^*.                                   (BGL3)
```

Thus its spectrum and trace are the first gauge-invariant three-chart data.
For rank-one charts, this is the usual Bargmann phase of a triple overlap.

This invariant is not automatically pinned.  If the three charts and their
actor act on `H_label tensor M`, every transporter can be multiplied by a
unitary on the common multiplicity factor without affecting `(BGL1)` or
actor covariance.  Multiplying one edge by `1 tensor W` changes every loop
to

```text
L_i -> L_i tensor W,                                    (BGL4)
```

where `W in U(M)` is arbitrary.  Finite projective label cocycles do not
remove this freedom: conjugate doubling makes the label loop honest and
leaves precisely the factor `W`.

For two authenticated returns `L_i^(0),L_i^(1)` into the same corner, the
relative holonomy and exact Hilbert--Schmidt payment are

```text
K_i=(L_i^(0))^*L_i^(1),

||L_i^(0)-L_i^(1)||_2^2
  =2 tau(P_i^0)-2 Re tau(K_i),                           (BGL5)

||(L_i^(0)+L_i^(1))/2||_2^2
  =tau(P_i^0)/2+(1/2)Re tau(K_i).                        (BGL6)
```

The scalar `tau(K_i)` is invariant under every chart gauge, but `(BGL4)`
shows that fullness and covariance allow it to be any finite-dimensional
unitary trace, hence asymptotically any point of the closed unit disk.

## Explicit SL3 shell realization

On `l^2(Omega times Omega)`, use the diagonal `SL_3(Z)` actor, coordinate
flip `F`, and rotations `U_t=cos(t)I+i sin(t)F` from
`two-sl3-shell-charts-have-a-rotated-flip-escape`.  For three generic
parameters `t_0,t_1,t_2`, put

```text
P_i^a=U_(t_a)Q_iU_(t_a)^*,
T_ab=U_(t_a)U_(t_b)^*.                                  (BGL7)
```

The charts are pairwise noncommuting, all transports and actor covariance
are exact, and the triangle telescopes to the identity.  After tensoring by
`M`, replace one edge by `T_ab tensor W`.  This realizes the arbitrary loop
`W` exactly.  Choosing cyclic regular shifts of growing order gives canonical
trace camouflage for the free loop word while retaining all chart data.

Therefore a three-chart loop, or even two full returns into the same corner,
does not by itself yield a dimension-free trace-square payment.  The minimal
remaining incidence must **compare** the returns through a relation that
controls `(BGL5)` or `(BGL6)`: for example, one additive same-block entry in
which both paths occur coherently.  In the arithmetic lane, the only current
candidate source of such control is a raw denominator-section identity or a
mixed-root relation that ties the multiplicity gauges of two distinct
triangles.  Those native identities are not asserted by this abstract
countermodel.

The first native section rectangle now has an exact dichotomy.
`sl3-raw-weyl-rectangle-pins-only-equal-rank-corners` shows that the literal
`s_12` and `s_23` denominator paths have trivial relative loop before
decoding, and that equal-rank source fullness transfers this pinning with an
exact Gram formula.  The present 42-shell atom has the wrong rank for that
interface, so the abstract multiplicity escape remains available on the
decoded carrier.
