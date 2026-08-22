---
rg: 2
id: atlas-a4-two-c3-line-carriers-have-exact-angle-gap
kind: claim
title: The two rank-three A4 line carriers have exact connection gap (9 minus square-root 17) over 18
artifacts:
  - experiments/atlas_a4_c3_line_connection_spectrum.py
distinct_from:
  atlas-19243-has-continuous-regular-s3-line-holonomy: that identifies the collision-blind trivial/sign line sector; this proves the other packet S3 sees that sector with a fixed positive angle in the common GL3(2) frame.
  atlas-a4-rank-three-core: that proves the two S3 packet components generate GL3(2); this computes the full principal-angle spectrum of their C3-fixed line carriers in the regular representation.
  atlas-a4-rank-three-core-commutant-collapse: that asks the packet and collision equations to put the relative unitary in the GL3(2) commutant; this supplies the exact finite connection coefficient once a common defect vector is exposed by both components.
---

Let `H_6,K ~= S3` be the two components of the fourteen-word A4 core and

```text
H=<H_6,K> ~= GL3(F2).
```

Let `C_6 triangleleft H_6` and `C_K triangleleft K` be their order-three
subgroups.  On `Reg(H)` let

```text
P_6=(1/3)sum_(g in C_6) lambda(g),
P_K=(1/3)sum_(g in C_K) lambda(g).                       (A4-C3-1)
```

These are exactly the projections onto the `triv direct_sum sign` line
sectors of the two `S3` restrictions.  The complete spectrum of
`P_K P_6 P_K` on `ran(P_K)` is

```text
0                                      multiplicity 7,
1                                      multiplicity 1,
2/9                                    multiplicity 12,
4/9                                    multiplicity 6,
1/3 +/- 2sqrt(2)/9                     multiplicity 8 each,
1/2 +/- sqrt(17)/18                    multiplicity 7 each. (A4-C3-2)
```

The eigenvalue-one line consists of the constant vectors, because
`<C_6,C_K>=H`.  Therefore the largest nontrivial squared principal cosine is

```text
lambda_*=1/2+sqrt(17)/18,
gamma_*=1-lambda_*=(9-sqrt(17))/18.                    (A4-C3-3)
```

In particular, if `z in ran(P_K)` is orthogonal to the constants, then

```text
||(1-P_6)z||_2^2 >= gamma_* ||z||_2^2.                 (A4-C3-4)
```

The same constant holds in `Reg(A8)|_H=120 Reg(H)`, under every external
amplification, and for Hilbert-space-valued copies of the connection.

Thus the continuous collision line holonomy is not invisible to the other
packet component: once the **same common-frame defect vector** is known to
lie in the `K` line carrier and is tested by the `H_6` line carrier, it pays
the explicit dimension-free gap `(A4-C3-3)`.  No spectral estimate remains
to be guessed at this stage.

The exact remaining common-`U` equation is now isolated.  Starting from the
shifted factorizations `U=X_j R Y_j`, one must show that the dihedral
trivial/sign angle produced by collision is represented by a single vector
`z` to which an `H_6` packet residual bounds `||(1-P_6)z||_2`.  Equation
`(A4-C3-4)` would then bound the nonconstant angle by that residual.  Separate
tree gauges do not provide such a common `z`; retaining the literal common
`U` in all fourteen factorizations is essential.

