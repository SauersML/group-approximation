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

There is also an exact operator-space form.  On Hilbert--Schmidt operators put

```text
mathcal P_i(X)=P_i X P_i,       i in {6,K}.              (A4-C3-5)
```

After vectorization, the compression
`mathcal P_K mathcal P_6 mathcal P_K` is the tensor product of
`P_KP_6P_K` with its conjugate.  Its eigenvalues are the pairwise products of
those in `(A4-C3-2)`.  Off the common scalar operator its norm is still at
most `lambda_*` (one factor may be the constant eigenvector).  Hence every
`Z in P_K L^2 P_K` orthogonal to the common scalar satisfies

```text
||Z-P_6 Z P_6||_2^2 >= gamma_* ||Z||_2^2.              (A4-C3-6)
```

Thus the continuous collision line holonomy is not invisible to the other
packet component: once the **same common-frame defect vector** is known to
lie in the `K` line carrier and is tested by the `H_6` line carrier, it pays
the explicit dimension-free gap `(A4-C3-3)`.  No spectral estimate remains
to be guessed at this stage.

The exact remaining common-`U` equation can be written without choosing any
factorization witnesses.  For `K=<r,s>` define its trivial/sign idempotents

```text
E_K^+=(1/6)(1+r+r^2)(1+s),
E_K^-=(1/6)(1+r+r^2)(1-s).                              (A4-C3-7)
```

Let `b_0` be the repeated first-chart involution in collision `19243`, and
write all matrices in the reference-aligned common frame.  The canonical
collision line-angle operator is

```text
Z(U)=E_K^- U^* rho(b_0) U E_K^+.                       (A4-C3-8)
```

In the continuous dihedral family of
`atlas-19243-has-continuous-regular-s3-line-holonomy`, `(A4-C3-8)` is exactly
the off-diagonal sine of the free reflection angle.  It lies in
`P_K L^2 P_K` and is orthogonal to the common scalar because it maps the
trivial sector to the sign sector.

Consequently the last gauge-free compression estimate required from the
fourteen shifted common-`U` packet equations is

```text
||Z(U)-P_6 Z(U) P_6||_2
 <= C [sum_j dist_2(U,D_j)^2+||q_19243(U)-1||_2^2]^1/2 (A4-C3-9)
```

Combining `(A4-C3-9)` with `(A4-C3-6)` controls the continuous angle
quantitatively.  Independent witnesses `U=X_jRY_j` cannot define `Z`; formula
`(A4-C3-8)` shows exactly why retaining their shared literal `U` is essential.
The proof of `(A4-C3-9)`, or an exact common-`U` matrix countermodel to it, is
the remaining coupling problem.

The fixed subgroup bridge is now explicit.  By
`atlas-collision-involution-is-an-a4-bridge-to-h6`, the repeated collision
involution and `C_6` generate a regular `A4`, so the `1` versus `1/3` line
split canonically exposes the transported carrier `P_6(U)=U^*P_6U` with gap
`2/3`.  This does not prove `(A4-C3-9)`: its left side uses the fixed `P_6`.
It reduces the missing identity to transporting that moving regular-`A4`
carrier to the fixed one on `Z(U)` using the literal common `H_6` rectangle
equations.
