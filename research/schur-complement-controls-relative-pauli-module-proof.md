---
rg: 2
id: schur-complement-controls-relative-pauli-module-proof
kind: route
title: Null the leading commutators and retain the Schur complement as one Pauli bit
target: schur-complement-controls-relative-pauli-module
requires:
  - boolean-predicate-is-one-rank-jump
  - predicate-rank-gate-doubles-restriction-multiplicity
---

Fix a Boolean assignment `x` and abbreviate `U=U_f(x)`.  Over `F_2` put

```text
u^T=e_s^T U^(-1),                 v=U^(-1)e_t,
P_x=p_(N+1) product_i p_i^(u_i),  Q_x=q_(N+1) product_j q_j^(v_j). (SCP4)
```

All `p` generators commute with one another and all `q` generators commute
with one another, so `P_x,Q_x` are involutions.  Their commutation exponents
with the leading packet are

```text
u^T U+e_s^T=0,                    Uv+e_t=0.                         (SCP5)
```

Hence both commute with `A_f` on the `x` sector.  If
`a=(u,1)^T` and `b=(v,1)^T`, then

```text
M_f(x)b=(0,e_s^T U^(-1)e_t)^T=(0,f(x))^T,
a^T M_f(x)b=f(x).                                                     (SCP6)
```

The packet commutator rule therefore gives

```text
P_x Q_x=(-1)^(f(x)) Q_x P_x.                                        (SCP7)
```

The `e_x` are central, orthogonal and sum to one.  Substituting `(SCP4)` in
`(SCP1)` consequently gives self-adjoint involutions commuting with `A_f`,
and summing `(SCP7)` over the selector sectors gives `(SCP2)`.

Now fix a forbidden simple block `T_(x,lambda)` with external multiplicity
`m=m_(x,lambda)`.  Restriction to `A_f` has the canonical form

```text
T_(x,lambda) tensor C^m
   = S_x tensor C^2 tensor C^m,
```

with `A_f` acting on `S_x`, `P_f,Q_f` acting as a Pauli pair on `C^2`, and
the `B_f` commutant acting as `M_m` on the last factor.  Therefore

```text
(span{P_f,Q_f,P_f Q_f}) C_B
 = I_(S_x) tensor (M_2 minus C I_2) tensor M_m.                    (SCP8)
```

The three Pauli directions are Hilbert--Schmidt orthogonal, so this space has
dimension `3m^2`.  It commutes with `A_f` and is orthogonal to the
`B_f`-commutant `I_(S_x tensor C^2) tensor M_m`; hence it lies in
`range(R_A-R_B)`.  Distinct `(x,lambda)` blocks are orthogonal.  Summing their
dimensions proves `(SCP3)`.

