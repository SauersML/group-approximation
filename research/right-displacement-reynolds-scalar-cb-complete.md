---
rg: 2
id: right-displacement-reynolds-scalar-cb-complete
kind: claim
title: Right-displacement decomposition makes the scalar Reynolds shadow cb-complete at exact endpoints
distinct_from:
  constrained-reynolds-column-has-a-diagonal-scalar-shadow: that extracts the diagonal restriction as a necessary scalar test; this proves that, at an exact left-regular endpoint, every off-diagonal coefficient is an identical copy and the full cb inverse has exactly the same norm.
  exact-passive-jacobian-is-two-reynolds-expectations: that identifies the exact Jacobian as two constrained expectations; this computes its complete matrix-coefficient decomposition and inverse norm.
  passive-iwahori-off-zero-cb-normal-splitting: that asks for a splitting at arbitrary operator-small passive tuples; this removes the off-diagonal obstruction only at exact congruence endpoints.
---

**ESTABLISHED; THE EXACT-ENDPOINT OFF-DIAGONAL AUDIT CLOSES.**  Let `Q` be
a finite congruence quotient and let `(R,S,X)` be an exact left-regular
half-parabolic endpoint on `H=l2(Q)`, with

```text
A=XS^2,       B=XRS,       A^3=B^3=I.
```

Write `lambda` and `rho` for the commuting left and right regular
representations.  Every matrix `Y in B(H)` has a unique right-displacement
expansion

```text
Y=sum_(z in Q) M_(f_z) rho(z),                         (RDC1)
```

where the summand `M_(f_z)rho(z)` is supported on the matrix diagonal
`(q,qz)`.  Left conjugation acts coefficientwise:

```text
Ad_(lambda(g))(M_f rho(z))=M_(L_g f)rho(z).            (RDC2)
```

Consequently the fixed-`R`, `X`-odd tangent constraints and both cubic
Reynolds rows preserve every displacement `z`.  On every one of the `|Q|`
orthogonal Hilbert--Schmidt fibers they are the *same* scalar signed-incidence
column `C_Q` from
`constrained-reynolds-column-has-a-diagonal-scalar-shadow`.  In particular,
the Hilbert-space Moore--Penrose normal inverse of the full Jacobian is the
coefficientwise lift of the scalar inverse.

There is no hidden operator-space loss in that lift.  Extend the scalar
column by zero off its fixed-`R`, `X`-odd domain and put

```text
G_Q=C_Q^dagger=(T_(1,Q),T_(2,Q)).                      (RDC3)
```

Every ingredient of `C_Q` is a finite linear combination of left
translations: the fixed-`R` and `X`-odd projections, the two order-three
Reynolds projections, and the two coordinate shifts.  Hence `C_Q^*C_Q`
belongs to the finite-dimensional left group `C^*`-algebra.  Functional
calculus for its Moore--Penrose inverse gives unique coefficients

```text
T_(j,Q)=sum_(g in Q) a_(j,g) L_g.                      (RDC4)
```

The full matrix normal inverse is therefore

```text
Ghat_Q(Y_1,Y_2)
 =sum_(j=1)^2 sum_(g in Q) a_(j,g)
      Ad_(lambda(g))(Y_j).                             (RDC5)
```

Give the two-row input the maximum norm.  Since every conjugation in
`(RDC5)` is a complete isometry,

```text
||Ghat_Q||_cb <= sum_(j,g)|a_(j,g)|.                   (RDC6)
```

On the scalar diagonal, the row operator in `(RDC4)` has exactly this
norm.  Indeed, for one chosen output point `q_0`, the points `g^(-1)q_0`
are distinct as `g` varies, and the two input functions may independently
choose the phases of all coefficients.  Thus

```text
||G_Q||_(linfinity(Q)^2 -> linfinity(Q))
 =sum_(j,g)|a_(j,g)|.                                  (RDC7)
```

The diagonal is a complete isometric subspace of the full matrix algebra,
so `(RDC6)--(RDC7)` give the exact identity

```text
boxed(
 ||Ghat_Q||_cb
 =||G_Q||_(linfinity(Q)^2 -> linfinity(Q))
 =||G_Q||_cb
).                                                     (RDC8)
```

The same identity holds after every external multiplicity amplification,
because `(RDC5)` merely tensors the conjugations with the identity.
It also controls every (not necessarily regular) representation of `Q`.
Indeed any finite-dimensional `pi` embeds into `lambda tensor I_m` for some
`m`.  The corresponding projection `P` belongs to the commutant of
`lambda(Q) tensor I_m`; hence the operator corner

```text
P B(l2(Q) tensor C^m) P
```

is reducing for all tangent projections, Reynolds rows, their adjoints,
and the Moore--Penrose inverse.  Restricting `(RDC5)` to this corner gives
the normal inverse for `pi`, with cb norm no larger than `(RDC8)`.

Therefore the exact-zero cb frontier has **no independent off-diagonal
matrix-coefficient obstruction**.  Proving the uniform scalar infinity
Green estimate for the regular arithmetic columns `C_Q` is therefore
equivalent to proving the full exact-endpoint cb normal-inverse estimate
over all quotient representations and multiplicities.  Conversely, a
scalar divergent mode already refutes the full estimate.

This does not prove the off-zero claim
`passive-iwahori-off-zero-cb-normal-splitting`.  Away from an exact endpoint,
the moving involution need not be a left translation, so the common
right-displacement decomposition need not survive.  The remaining gap is
therefore sharply split into (i) the scalar arithmetic Green estimate at
the zero locus and (ii) a nonlinear continuation of that estimate through
the operator-small passive region; off-diagonal coefficients add no third
exact-endpoint gate.
