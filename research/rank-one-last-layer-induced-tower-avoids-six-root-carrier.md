---
rg: 2
id: rank-one-last-layer-induced-tower-avoids-six-root-carrier
kind: claim
title: A rank-one last-layer induced tower avoids the six-root carrier
invalidates:
  - six-root-scalar-transfer-then-canonical-target-vanishing
distinct_from:
  six-weyl-sign-proper-moments-miss-top-parity: that is an abstract Weyl-covariant six-sign model agreeing with all proper moments; this is a genuine finite congruence representation of SL_3 with full last-layer conjugation covariance and canonical fixed-word limiting character.
  canonical-trace-does-not-control-moving-root-orthogonality: that gives an abelian clock model showing the general moving-word problem; this realizes the obstruction in the precise last congruence layer and computes the surviving sixfold parity coefficient.
---

**ESTABLISHED GENUINE-CONGRUENCE NO-GO.**  For `a>=2` put

```text
Q_a=SL_3(Z/2^a Z),
N_a=ker(Q_a -> Q_(a-1)) ~= (sl_3(F_2),+).
```

For `Y in sl_3(F_2)` define

```text
chi_Y(1+2^(a-1)X)=(-1)^tr(YX).
```

Take `Y=E_12` and

```text
pi_a=Ind_(N_a)^(Q_a) chi_Y,                            (RLT1)
```

pulled back to `SL_3(Z)`.  Since `N_a` is normal, the induced character
vanishes off `N_a`.  Every fixed nonidentity integral matrix lies outside
`N_a` for all sufficiently large `a`; hence `(pi_a)` has the canonical
fixed-word limiting character.

On `N_a`, the normalized character is the uniform average over the
`Q_a`-conjugacy orbit of `chi_Y`.  Modulo two this orbit consists of the 21
rank-one nilpotents

```text
Y=uv^T,   u,v in F_2^3\{0},   v^T u=0.                (RLT2)
```

Let `u_ij=x_ij(2^(a-1))` for the six ordered roots.  On the character
labelled by `Y`, its sign is `(-1)^(Y_(ji))`.  The all-negative six-root atom
would require every off-diagonal entry of `Y` to equal one.  No rank-one
trace-zero `3 x 3` matrix over `F_2` has this property: all three nonzero
rows would have to agree, forcing the all-ones matrix, whose trace is one.
Therefore the all-negative carrier projection has normalized trace exactly
zero in every `pi_a`.

The missing full parity coefficient is nevertheless macroscopic.  The word

```text
r_a=product_(i!=j) u_ij
```

pairs with `Y=uv^T` by

```text
(-1)^(v^T(J+I)u)=(-1)^((1^T u)(1^T v)),               (RLT3)
```

because `v^Tu=0`.  Exactly six of the 21 incident pairs have both coordinate
sums odd: `u` is one of the three basis vectors and `v` is one of the other
two.  Hence

```text
tr_(pi_a)(r_a)=(15-6)/21=3/7.                         (RLT4)
```

This tower shows that full last-layer covariance and canonical convergence
on every fixed word do not recover the six-root all-negative carrier.  It
also separates scalar transport from the endpoint needed by the arithmetic
proof.  Even if a supported intertwiner transported `(RLT4)` to the
staggered word

```text
s_a=x_21(2^(a-2)) x_32(2^(a-2)) x_31(2^(a-3)),
```

one would obtain only `tr(s_a) approximately 3/7`.  The word `s_a` moves
with the conductor, so canonical fixed-word convergence supplies no
contradiction.  The surviving gate must control a common `h`-compatible
reservoir or charge first exit; scalar trace transfer alone is insufficient.

DERIVATION
induce-rank-one-coadjoint-character-over-last-kernel
