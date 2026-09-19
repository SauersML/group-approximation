---
rg: 2
id: full-moving-hecke-q-kernel-profile-proof
kind: route
title: Build the adjacent-character monomial model and compute its full-source endpoint kernel
target: full-moving-hecke-packet-retains-q-kernel-profile
requires:
  - endpoint-order-five-return-leaves-full-hecke-fine-sign-free
  - native-j1-extension-gives-gl5-but-only-second-whitehead-gram
---

Let `E` be the direct sum of the eight projective summands in `(FMQ5)`.
Every named generator preserves `E`.  Prefix cancellation identifies its
restriction with an ordinary binary matrix.  The ten `L_0` arrows are

```text
q5->q6, q4->q5, q2->q4, q2->u2, q4->u3,
q2->u3, u1->u3, u1->q5, u1->q6, u2->q6,              (1)
```

with the first three negative.  Their closure has order `8192` and carries
the stated character.  On the five middle nodes,

```text
W=(u2 u4),       J1=(u1 u2),
M=(u2 u3) x_(u3,q5)(1) x_(q5,u2)(1).                 (2)
```

Conjugating the four row-six roots `(C3,s,t,s')` gives

```text
M:(C3,s,t,s')->(C3t,t,C3s,s'),
W:(C3,s,t,s')->(C3,s',t,s),                           (3)
```

so `(2)` is the same literal actor, not a replacement finite model.

Write the abelianization of the unipotent radical's adjacent layers as

```text
(x,b,a) in F_2 x F_2^5 x (F_2^5)^*.
```

For `(r,s) in Omega_epsilon`, define

```text
chi_(r,s)(x,b,a)=(-1)^(x+r(b)+a(s)).                  (4)
```

The `GL_5` action in `(FMQ7)` transports these characters, so diagonal
action by `(4)` and permutation action by `(FMQ7)` define an exact unitary
representation on `ell^2(Omega_epsilon)`.  The non-adjacent radical layers
act trivially.  Therefore the ten generators in `(1)`, and the complete
actors in `(2)`, satisfy every relation inherited from the literal
parabolic.

Use `epsilon=0`.  The `lambda_0` eigenspace is computed using only ten
involutory equations.  The negative equations for `C2,C3` say

```text
r_0=s_0=1.                                             (5)
```

The positive adjacent equations for `f,w,s` say

```text
r_3=0,                s_1=s_2=0.                       (6)
```

The skip roots `d,k` impose nothing in `(4)`.  Finally the two positive
Levi roots

```text
c:x_(u1,u3)(1),       v:x_(u1,u0)(1)                  (7)
```

pair the surviving states.  Solving `(5)--(7)` together with `r(s)=0`
gives exactly the four two-point components in `(FMQ8)`.  Their equal-sign
sums are an orthogonal basis of `Q ell^2(Omega_0)`, proving `rank(Q)=4`.

Apply `W=(u2 u4)` to those four sums and project back to the list `(FMQ8)`.
All four leave the list entirely, because their vector coordinate has bit
`u4` but not bit `u2`.  Hence the compression matrix is zero, proving
`(FMQ3)--(FMQ4)`.  Repeating the same finite calculation on `Omega_1`
gives the companion ranks `12` and `8`.

`experiments/full_q_moving_gl8_permutation_audit.py` checks the binary
restriction `(1)--(3)`, closes the exact signed group of order `8192`,
constructs both the `465`- and `496`-state orbits, solves the signed
component equations, and prints respectively the zero `4 x 4` Gram and the
rank-eight `12 x 12` Gram.  It runs through MSI only and completes in under
ten seconds.
