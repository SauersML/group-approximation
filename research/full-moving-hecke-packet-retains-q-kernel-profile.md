---
rg: 2
id: full-moving-hecke-packet-retains-q-kernel-profile
kind: claim
title: The complete moving Hecke packet has an exact zero-QWQ profile
artifacts:
  - research/full-moving-hecke-q-kernel-profile-proof.md
  - experiments/full_q_moving_gl8_permutation_audit.py
distinct_from:
  endpoint-order-five-return-leaves-full-hecke-fine-sign-free: that gives a two-dimensional profile for the pointwise return relations only and explicitly does not extend it across the moving actor; this constructs one exact representation of the complete literal L0, W, M, J1 packet.
  native-j1-extension-gives-gl5-but-only-second-whitehead-gram: that computes a one-sided support bound on the coarser p2 source from the GL5 stabilizer; this keeps the four additional roots of the actual Hecke source Q and makes its W compression identically zero.
  endpoint-whitehead-signed-source-has-only-relative-hecke-overlap: that computes the canonical regular-trace overlap and a flag-interface fence; this supplies a finite complete-moving-packet zero-Gram profile rather than only the static endpoint relations.
---

**ESTABLISHED COMPLETE-PACKET ZERO-GRAM FENCE.**  Put

```text
u_0=q@5, u_1=e_1@7, u_2=e_2@8, u_3=e_3@9, u_4=e_3@2
```

and retain the complete signed Hecke source

```text
L_0=<C_1,C_2,C_3,d,f,k,c,v,w,s>,
Q=e_(L_0,lambda_0).                                  (FMQ1)
```

There is an exact `465`-dimensional signed-permutation representation of the
literal subgroup

```text
<L_0,W,M,J_1>,             M=J_2B_3A_2,              (FMQ2)
```

in which

```text
rank(Q)=4,                QWQ=0.                       (FMQ3)
```

Consequently

```text
tr((QWQ)^*(QWQ))=0,             rank(Q)=4.             (FMQ4)
```

Thus the complete moving packet does **not** force positive scalar Gram
mass for the full Hecke source.  This is stronger than the earlier scoped
return profile: both native Whiteheads, the order-seven head, every one of
the ten signed `L_0` generators, and all their literal relations act on one
common finite Hilbert space.

The model comes from the exact eight-projective-summand chart

```text
q@2, q@4, q@5, q@6, e_1@7, e_2@8, e_3@9, e_3@2.       (FMQ5)
```

On the middle five summands the actor is the literal `GL_5(F_2)` of
`native-j1-extension-gives-gl5-but-only-second-whitehead-gram`.  The other
three summands turn this into the four-block parabolic with block sizes
`1,1,5,1`.  Quotient its unipotent radical by the non-adjacent layers and
fix the nontrivial character on the first scalar edge.  The remaining
nonzero vector/covector characters split into the two `GL_5(F_2)` orbits

```text
Omega_epsilon={(r,s) in (F_2^5\{0})^* x (F_2^5\{0})
               : r(s)=epsilon},
|Omega_0|=31*15=465,          |Omega_1|=31*16=496.    (FMQ6)
```

For `g in GL_5(F_2)` the monomial basis action is

```text
(r,s) -> (r g^(-1),g s).                              (FMQ7)
```

Use `Omega_0`.  The adjacent radical coordinates act by their character
signs.  In the bit order `(u_0,u_1,u_2,u_3,u_4)`, the four signed `L_0`
components are the two-point sums indexed by

```text
{17,19}x{17}, {17,19}x{25},
{21,23}x{17}, {21,23}x{25}.                           (FMQ8)
```

Here `{a,b}x{c}` denotes the vector supported at `(a,c),(b,c)` with equal
signs.  The endpoint word `W` swaps bits `u_2,u_4`.  Every vector in
`(FMQ8)` has `s_2=0,s_4=1`; after applying `W` it has `s_2=1,s_4=0`, which
violates the positive `s` equation defining `Q`.  Hence all four basis
vectors are killed by the `Q`-compression, proving `(FMQ3)--(FMQ4)`.

For comparison, the companion orbit `Omega_1` has `rank(Q)=12` and
`rank(QWQ)=8`.  It shows that the zero result is orbit-sensitive, while the
`Omega_0` representation is the decisive exact profile.

This does not claim that the model extends to all of `St_20(R)`.  It proves
the exact safe conclusion needed at this frontier: adding `J_1` and the
complete moving `GL_5` actor to the full signed source still cannot descend
the coarser `p_2` one-third bound to `Q`.  It does not refute `(APG1)` for
some different authenticated native rectangular transports; it refutes the
specific attempt to obtain `(APG1)` by taking the full-source endpoint Gram
`QWQ`.  A positive proof must use an additional native occurrence outside
`(FMQ2)` which pays the four zero-Gram states.

No Property `(T)`, canonical trace, literature input, local computation, or
Lean compilation is used.

DERIVATION
full-moving-hecke-q-kernel-profile-proof
