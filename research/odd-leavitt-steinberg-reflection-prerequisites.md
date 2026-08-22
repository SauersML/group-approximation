---
rg: 2
id: odd-leavitt-steinberg-reflection-prerequisites
kind: claim
title: Odd Leavitt prefix reflections are finite Steinberg words, while connector transport has a central-lift boundary
distinct_from:
  schur-toeplitz-head-swap-exposes-the-steinberg-injectivity-fork: that audits an ascending Steinberg endomorphism and its odd-characteristic head actuator; this audits static Leavitt prefix reflection and partial-equivalence words.
  one-sided-leavitt-connector-has-sharp-overlap-payment: that proves the characteristic-two connector is an involution and gives the finite-trace HS ledger; this gives the signed odd-characteristic connector and separates elementary transport from equality of canonical Steinberg lifts.
  leavitt-prefixes-form-exponential-heisenberg-packet: that already proves the common-phase dimension theorem uniformly in the characteristic; this records that no new odd-characteristic annihilation theorem is missing.
---

Fix an odd prime `p`, let `L=L_(F_p)(1,2)`, and work at Steinberg rank
`r>=5`.

## Finite presentation

The ring `L` has its finite unital ring presentation over the finite field:
two creation and two annihilation generators with

```text
t_i s_j=delta_(ij),             s_0t_0+s_1t_1=1.        (OLR1)
```

Krstic--McCool, Theorem 3 (*Presenting `GL_n(k<T>)`*, J. Pure Appl.
Algebra 141 (1999), 175--183), as quoted and source-checked in
`atlas-relator-extraction-2026-08-15`, implies

```text
St_r(L) is finitely presented for r>=4.                  (OLR2)
```

Thus rank five is safely inside the theorem.  This input is independent of
the characteristic.  It should not be weakened to rank three, where the same
source has non-finite-presentability examples.

## The canonical reflection word and its actual size

For any idempotent `e`, put

```text
u_e=1-2e.                                                (OLR3)
```

Odd characteristic causes no invertibility problem:
`u_e^2=1`, hence `u_e^(-1)=u_e`.  In the ordinary parametric Steinberg
presentation define

```text
w_ij(u)=x_ij(u)x_ji(-u^(-1))x_ij(u),
h_ij(u)=w_ij(u)w_ij(-1).                                 (OLR4)
```

This is a six-root word, and its elementary image is

```text
diag(u,u^(-1))                                           (OLR5)
```

in coordinates `i,j`.  Therefore `h_ij(u_e)` is a bounded-root-factor
ordinary Steinberg word for every prefix idempotent `e=s_alpha t_alpha`.

There is an important metric qualification.  The symbols `x_ij(u_e)` are
not generators of one fixed finite group presentation as `alpha` varies.
At prefix depth `m`, balanced Steinberg commutator multiplication gives a
word over the fixed finite generating set of length `O(m^2)`, by
`leavitt-steinberg-quadratic-radius-pressure`.  No depth-independent word
length or filling-area bound follows from `(OLR4)`.

## The signed one-sided connector

Let `q,p` be idempotents and suppose

```text
x=pxq,        y=qyp,        xy=p,        yx=q.           (OLR6)
```

In odd characteristic the native three-root connector is the **signed**
word

```text
j_ab(x,y)=x_ab(x)x_ba(-y)x_ab(x).                        (OLR7)
```

Its elementary image on coordinates `a,b` is

```text
[[1-p, x],[-y,1-q]],                                    (OLR8)
```

with inverse `[[1-p,-x],[y,1-q]]`.  Consequently it sends the `q` support
in coordinate `b` to the `p` support in coordinate `a`.  Unlike the binary
formula, `(OLR8)` is generally not an involution; its square on the active
corners is the sign reflection.  Using the unsigned characteristic-two
formula here is therefore incorrect.

Two disjoint copies give the exact stable reflection transport.  Put

```text
J=j_13(x,y)j_24(x,y).                                    (OLR9)
```

In `E_4(L)` one has

```text
J diag(1,1,u_q,u_q) J^(-1)
   =diag(u_p,u_p,1,1).                                  (OLR10)
```

Equivalently, after the evident coordinate embeddings, the elementary
images of `J h_34(u_q)J^(-1)` and `h_12(u_p)` agree.

Equation `(OLR10)` is the exact algebraic connector statement, but it does
not automatically give equality of the two displayed **canonical lifts**
inside `St_r(L)`.  At rank at least five their quotient lies in the central
kernel

```text
ker(St_r(L)->E_r(L))=K_2(r,L).                           (OLR11)
```

Thus there are two rigorous uses:

1. work in the elementary quotient, where `(OLR10)` is literal; or
2. define the target reflection lift to be `J h_34(u_q)J^(-1)`.

Replacing that transported lift by the separately canonical word
`h_12(u_p)` requires an additional Steinberg-symbol/root calculation showing
that the element in `(OLR11)` is trivial.  Finite presentation and the matrix
identity alone do not prove it.

## Common central phase in odd characteristic

No new representation-theoretic generalization is needed.  The established
claim `leavitt-prefixes-form-exponential-heisenberg-packet` is already stated
over every finite characteristic `p`.  At depth `m` it gives `2^m`
Heisenberg pairs with the same central root `J_A` of order `p`.  On every
nontrivial central-character sector, finite Stone--von Neumann theory forces
dimension divisible by

```text
p^(2^m).                                                 (OLR12)
```

Since `(OLR12)` holds for all `m` with the same `J_A`, every
finite-dimensional unitary representation kills `J_A`.  This includes all
odd primes exactly as written; the characteristic-two involution proof is
only the special case `p=2`.

