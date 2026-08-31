---
rg: 2
id: nearby-exact-actor-transfer-collapses-shared-pauli-wall-proof
kind: route
title: Transfer the finite Pauli packet to a genuine actor and invoke compactness
target: full-shared-pauli-wall-excludes-nearby-exact-actor
requires:
  - kazhdan-stabilizer-collapses-shared-pauli-sign
  - generic-perturbations-destroy-exact-commutant-gap
---

# Nearby exact actors cannot carry the shared-Pauli wall

All Hilbert--Schmidt norms are normalized.

## 1. Transfer the stabilizer rows

Fix a genuine representation `rho:G->U(D)` satisfying (SPW2).  For
`q in Q` and `C in {A,B}`,

~~~text
norm_2(C rho(q)-rho(q) C)
 <= norm_2(C U_q-U_q C)+2 norm_2(U_q-rho(q))
 <= d_H+2 eta.                                           (1)
~~~

Put

~~~text
d_H'=d_H+2 eta.                                          (2)
~~~

Apply the Kazhdan inequality to the genuine conjugation representation
`Ad rho|Gamma`.  If

~~~text
C_0=rho(Gamma)' intersect M_D,
~~~

the trace-preserving conditional expectation onto `C_0` puts `A` and `B`
within `d_H'/kappa` of `C_0` in normalized `L^2`.  Polar completion inside
`C_0` gives unitaries `A_hat,B_hat in C_0` with

~~~text
norm_2(A-A_hat), norm_2(B-B_hat) <= a,
a=2d_H'/kappa.                                           (3)
~~~

This projection is made only after a nearby genuine actor `rho` has been
supplied.  Nothing here projects into the discontinuous literal commutant of
the approximate tuple `U`.

## 2. Transfer the off-site rows

For `r=r_l` and either `D_0=A` or `B`, (SPW2) gives

~~~text
norm_2(U_r D_0 U_r^* - rho(r) D_0 rho(r)^*) <=2 eta.         (4)
~~~

Commuting the difference in (4) past a unitary costs another factor two.
Thus every prototype row for the genuine actor has defect

~~~text
norm_2(C rho(r_l) D_0 rho(r_l)^*
           - rho(r_l) D_0 rho(r_l)^* C)
 <= d_X+4 eta=:d_X'.                                      (5)
~~~

Replace `C,D_0` in (5) by their hatted versions.  Changing the first entry
of an additive commutator costs at most `2a`, and changing the second costs
at most `2a`.  Hence

~~~text
norm_2(C_hat rho(r_l) D_hat_0 rho(r_l)^*
           - rho(r_l) D_hat_0 rho(r_l)^* C_hat)
 <= d_X'+4a.                                              (6)
~~~

## 3. Exact equivariance propagates every ordered pair

For `x=gGamma` define

~~~text
A_hat_x=rho(g) A_hat rho(g)^*,
B_hat_x=rho(g) B_hat rho(g)^*.                             (7)
~~~

Because the hatted pair lies in `rho(Gamma)'`, (7) is independent of the
coset representative and is exactly `G`-equivariant.

Every ordered pair of distinct sites is `G`-conjugate to one of the
finitely many prototypes in (SPW1).  Therefore (6) propagates, with no
word-length loss, to every distinct `x,y in X` and every hatted Pauli
choice:

~~~text
norm_2(C_hat_x D_hat_y-D_hat_y C_hat_x)
 <= d_X'+4a.                                              (8)
~~~

## 4. Finite-dimensional compactness collides two sites

The set `U(D) times U(D)` is compact.  Since `X` is infinite, for every
`epsilon>0` there are distinct sites `x,y` with

~~~text
norm_2(A_hat_x-A_hat_y)<epsilon,
norm_2(B_hat_x-B_hat_y)<epsilon.                         (9)
~~~

Use the `A_hat,B_hat` instance of (8) and replace `B_hat_y` by
`B_hat_x`.  The two replacement terms cost `2epsilon`, so

~~~text
norm_2(A_hat_x B_hat_x-B_hat_x A_hat_x)
 <= 2epsilon+d_X'+4a.                                    (10)
~~~

Exact equivariance makes the left side independent of `x`.  Letting
`epsilon->0` gives

~~~text
norm_2(A_hat B_hat-B_hat A_hat)<= d_X'+4a.                (11)
~~~

Returning both entries to `A,B` costs another `4a`:

~~~text
norm_2(AB-BA) <= d_X'+8a.                                  (12)
~~~

For unitaries,

~~~text
norm_2(ABA^*B^*-I)=norm_2(AB-BA).                        (13)
~~~

Combine (13), the definition of `d_J`, (2), (3), and (5):

~~~text
norm_2(J-I)
 <= d_J+d_X'+8a
 = d_J+d_X+4 eta+(16/kappa)(d_H+2 eta).                    (14)
~~~

This is (SPW4).

## 5. The instability wall

If `d_J,d_H,d_X<=delta` and `norm_2(J-I)>=c`, rearranging (14) gives
(SPW5).  In particular no sequence with `eta->0` and `delta->0` can retain
a separated central sign.

The trace-faithful perturbation construction starts from genuine regular
finite-quotient actors and changes each fixed actor word by `o(1)`, so its
`eta` in (SPW2) tends to zero.  Equation (14) proves that adding a
canonical full Pauli wall to those coordinates is impossible.  Generic
perturbation deletes the literal commutant, but the four cross-site
prototype rows remember enough of the nearby exact representation to restore
the compactness contradiction.

This does not settle an arbitrary hyperlinear actor tuple.  Such a tuple
need not be close to any genuine representation on the fixed packet; indeed
(SPW5) says that any full-wall model must be uniformly far.  The remaining
low-band problem must therefore exploit structure beyond nearness to an
exact actor.
