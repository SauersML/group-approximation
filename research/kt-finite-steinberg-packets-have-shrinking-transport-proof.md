---
rg: 2
id: kt-finite-steinberg-packets-have-shrinking-transport-proof
kind: proof
title: Exact intermediate Steinberg models realize every collision packet only on shrinking support
proves:
  - kt-intermediate-actor-cannot-extract-positive-coefficient-transport
requires:
  - kt-canonical-lamp-collision-forces-vanishing-intertwiner
  - kt-single-laurent-return-has-profinite-coset-models
---

# Exact intermediate Steinberg models realize every collision packet only on shrinking support

## 1. Exact coherent models

Use

~~~text
S=F_2[x_1,y,x_3],
P=F_2[x_1,x_1y,x_3],
H=EL_3(S),
Gamma=EL_3(P),
W_H=(direct_sum_(H/Gamma) C_2) rtimes H.
~~~

For the truncations

~~~text
T_N=S/(x_1,y,x_3)^(N+1),
Q_N=EL_3(T_N),
Gamma_N=EL_3(P_N),
W_N=(direct_sum_(Q_N/Gamma_N) C_2) rtimes Q_N,
~~~

the quotient maps `W_H->W_N` separate every fixed element and every fixed
finite coset table. The pulled-back left regular representations
`lambda_N` are genuine representations of the **entire** group `W_H`.
In particular every Steinberg relation in `H`, every stabilizer row, and
every intermediate-ring actor word holds exactly.

For every fixed nonidentity `g in W_H`, its image in `W_N` is
nonidentity for all large `N`, so

~~~text
tr(lambda_N(g))=0.
~~~

Thus `lambda_N` converges to the canonical character of `W_H`.

## 2. An arbitrary finite collision packet

Let

~~~text
V=S/P,                   X[f]=[x_1f].
~~~

Choose `r` independent fixed kernel vectors, for example

~~~text
eta_j=[x_1^(j-1)y^j],          1<=j<=r,
~~~

and put `eta_0=0`. For all sufficiently large `N`, the sites

~~~text
e_12(eta_0)Gamma_N,...,e_12(eta_r)Gamma_N
~~~

are distinct, while all lie in the fiber `X^(-1)(0)`.

Let `z_j` be the corresponding lamp involutions in the regular
representation of `W_N`, and take the target lamp `w=z_0`. Set

~~~text
h_j=z_0z_j,
E_r=2^(-r) product_(j=1)^r(I+h_j).                         (1)
~~~

The nontrivial products of the `h_j` are nonidentity lamp words, hence
have regular trace zero. Therefore

~~~text
tr(E_r)=2^(-r).                                            (2)
~~~

Moreover `E_r h_j=E_r`, so with `T_r=E_r`,

~~~text
wT_r=T_r z_j,              0<=j<=r,                        (3)
T_r^*T_r=E_r,
tr(T_r^*T_r)=2^(-r).                                      (4)
~~~

Thus every finite coefficient-collision table is exactly satisfiable
inside an exact canonical finite model. Its support is exponentially small
in the collision rank.

## 3. Optimality and a diagonal escape

The Fourier-expectation inequality from
`kt-canonical-lamp-collision-forces-vanishing-intertwiner` applies with
`epsilon=delta=0`. It says that **every** partial isometry `T` satisfying
(3) obeys

~~~text
tr(T^*T)<=2^(-r).                                         (5)
~~~

Hence (4) is optimal; a different polar factor, multiplicity choice, or
internal block unitary cannot retain more support.

Choose `r_N->infinity` slowly enough that the first `r_N` sites and
all desired finite word tables remain separated at level `N`. Equations
(3)--(4) then give a single sequence such that every fixed collision
covariance is eventually exact while

~~~text
tr(T_(r_N)^*T_(r_N))=2^(-r_N)->0.                          (6)
~~~

The actor and all intermediate Steinberg relations remain exact throughout,
and the ambient group character remains canonical.

## 4. Extraction consequence

Suppose an actor-to-carrier theorem used only canonical trace and the
relations of

~~~text
H=<Gamma,e_12(y)>=EL_3(F_2[x_1,y,x_3])
~~~

to produce partial transports with support bounded below by a constant
`q_0>0` and errors tending to zero on every fixed coefficient-collision
row. Apply it to the exact models above. For fixed `r` larger than
`log_2(q_0^(-1))`, inequality (5) contradicts the asserted support.

Therefore no such extraction theorem exists at the coherent intermediate
Steinberg level. The finite-packet escape is explicit and unique in scale:
solve rank `r` exactly on support `2^(-r)` and let that support vanish.

This does not refute an extraction theorem which genuinely uses Laurent
relations outside `H` or the simultaneous external Kun--Thom compressors.
Those are precisely the relations absent from the profinite intermediate
models. Any positive actor-to-carrier result must identify where those extra
relations prevent the optimal shrinking-support construction; actor
multiplicativity and Steinberg coherence inside `H` cannot do it.
