---
rg: 2
id: full-shared-pauli-rows-have-an-exact-finite-tracial-model
kind: claim
title: The negative central corner exactly realizes every shared-Pauli row in a finite tracial algebra
distinct_from:
  kazhdan-stabilizer-collapses-shared-pauli-sign: that uses compactness of a fixed finite-dimensional unitary group to collapse the sign for exact finite-dimensional actors; this proves the same rows have an exact model in a finite von Neumann algebra, so finite-dimensionality is essential.
  ozawa-sos-does-not-round-an-approximate-actor-to-its-exact-commutant: that refutes literal-commutant rounding by generic matrix perturbations; this refutes any collapse derived only from tracial positivity or a universal sum-of-squares identity, even after all Pauli rows are imposed.
  kun-thom-diagonal-pauli-common-chart-obstruction: that identifies the negative corner as a Bernoulli crossed product and isolates the common-chart converse; this turns that identification into an explicit no-go for dimension-free tracial collapse inequalities.
---

Let `G` act on a countably infinite set `X` and let

~~~text
Pi_X=P_X semidirect G
~~~

be the shared-center Pauli group, with root pairs `A_x,B_x` and common
central involution `J`.  Put `p_-=(1-J)/2 in L(Pi_X)` and give the nonzero
corner

~~~text
M_-=p_- L(Pi_X) p_-
~~~

its normalized trace.  In `M_-` the cornered group unitaries give an exact
tracial model of the entire presentation, with

~~~text
J=-1,
[A_x,B_x]=-1,
[A_x,A_y]=[A_x,B_y]=[B_x,A_y]=[B_x,B_y]=1  (x!=y),
g A_x g^*=A_(gx),   g B_x g^*=B_(gx).                    (FTC1)
~~~

In particular

~~~text
norm_2(J-1)=2.                                           (FTC2)
~~~

The base algebra in this corner is canonically

~~~text
N={A_x,B_x:x in X}'' = tensor_(x in X) M_2(C) = R,       (FTC3)
~~~

the hyperfinite `II_1` factor, and

~~~text
M_-=R crossed_product G                                  (FTC4)
~~~

for the tensor-leg action, with the action kernel retained in the crossed
product when necessary.

Consequently no dimension-free collapse inequality which follows only from
the displayed `*`-relations, tracial Cauchy--Schwarz, and positivity can
force `J=1`.  In particular, adding the Pauli rows to an Ozawa
sum-of-squares certificate cannot yield a universal finite-tracial
inequality

~~~text
norm_2(J-1) <= F(relator and Pauli defects),   F(0)=0.    (FTC5)
~~~

The exact model (FTC1)--(FTC2) would contradict it at zero defect.

This does not construct matrix microstates.  On the contrary, proving that
`M_-` is not Connes embeddable for a pinned actor/action would prove the
desired obstruction.  The theorem isolates what a successful source-specific
low-band argument must use: finite-dimensional rank/compactness or a genuine
matrix-ultraproduct restriction not expressible by universal tracial
sum-of-squares reasoning.  Hyperlinearity of the pinned shared-Pauli group
and the global nonhyperlinearity target remain **OPEN**.

DERIVATION
negative-central-corner-is-the-exact-pauli-tracial-firewall-proof
