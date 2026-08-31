---
rg: 2
id: kt-ab-compressors-have-one-backward-commutant-edge
kind: claim
title: The two Kun--Thom compressors have one backward commutant edge
artifacts:
  - research/kt-ab-commutant-cocycle-and-pointed-martingale-no-go-proof.md
distinct_from:
  kt-two-positive-compressors-generate-full-obstruction: That proves the pair generates the full actor and has a global permutation incompatibility; this computes the operator-algebraic correspondence induced by the pair and shows its two first ranges coincide.
  strict-compressor-mixed-return-collapses-shared-pauli-sign: That gives a conditional low-band estimate using one off-site mixed return; this proves that the second named positive compressor supplies no independent first-step martingale projection with which to bound that leakage.
  kt-regular-mask-removes-trace-faithfulness-from-commutant-wall: That embeds arbitrary multiplicity defects behind a regular trace mask; this identifies the exact one-endomorphism/one-automorphism cocycle which such a defect must satisfy.
---

**ESTABLISHED STRUCTURAL NO-GO; THE GLOBAL ROUTE REMAINS OPEN.**

Use the Kun--Thom actor with

~~~text
Gamma = EL_r(F_q[x_1,x_2,x_3]),
B = I+E_12,
C e_i = e_(i+1),
A = C B.
~~~

Let `sigma:G->U(M)` be any representation in a finite tracial von
Neumann algebra, including a trace-faithful representation in a matrix
tracial ultraproduct, and put

~~~text
R = sigma(Gamma)' intersect M.
~~~

For a positive compressor `g` define its backward commutant
endomorphism

~~~text
Phi_g(x)=sigma(g)^* x sigma(g),       x in R.
~~~

Then, with `Theta=Phi_C`,

~~~text
Theta is an automorphism of R,
Phi_A = Phi_B o Theta,
Phi_A(R)=Phi_B(R)=sigma(B^(-1) Gamma B)' intersect M.    (KCE1)
~~~

Equivalently,

~~~text
A^(-1) Gamma A = B^(-1) Gamma B.                        (KCE2)
~~~

Thus the two positive compressors do not give two backward subfactor
directions at the root. They give one trace-preserving endomorphism
`Phi_B` and one order-three source automorphism `Theta`. If
`E_A,E_B:R->R` denote the trace-preserving conditional expectations
onto the two ranges, then

~~~text
E_A=E_B,
dist_2(x,Phi_A(R))=dist_2(x,Phi_B(R))                    (KCE3)
~~~

for every `x in R`. In correspondence language, the
`A`-correspondence is the `B`-correspondence with its source
label pulled back by `Theta`; it is not a second independent
correspondence.

This identity is already pointed and stable in normalized Hilbert--Schmidt
microstates. If contractions `x_n` represent `x` and actor lifts satisfy
`||u_(A,n)-u_(C,n)u_(B,n)||_2->0`, then

~~~text
||u_(A,n)^* x_n u_(A,n)
  -u_(B,n)^* u_(C,n)^* x_n u_(C,n) u_(B,n)||_2 -> 0.    (KCE4)
~~~

No adjoint-rank normalization occurs in this estimate.

There is also a concrete matrix-ultraproduct obstruction to extracting more
from the single range. Put `V=<Gamma,B>` and

~~~text
W_B=(direct_sum_(V/Gamma) C_2) rtimes V.
~~~

The established one-compressor theorem makes `W_B` sofic. In its
canonical permutation-ultraproduct representation, the root lamp projection

~~~text
p=(1+z_Gamma)/2
~~~

has `||p||=1`, lies exactly in `R`, and satisfies

~~~text
dist_2(p,Phi_B(R)) >= 1/(2 sqrt(2)).                     (KCE5)
~~~

Hence property (T) of `Gamma`, exact compressor covariance, a
uniform operator-norm bound on the chosen vector, and even canonical mixed
traces do not control the first martingale difference. A successful
two-compressor proof must use the noncommuting transport of `Theta` through
later copies of `Phi_B`, or an equivalent named mixed-return relation.
It cannot sum two root-range Poincare inequalities.

The model proving (KCE5) is only the one-compressor restriction. Extending
its pointed lamp through the full `C`-holonomy is precisely the
multi-compressor hyperlinearity problem. Nothing here constructs a
hyperlinear model of the full Kun--Thom wreath, so the non-hyperlinear-group
root remains **OPEN**.

DERIVATION
kt-ab-commutant-cocycle-and-pointed-martingale-no-go-proof
