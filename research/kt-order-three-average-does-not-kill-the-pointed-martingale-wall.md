---
rg: 2
id: kt-order-three-average-does-not-kill-the-pointed-martingale-wall
kind: claim
title: Order-three averaging leaves the Kun--Thom pointed martingale wall untouched
artifacts:
  - research/kt-minimal-cyclic-holonomy-and-explicit-laurent-return-proof.md
distinct_from:
  kt-ab-compressors-have-one-backward-commutant-edge: That proves the two length-one ranges coincide and gives a one-compressor matrix-ultraproduct wall; this writes the first noncommuting cyclic holonomy, tests the proposed order-three averaging, and identifies an explicit Laurent mixed return.
  strict-compressor-mixed-return-collapses-shared-pauli-sign: That proves a conditional abstract estimate for an unspecified element outside the compressed subgroup; this identifies a fixed elementary Laurent word and its cyclic orbit in the actual Kun--Thom presentation.
---

**ESTABLISHED TRACIAL NO-GO; MATRIX APPROXIMABILITY REMAINS OPEN.**

Use

~~~text
B_0=B=I+E_12,
C e_i=e_(i+1),
B_-=C^(-1) B C=I+E_31,
D=I+E_32.
~~~

The first noncommuting cyclic holonomy is the fixed positive-semigroup
identity

~~~text
B_- B_0 = D B_0 B_-.                                    (KHL1)
~~~

For `R=sigma(Gamma)' intersect M`,
`Phi_g=Ad(sigma(g)^*)|R`, and `Theta=Phi_C`, it becomes

~~~text
Phi_(B_-) = Theta o Phi_B o Theta^(-1),
Phi_B o Phi_(B_-)
 =Phi_(B_-) o Phi_B o Phi_D.                             (KHL2)
~~~

Thus the earliest branch beyond the common length-one range is a
Steinberg holonomy defect, not a second Poincare direction.

Order-three averaging does not control that defect. In the exact canonical
binary wreath

~~~text
W=(direct_sum_(G/Gamma) C_2) rtimes G
~~~

inside `L(W)`, let `p=(1+z_Gamma)/2` be the root lamp
projection. Then

~~~text
p in R,             Theta(p)=p,
dist_2(p,Phi_B(R)) >= 1/(2 sqrt(2)).                     (KHL3)
~~~

Consequently no inequality of the form

~~~text
dist_2(x,Phi_B(R))
 <=K( max_(s in S_Gamma)||[x,sigma(s)]||_2
       +||x-Theta(x)||_2 )                               (KHL4)
~~~

can hold for all operator-norm-one contractions in finite tracial models,
for any finite `K` and any Kazhdan set `S_Gamma`. Both terms on the
right vanish at `x=p` while the left side has the displayed fixed lower
bound. Property (T) and the finite cyclic average round into `R^Theta`,
not into the strictly smaller algebra `Phi_B(R)`.

The missing observable can be named with one elementary Laurent return.
Put

~~~text
gamma=e_12(x_2) in Gamma,
h=B^(-1) gamma B=e_12(x_2/x_1)
  in B^(-1) Gamma B setminus Gamma.                      (KHL5)
~~~

Then, in the same canonical model,

~~~text
||[p,sigma(h)]||_2=1/sqrt(2).                            (KHL6)
~~~

The two cyclic conjugates `C^(-i)hC^i`, `i=1,2`, have the
same norm. Therefore any successful matrix-ultraproduct argument must use a
source-specific estimate forcing this fixed Laurent-return packet to have
small action on the pointed contraction. Order-three averaging and the
Gamma spectral gap alone provably cannot do it.

The model in (KHL3)--(KHL6) is the full exact finite tracial wreath model.
Whether its trace is Connes embeddable is the desired hyperlinearity
question, so it is not a non-hyperlinear-group proof and the global root
remains **OPEN**.

DERIVATION
kt-minimal-cyclic-holonomy-and-explicit-laurent-return-proof
