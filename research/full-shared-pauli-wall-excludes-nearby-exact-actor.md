---
rg: 2
id: full-shared-pauli-wall-excludes-nearby-exact-actor
kind: claim
title: The full shared-Pauli wall forces a fixed distance from every genuine actor
distinct_from:
  kazhdan-stabilizer-collapses-shared-pauli-sign: that assumes the supplied actor coordinates are exact; this transfers its collapse through an arbitrary nearby actor tuple and solves quantitatively for the required actor distance.
  generic-perturbations-destroy-exact-commutant-gap: that makes a trace-faithful actor tuple arbitrarily close to a genuine regular quotient while destroying its literal commutant; this proves such a tuple cannot simultaneously carry the full Pauli wall.
  kt-majorana-wall-certifies-macroscopic-actor-instability: that uses one Kun--Thom mixed return and finite-image collapse; this uses the finite-double-coset shared-Pauli rows and applies to every transitive finite-rank action with Kazhdan stabilizer.
---

**NEAR-EXACT COUNTERMODELS EXCLUDED; ARBITRARY LOW-BAND CASE OPEN.**

Let `G` act transitively on the infinite set `X=G/Gamma`.  Suppose
`Gamma` has Kazhdan pair `(Q,kappa)` and choose the non-diagonal
double-coset representatives

~~~text
Gamma backslash G/Gamma
 ={Gamma,Gamma r_1 Gamma,...,Gamma r_s Gamma}.            (SPW1)
~~~

Let `U` be any unitary tuple on a fixed generating set of `G`, with
`U_w` denoting free-word evaluation.  Let `rho:G->U(D)` be a genuine
representation and set

~~~text
eta=max_(w in Q union {r_1,...,r_s}) norm_2(U_w-rho(w)).  (SPW2)
~~~

For unitaries `A,B,J` define

~~~text
d_J=norm_2(ABA^*B^*-J),

d_H=max_(q in Q; C in {A,B}) norm_2(CU_q-U_qC),

d_X=max_(1<=l<=s; C,D_0 in {A,B})
    norm_2(C U_(r_l) D_0 U_(r_l)^*
             -U_(r_l) D_0 U_(r_l)^* C).                 (SPW3)
~~~

Then

~~~text
norm_2(J-I)
 <= d_J+d_X+4 eta+(16/kappa)(d_H+2 eta).                 (SPW4)
~~~

In particular, if all three Pauli defects are at most `delta` and
`norm_2(J-I)>=c`, then every genuine actor satisfies

~~~text
eta >=
 [c-(2+16/kappa)delta]_+ /(4+32/kappa).                  (SPW5)
~~~

Thus a canonical sign with `c->sqrt(2)`, or a negative spin corner with
`c=2`, certifies a dimension-independent actor instability.

Consequently the trace-faithful generic perturbations in
`generic-perturbations-destroy-exact-commutant-gap` cannot keep the full
shared-Pauli rows with `J` separated: they are `o(1)` from genuine regular
quotient coordinates, so (SPW4) would force `J->I`.  This proves that the
exact-actor theorem has real source-specific leverage and that the generic
literal-commutant no-go is not a countermodel to the Pauli presentation.

The remaining case is precise.  A hypothetical full-wall hyperlinear model
must have its fixed packet `Q union {r_l}` stay a positive normalized-HS
distance from every genuine actor representation.  Property
`(T;FD)_rob` may still place the Pauli generators in a robust low spectral
band, but that band cannot arise from an `o(1)` perturbation of an exact
coordinate model.  No collapse of such arbitrary low-band models, and no
nonhyperlinear group, is proved here.

DERIVATION
nearby-exact-actor-transfer-collapses-shared-pauli-wall-proof
