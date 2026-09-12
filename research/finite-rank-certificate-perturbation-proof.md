---
rg: 2
id: finite-rank-certificate-perturbation-proof
kind: route
title: Propagate invertibility through finite certificate changes and then through their dense closure
target: one-invertible-certificate-fiber-forces-global-invertibility
requires:
  - certificate-linear-automata-have-local-linear-decoders
---

## The finite-rank lemma

Let V be any vector space over k, including an infinite-dimensional
space of all configurations. If T=I+K and W=im K is finite-dimensional,
then T(W) is contained in W. If T is injective, its restriction to W
is bijective. Given v in V, choose w in W with T w=K v; then

    T(v-w)=v.

Thus an injective finite-rank perturbation of I is bijective. A
finite-rank perturbation of any invertible operator has the same property
after multiplication by that operator's inverse. Conversely, a surjective
I+K is injective: every preimage of W lies in W, so T|W is surjective
and hence injective, and ker T is contained in W. No topology, analytic
Fredholm theorem, or characteristic restriction is used.

## A finite change affects finitely many output rows

Take a common certificate memory D for the coefficients of A. If c
differs from c_* only on a finite set E, the coefficients at output g
can differ only when gD meets E, namely when g belongs to ED^(-1).
This is a finite subset of G. Hence

    im(A_c-A_(c_*)) is contained in (k^n)^(ED^(-1)),

where the notation on the right denotes data supported in that finite
set. In particular A_c-A_(c_*) has finite rank on the full configuration
space. Since B_c A_c=I, A_c is injective. If A_(c_*) is invertible,
the finite-rank lemma makes A_c bijective. Its given left inverse B_c
is then its inverse, so A_c B_c=I.

## Finite-change certificates detect all local identities

Every finite cylinder in B^G contains a certificate agreeing with c_*
outside finitely many sites: retain the cylinder pattern and use c_*
elsewhere. Such certificates are therefore dense. The product AB is
again a certificate-local operator with finite data memory. Each of its
coefficient functions is locally constant, and each coefficient of AB-I
vanishes on the dense finite-change class by the previous paragraph.
They consequently vanish everywhere. This proves the fiber theorem.

## Constant evaluation reflects a one-sided inverse defect

The algebraic crossed product has the faithful representation

    (pi_c(sum_s f_s u_s)z)(g)=sum_s f_s(g^(-1).c)z(gs).

Faithfulness follows by evaluating at the origin and testing input
vectors supported at individual s. Matrix coefficients are handled
by also choosing an individual scalar data coordinate.

For any b in B, the constant certificate c_b is fixed by G. Thus

    ev_b(sum_s f_s u_s)=sum_s f_s(c_b)[s]

is a unital ring homomorphism R_C->k[G], retracting the constant
coefficient inclusion. Given BA=I, if ev_b(A)ev_b(B)=I, the represented
fiber at c_b is invertible and the fiber theorem gives AB=I in every
fiber, hence in R_C. Therefore AB!=I must remain nonzero under every
ev_b. This proves the claimed fixed-size direct-finiteness equivalence;
the reverse implication also follows from the inclusion k[G] subset R_C.

For the finite-field dynamical statement, apply the local decoder theorem
to an injective (z,c)->(A_c z,c). This gives B as above. Surjectivity of
the full map is exactly surjectivity of every fiber, and the theorem
shows that one surjective fiber suffices. Nonsurjectivity therefore
occurs on every fiber, including every constant one.

Finally, in the output-secant setting QP=I, apply the result with A=P,
B=Q. If any Q_c is injective, its existing right inverse P_c makes it
bijective, so the theorem forces PQ=I everywhere. A nonlinear collision
already gives a nonzero reverse defect, so no such fiber can be injective.
