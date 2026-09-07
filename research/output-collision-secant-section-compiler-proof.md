---
rg: 2
id: output-collision-secant-section-compiler-proof
kind: route
title: Use a decoder collision as a secant kernel vector and linearize a local section
target: output-secants-with-local-sections-force-matrix-defects
requires:
  - nonlinear-local-sections-of-linear-families-linearize
  - certificate-linear-counterexamples-compile-to-lamp-algebras
  - boolean-secants-do-not-supply-operator-left-inverses
---

## Secants exist locally, but their sections are an additional premise

For each local rule of sigma enumerate its finitely many scalar input
coordinates. Interpolate a local input a to b one coordinate at a time.
Divide each successive output difference by the nonzero coordinate
increment to obtain that column of a secant matrix. At a zero increment,
use the output change under a unit increment in that coordinate. The
successive differences telescope, giving (OSC1). Applying the same
enumeration at every group coordinate yields Q with finite data memory
and finite certificate memory. The unit-increment convention also gives
the actual coefficient operator when sigma is linear.

This establishes only (OSC1). Even when sigma has a nonlinear cellular
section tau, its local rule need not invert any particular Q_c when c
is held fixed and arbitrary new data are supplied.

This is a demonstrated limitation, not just an unverified inference.
For the reversible three-bit gate in
`boolean-secants-do-not-supply-operator-left-inverses`, its secant at
(000,111) has rank two. Since the rule is sitewise, the corresponding
operator cannot even produce all three-bit values at one site, so it
has no right inverse, local or otherwise. The reduction below applies
to a secant family satisfying (OSC2); it does not assert that canonical
telescopes always give such a family.

## A collision forces a nonzero reverse defect

Apply `nonlinear-local-sections-of-linear-families-linearize` to (OSC2).
It gives a certificate-local linear P with Q_c P_c=I for every c. Both
families are matrices in R_B. Their representation on all certificate
fibers is faithful: evaluating a nonzero coefficient at a suitable
certificate and testing a unit input at its group coordinate isolates
that coefficient in an output row. Hence QP=I in the coefficient ring.

Since sigma is noninjective, choose a!=b with sigma(a)=sigma(b).
Equation (OSC1) gives Q_c d=0 at c=(a,b), d=b-a!=0. It follows directly
that (I-P_c Q_c)d=d. Thus PQ!=I as a represented operator and therefore
also as a matrix in R_B. The witness d need not have finite support;
a nonzero output coordinate still detects a nonzero row of the finite
matrix expression I-PQ.

The map E(z,c)=(P_c z,c) is injective, since applying Q_c recovers z.
It is not surjective: the pair (d,c) is missing from its image. Indeed,
if P_c z=d then z=Q_c P_c z=Q_c d=0 and hence d=0, a contradiction.
This proves strictness on the entire full shift, without restricting
the certificate space to valid computations or image pairs.

Apply `certificate-linear-counterexamples-compile-to-lamp-algebras`
with |B|=p^(2n) to obtain the stated finite-lamp group and matrix sizes.
The claim concerns stable finiteness of this larger group's algebra;
it does not assert direct or stable finiteness failure of F_p[G] itself.

## A missing encoder output supplies the collision

Suppose sigma tau=id and b is outside the image of tau. Set
a=tau(sigma(b)). Then a is in that image and a!=b. Moreover,

    sigma(a)=sigma(tau(sigma(b)))=sigma(b).

Thus d=b-tau(sigma(b)) is a nonzero kernel vector for Q_(a,b), and
the reverse matrix defect fixes it exactly as in (OSC3). In fact,
under sigma tau=id, tau is nonsurjective if and only if sigma is
noninjective: if sigma were injective, sigma tau sigma=sigma would
imply tau sigma=id; if tau were surjective, sigma would be its inverse.

This explains the choice of certificates. Input-pair secants only see
pairs (tau(x),tau(y)) inside the encoder's image and cannot use the pair
(a,b) above. Output-pair certificates range over the whole full shift,
including missing outputs. They retain the actual nonlinear collision
needed to certify the reverse defect. What remains is a local section
of their linear secant family on every certificate and every data input.
