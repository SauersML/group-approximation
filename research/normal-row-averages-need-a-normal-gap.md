---
rg: 2
id: normal-row-averages-need-a-normal-gap
kind: claim
title: Averaged normal rows give a flat corner exactly after a normal-packet gap
artifacts:
  - research/spectral-cut-and-packed-lamp-countermodel.md
distinct_from:
  exact-core-domain-does-not-descend-to-normal-quotient: that separates the vacuum row from one translated row; this treats a complete finite Schreier packet, proves the sharp positive spectral-cut theorem, and gives a packed packet with vanishing average but zero common fixed space.
  cayley-expansion-aligns-isometry-frame-coranges: that uses quotient Cayley expansion to align a field of range projections; this shows that the different Laplacian formed from growing normal returns can have gap tending to zero even over uniformly expanding quotient graphs.
  packed-d-coset-flip-has-full-bs-hull: that packs a small cubic-displacement support whose BS hull is full inside one regular congruence block; this packs rank-one normal holonomies whose averaged operator tends to zero although their joint fixed space is zero.
---

Let (Gamma) be a finitely generated group, let
(Lambda	riangleleftGamma), and let
(mathcal R={r_1,ldots,r_M}) be a finite set which generates
(Lambda) as a group. For a unitary representation
(pi:Gamma	o U(mathcal H)), define the normal-packet Laplacian

[
 L_{mathcal R}
 =rac1Msum_{j=1}^M
   (pi(r_j)-1)^*(pi(r_j)-1).                         	ag{ANR1}
]

Its kernel is exactly

[
 mathcal K=mathcal H^{pi(Lambda)}.                 	ag{ANR2}
]

Because (Lambda) is normal, (mathcal K) reduces (pi(Gamma)).
Write (P) for its projection. Suppose that the packet has a spectral
gap

[
 L_{mathcal R} geq kappa(1-P)                    	ag{ANR3}
]

for some (kappa>0). Let (B<Gamma), let
(eta:B	o U(d)), and let (V:mathbb C^d	omathcal H) be an
isometry satisfying

[
 pi(b)V=Veta(b)qquad(bin B).                      	ag{ANR4}
]

Put

[
 D_{mathcal R}(V)^2
 =rac1{Md}sum_{j=1}^M
   |(pi(r_j)-1)V|_{mathrm F}^2,qquad
 delta=rac{D_{mathcal R}(V)^2}{kappa}.             	ag{ANR5}
]

Then there is a projection (eineta(B)') and an isometry

[
 W:emathbb C^dlongrightarrowmathcal K               	ag{ANR6}
]

which intertwines (eta|_e) with the quotient representation
(pi|_{mathcal K}:Gamma/Lambda	o U(mathcal K)), and

[
 rac{operatorname{rank}e}{d}geq1-2delta,qquad
 rac1d|W-Ve|_{mathrm F}^2leq2delta.              	ag{ANR7}
]

Thus an averaged translated-row estimate does produce a
positive-density invariant-flat relative corner, but only after a lower
bound for the **normal-packet** gap (kappa).

This additional gap is indispensable, even if the quotient graphs are
uniform Hilbert expanders and the vacuum/core row is exact. Let (Q) be
any finite group of order (M), put

[
 Lambda_Q=(C_2)^Q,qquad
 Gamma_Q=Lambda_Qtimes Q,                           	ag{ANR8}
]

where (Q) acts on its coordinate set by left translation. On
(mathcal H_Q=ell^2(Q)), let (Q) act by permutations and let the
coordinate lamp (z_q) act as the reflection

[
 pi_Q(z_q)=1-2p_q,                                    	ag{ANR9}
]

where (p_q) is projection onto the coordinate vector (e_q). Take
(B_Q=langle z_1angle), let
(V_Q:mathbb C^{M-1}	oell^2(Q)) include
(e_1^perp), and take the trivial (eta_Q). Then

[
 pi_Q(z_1)V_Q=V_Q,                                    	ag{ANR10}
]

so the distinguished vacuum row and the whole stated core are literal.
The translated normal packet is

[
 mathcal R_Q={qz_1q^{-1}:qin Q}
             ={z_q:qin Q},                          	ag{ANR11}
]

and it generates (Lambda_Q). Nevertheless

[
 L_{mathcal R_Q}=rac4M I_{ell^2(Q)},qquad
 D_{mathcal R_Q}(V_Q)^2=rac4M,                       	ag{ANR12}
]

while

[
 mathcal H_Q^{pi_Q(Lambda_Q)}=0.                    	ag{ANR13}
]

Hence the averaged defect tends to zero even in operator order, every
non-vacuum row has only rank-one support, and the combined deck holonomy
has no nonzero flat corner.

Choose (Q) along any uniformly expanding family, for example finite
congruence quotients of one fixed property-((T)) group with their fixed
marked images. Then the quotient Cayley graphs of
(Gamma_Q/Lambda_Q=Q) have one uniform Poincare constant, while
(ANR12)--(ANR13) persist. The defect field is exactly transported by the
quotient action, so averaging it again or applying the quotient Poincare
inequality loses no asymmetry that could reveal a flat vector.

For the Iwahori quotient, a section of
(G_N=A/Lambda_N) and the fixed marking (S) give the finite Schreier
packet

[
 r(q,s)=widetilde{sq}^{, -1}swidetilde q
 inLambda_Nqquad(qin G_N, sin S),                 	ag{ANR14}
]

after deleting identities and adjoining inverses. Schreier's lemma says
that these rows generate (Lambda_N). Therefore (ANR1)--(ANR7) give an
exact sufficient route from an averaged packet on the finite deck
quotient to a genuine quotient corner. What is missing is a
dimension-independent lower bound in (ANR3), for the actual candidate
dilations after core optimization.

Property ((T;FD)) controls a fixed marked (Gamma)-Laplacian on
finite-dimensional representations, and Selberg expansion controls
functions on the quotient. Neither statement by itself is (ANR3), which
is a growing normal-return Laplacian inside the selected Stinespring host.
The packed model proves that quotient expansion, equivariance, exact
vacuum data, and even operator-norm-small average packet energy do not
formally imply such a gap. Optimizing the core inside this host cannot
create vectors in the zero space (ANR13); selecting a different host is
the original finite-corner problem.

The packed model is not a representation of the arithmetic Iwahori
amalgam and is not a counterexample to relative liftability. It is an
exact firewall against the proposed expansion-only deck-averaging
argument. The arithmetic normal-packet gap, or another selector which
changes the host, remains open.

DERIVATION
spectral-cut-and-packed-lamp-countermodel
