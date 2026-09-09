---
rg: 2
id: shell-finite-ray-normal-core-finiteness-proof
kind: route
title: Quotient by central diagonal ray translation and recover a finite-index rational stabilizer as kernel
target: virtually-cyclic-inputs-have-fp-shell-stabilizers
requires:
  - shell-cantor-embeddings-are-finite-germ-extensions
  - shell-prefix-core-detects-finite-ray-enumerations
  - contracting-srn-rational-stabilizers-are-fp
artifacts:
  - research/artifacts/boone-higman-shell-normal-core-criterion-2026-09-08.md
---

Use the enumeration and m from the prefix-core claim. The group of
eventually m-periodic near permutations identifies with

    R_m = Z^m semidirect S_m.

The permutation records the target residue ray, and each integer
records the translation of its ray coordinate. Unlike actual
permutations of N, near permutations need not satisfy a zero sum
condition on these translations. The isotropy germ group Q lies
in R_m: its generators rho(P) are eventually m-periodic, and tau
is as well. Here C=<tau^m> is simultaneous translation by one on
every ray, so it is central in R_m. Also C subset H=<tau>, with
[H:C]=m.

Every subgroup of R_m is virtually finitely generated abelian.
Indeed its intersection with Z^m is a subgroup of a finite-rank
free abelian group, hence finitely generated, and has finite index.
The same holds for Q/C and every subgroup of any finite power of
Q/C: these groups are virtually finitely generated abelian. They
are all finitely presented, since a finitely generated abelian
group has a finite presentation and finite extensions preserve
finite presentation.

Fix finite M subset M' subset Omega and let A=S(M,M'). Transport
the germs Q,H,C from p to each x in M by a V map carrying p to x.
Denote the transported groups by Q_x,H_x,C_x. Normality of C_x
in Q_x makes the following a homomorphism:

    psi: A -> product_(x in M) Q_x/C_x.

An element in its kernel has V germ at every x in M, since
C_x subset H_x. It was already locally V everywhere else. Thus
it lies in Fix_V(M'). More precisely,

    ker(psi) = {v in Fix_V(M'): germ_x(v) in C_x for all x in M}.

This is a subgroup of index at most m^|M| in Fix_V(M'), obtained
as the kernel of the joint germ map to product H_x/C_x. The
rational-stabilizer claim, applied to V and the trivial coefficient
group, makes Fix_V(M') finitely presented. So ker(psi) is finitely
presented. The image of psi is a subgroup of a virtually finitely
generated abelian group, hence is finitely presented as proved above.
An extension of a finitely presented kernel by a finitely presented
quotient is finitely presented, proving the claim for A. For M empty
this just recovers Fix_V(M'). No surjectivity onto the full germ
product has been assumed.

The V action on Omega is highly transitive by finite disjoint-cone
prefix interpolation. Applying
[Belk--Hyde--Matucci, Theorem 2.1](https://arxiv.org/html/2407.03149v1#S2.SS1)
with n=2 gives E finitely presented.

For a finite F subset Omega, put E_F=Fix_E(F), B_F=Fix_V(F).
This is still a finite germ extension, with singular set Omega.
To see the local assertion, extend the desired V germ while also
fixing F: when the basepoint lies outside F, correct the images of
F by a prefix map equal to the identity near the image of the
basepoint; when it lies in F, that point is already fixed and the
other points can be corrected away from its neighborhood. Distinct
points have disjoint sufficiently small cones, so finite prefix
interpolation realizes these prescriptions. The same correction
applied to a one-singularity representative gives the required
one-singularity element in E_F. Singularities at any prescribed
point of Omega can likewise be realized while fixing F. Relative
fullness follows because an E_F element locally B_F is locally V
and therefore belongs to B_F.

B_F has finitely many orbits on Omega^2: its fixed points are F
and it acts highly transitively on the complement. For M subset M'
of size at most two, its required singularity subgroup is exactly
S(M,M' union F), already proved finitely presented. The same n=2
theorem makes E_F finitely presented.

The kernel argument above is an additional finite-index normal-core
criterion. It is not an application of the source's normal-prefix-germ
alternative, whose normality hypothesis fails for these shell groups.
