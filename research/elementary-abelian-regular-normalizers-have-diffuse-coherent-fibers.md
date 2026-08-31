---
rg: 2
id: elementary-abelian-regular-normalizers-have-diffuse-coherent-fibers
kind: claim
title: Regular elementary-abelian windows classicalize only after quotienting diffuse normalizer fibers
distinct_from:
  simple-lamp-normalizers-have-unitary-multiplicity-fibers: that treats one amplified regular packet of a finite centerless simple lamp; this proves the fixed-window permutation quotient for elementary abelian lamps and gives an increasing-window, trace-faithful coherent countermodel.
  scalar-trace-of-diagonal-normalizer-is-permutation-blind: that hides trace cancellation in a diagonal phase after a full masa is normalized; this uses a Fourier unitary in the regular lamp multiplicity commutant and keeps lamp covariance and actor multiplication exact.
  kt-centralizer-normalization-hs: that is the global open relative-commutant normalization theorem for the Kazhdan pair; this settles only one invariant finite lamp window and isolates why moving windows are still different.
artifacts:
  - notes/TRUE_RELATIVE_BURTON_KUN_THOM_REDUCTION.md
---

**ESTABLISHED SHARP LOCAL BOUNDARY.**

## 1. One invariant regular window has a classical quotient

Let (B) be a fixed finite elementary abelian two-group and let
(sigma_n:B	ooperatorname{Sym}(V_n)) be permutation actions satisfying

[
 rac{|operatorname{Fix}(sigma_n(b))|}{|V_n|}longrightarrow 0
 qquad(b
e 0).                                      	ag{EAR1}
]

Let (H) act on (B) through a homomorphism
(alpha:H	ooperatorname{Aut}(B)).  Then there are genuine homomorphisms

[
 P_n:Hlongrightarrowoperatorname{Sym}(V_n)           	ag{EAR2}
]

such that, for every fixed (hin H) and (bin B),

[
 d_H!left(P_n(h)sigma_n(b)P_n(h)^{-1},
            sigma_n(alpha_h(b))ight)longrightarrow0. 	ag{EAR3}
]

Indeed, all but (o(|V_n|)) points lie in free (B)-orbits.  On each free
orbit, after choosing one basepoint, use the canonical permutation
(x=sigma_n(b)x_0mapstosigma_n(alpha_h(b))x_0); let (H) act trivially
on the exceptional set.  Thus an invariant asymptotically regular finite
lamp window has no local existence obstruction.  Coherent unitary
normalizers are not even needed for this conclusion.

On an exactly free packet
(ell^2(B)otimesmathbb C^k), write
(P_alphadelta_b=delta_{alpha(b)}).  Every unitary (U) satisfying

[
 U(lambda_B(b)otimes1)U^*
   =lambda_B(alpha(b))otimes1                       	ag{EAR4}
]

has the unique form

[
 U=D(P_alphaotimes1),qquad
 Dinmathcal U((lambda_B(B)otimes1)').              	ag{EAR5}
]

For a coherent actor family, the (D)'s form a nonabelian one-cocycle in
this commutant.  Passing to the quotient by the commutant returns the
canonical coherent permutations (P_alpha), but gives no metric control of
the chosen representatives.

## 2. Exact coherence and canonical trace do not control that fiber

There is a trace-faithful increasing-window model in which the cocycle in
((mathrm{EAR5})) is maximally nonmonomial.  Put

[
 A=igoplus_{rge1}mathbb F_2^3
]

and let (t) act on each three-dimensional block by
(J=1+N), where (N^3=0
e N^2).  Thus (J) has order four.  For the first
(m) blocks (B_mle A), choose (k_m	oinfty), let (Q_m) be the
permutation implementing (J) on (ell^2(B_m)), and let (F_{k_m}) be the
normalized Fourier matrix.  Then

[
 U_m=Q_motimes F_{k_m},qquad
 pi_m(b,t^j)=(lambda_{B_m}(b)otimes1)U_m^j          	ag{EAR6}
]

is an exact representation of (B_mtimes C_4).  The lamp restriction is
(k_m) copies of the regular permutation representation, all covariance
rows and all actor products have zero defect, and the sequence has the
canonical group trace.  Nevertheless, for every monomial matrix (M_m) in
the displayed lamp basis,

[
 |U_m-M_m|_2^2ge 2-rac{2}{sqrt{k_m}}.             	ag{EAR7}
]

The same lower bound tends to (2) after adjoining (o(|B_m|k_m)) identity
dimensions.  Hence neither exact coherence, canonical trace, regular lamp
multiplicity, nor negligible padding makes the supplied actor unitary close
to a permutation.

Fourier diagonalization gives

[
 (lambda_{B_m}(B_m)otimes1)'
   congigoplus_{chiinwidehat B_m}M_{k_m}(mathbb C). 	ag{EAR8}
]

In particular the tracial ultraproduct contains the diffuse algebra
(prod_{mathcal U}M_{k_m}), and the Fourier factor in ((mathrm{EAR6}))
lives entirely there.  This is a concrete diffuse-multiplicity model, not a
dimension-zero block surgery.

## 3. Exact surviving Kun--Thom gate

This result does **not** refute equivariant normalizer transfer: the canonical
permutations (Q_motimes1) exist in the countermodel.  It refutes only the
stronger shortcut that tries to round the given (U_m)'s themselves in
normalized Hilbert--Schmidt norm.

The Kun--Thom lamps present moving algebras
(B_Emapsto B_{gE}), not one invariant finite (B).  The remaining theorem
must therefore construct compatible commutant gauges, or directly construct
permutations, across an increasing family of moving windows so that actor
products agree on almost every point.  The cocycles live in different
multiplicity algebras as the window moves.  No finite-window quotient
argument identifies them, and the global route remains open.

DERIVATION
elementary-abelian-regular-normalizer-fiber-proof
