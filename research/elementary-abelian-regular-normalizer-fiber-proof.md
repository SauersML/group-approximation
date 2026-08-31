---
rg: 2
id: elementary-abelian-regular-normalizer-fiber-proof
kind: route
title: Split the free lamp orbits and insert a coherent Fourier multiplicity cocycle
target: elementary-abelian-regular-normalizers-have-diffuse-coherent-fibers
requires: []
---

## Step 1: almost every point is in a free orbit

Put

[
 V_n^{mathrm{fr}}
   ={xin V_n:operatorname{Stab}_B(x)={0}}.
]

Because (B) is fixed,

[
 V_nsetminus V_n^{mathrm{fr}}
   =igcup_{0
e bin B}operatorname{Fix}(sigma_n(b)),
]

and hence ((mathrm{EAR1})) gives

[
 rac{|V_nsetminus V_n^{mathrm{fr}}|}{|V_n|}
 lesum_{0
e bin B}
      rac{|operatorname{Fix}(sigma_n(b))|}{|V_n|}
 longrightarrow0.                                    	ag{EAP1}
]

The free set and its complement are both (B)-invariant.  Choose one
basepoint (x_i) in every free orbit.  Define

[
 P_n(h)(sigma_n(b)x_i)=sigma_n(alpha_h(b))x_i
                                                               	ag{EAP2}
]

on the free set, and define (P_n(h)) to be the identity on the complement.
Freeness makes ((mathrm{EAP2})) well-defined.  The homomorphism law for
(alpha) gives (P_n(h)P_n(k)=P_n(hk)) on every free orbit, and it is also
true on the complement.  Thus (P_n) is a genuine permutation
representation of (H).

Covariance is exact on (V_n^{mathrm{fr}}).  Its possible disagreement set
on the complement has measure bounded by the left side of ((mathrm{EAP1})),
which proves ((mathrm{EAR3})).  Notice that the construction used only the
regular-character condition; no choice of unitary implementers entered.

## Step 2: classify the exact unitary implementers

On (ell^2(B)otimesmathbb C^k), let (P_alpha) be the canonical
permutation of the first factor.  Suppose (U) satisfies
((mathrm{EAR4})), and put

[
 D=U(P_alphaotimes1)^*.
]

For every (cin B),

[
egin{aligned}
 D(lambda_B(c)otimes1)D^*
 &=U(P_alpha^*lambda_B(c)P_alphaotimes1)U^*\
 &=U(lambda_B(alpha^{-1}(c))otimes1)U^*\
 &=lambda_B(c)otimes1.
end{aligned}
]

Thus (D) is in the lamp commutant and (U=D(P_alphaotimes1)).
Uniqueness and the converse are immediate.

If (U_h=D_hP_h) is a genuine actor representation, with tensor identities
suppressed, then

[
 D_{hk}=D_h,operatorname{Ad}(P_h)(D_k).               	ag{EAP3}
]

So actor multiplication controls the multiplicity freedom only by the
ordinary nonabelian cocycle equation.  It does not force (D_h=1), or even
force (D_h) to be near a monomial.

## Step 3: an increasing trace-faithful coherent model

Give (mathbb F_2^3) a basis (e_1,e_2,e_3), let

[
 Ne_1=0,qquad Ne_2=e_1,qquad Ne_3=e_2,
]

and put (J=1+N).  In characteristic two,

[
 J^2=1+N^2
e1,qquad J^4=1+N^4=1,                     	ag{EAP4}
]

so (J) has order four.  Let

[
 A=igoplus_{rge1}mathbb F_2^3,qquad
 B_m=igoplus_{r=1}^mmathbb F_2^3,
]

and let (C_4=langle tangle) act blockwise by (J).  Truncation
(p_m:A	o B_m) is (C_4)-equivariant.

Let (Q_mdelta_b=delta_{Jb}) on (ell^2(B_m)).  For any sequence
(k_m	oinfty), let (F_{k_m}) be the normalized discrete Fourier matrix
and set

[
 U_m=Q_motimes F_{k_m}.
]

The standard identities (F_k^2e_r=e_{-r}) and (F_k^4=1), together with
(Q_m^4=1), give (U_m^4=1).  Moreover,

[
 U_m(lambda_{B_m}(b)otimes1)U_m^*
   =lambda_{B_m}(Jb)otimes1.                          	ag{EAP5}
]

Consequently

[
 pi_m(a,t^j)
  =(lambda_{B_m}(p_m(a))otimes1)U_m^j                	ag{EAP6}
]

is an exact representation of the fixed group (Atimes_J C_4).
It factors through (B_mtimes_J C_4).  Formula ((mathrm{EAP5})) proves
zero lamp-covariance defect, and (U_m^4=1) proves exact actor coherence.

These representations have the canonical group trace.  If (j=0) and
(a
e0), then (p_m(a)
e0) for all sufficiently large (m), and its left
translation has trace zero.  For (j=1,3), every diagonal entry of
(F_{k_m}^j) has modulus (k_m^{-1/2}), so

[
 |operatorname{tr}_{k_m}(F_{k_m}^j)|le k_m^{-1/2}.    	ag{EAP7}
]

The permutation (F_{k_m}^2) has at most two fixed basis vectors, and hence

[
 |operatorname{tr}_{k_m}(F_{k_m}^2)|le2/k_m.         	ag{EAP8}
]

For (j
e0), the normalized trace of ((mathrm{EAP6})) is the product of
the normalized traces of
(lambda_{B_m}(p_m(a))Q_m^j) and (F_{k_m}^j).  The first factor has
modulus at most one, while ((mathrm{EAP7}))--((mathrm{EAP8})) tend to
zero.  Thus every fixed nonidentity element has limiting trace zero.

## Step 4: the sharp monomial distance, including padding

In the product lamp basis, every row of (U_m=Q_motimes F_{k_m}) has
exactly (k_m) nonzero entries, all of modulus (k_m^{-1/2}).  A monomial
matrix selects at most one entry in each row.  With
(d_m=|B_m|k_m), it follows that for every monomial (M_m),

[
 left|operatorname{tr}_{d_m}(M_m^*U_m)ight|
 le k_m^{-1/2}.                                       	ag{EAP9}
]

Both matrices are unitary, so

[
 |U_m-M_m|_{2,d_m}^2
 =2-2operatorname{Re}operatorname{tr}_{d_m}(M_m^*U_m)
 ge2-rac2{sqrt{k_m}},
]

which is ((mathrm{EAR7})).

This persists under every negligible block padding, not just identity
padding.  Let (r_m=o(d_m)), let (Z_min U(r_m)) be arbitrary, and compare
(U_moplus Z_m) with an arbitrary monomial (M'_m) of size (d_m+r_m).
The old rows contribute at most (d_m/sqrt{k_m}) to the unnormalized
overlap and the new rows contribute at most (r_m).  Cross-block choices
contribute zero.  Hence

[
 left|operatorname{tr}_{d_m+r_m}
   ((M'_m)^*(U_moplus Z_m))ight|
 lerac{d_m/sqrt{k_m}+r_m}{d_m+r_m}longrightarrow0. 	ag{EAP10}
]

Therefore the squared normalized Hilbert--Schmidt distance is at least
(2-o(1)), and the distance tends to (sqrt2).  This covers every
permutation, every orbit-coherent permutation, and every monomial
representative after (o(d_m)) padding.

Finally, Fourier transform on the (B_m)-coordinate decomposes the regular
representation into its characters, each with multiplicity (k_m).  Thus

[
 (lambda_{B_m}(B_m)otimes1)'
 congigoplus_{chiinwidehat B_m}M_{k_m}(mathbb C).
]

The subalgebra (1otimes M_{k_m}) has a diffuse tracial ultraproduct because
(k_m	oinfty), and (1otimes F_{k_m}) is precisely the nonclassical
factor of (U_m).  The obstruction is therefore a macroscopic diffuse
multiplicity cocycle.

For comparison with the published frontier: Kun--Thom Theorem 4.1
(arXiv:2608.06222v1) obtains normalization inside a permutation ultraproduct
from finite expander-component groupoids.  Alekseev--Thom Open Problem 6.2
(arXiv:2608.05362v1) asks whether Kazhdan commutants in tracial matrix
ultraproducts admit finite-coordinate descriptions.  The diffuse algebra
above explains why the finite-window lamp calculation supplies neither
coordinate structure nor the moving-window compatibility needed by those
results.  It is not a counterexample to either published statement.
