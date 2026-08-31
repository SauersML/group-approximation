---
rg: 2
id: fixed-qutrit-constant-template-and-block-polar-proof
kind: route
title: Separate fixed qutrit exactification from the off-diagonal Lin occurrence gate
target: fixed-qutrit-test-is-either-finite-rigid-or-morita-neutral
requires:
  - quantum-low-degree-is-a-non-equality-pauli-synchronizer
  - fixed-field-plane-point-loses-uniform-low-degree-robustness
  - lin-independent-set-synchbcs-has-uniform-nonaffine-onehot-mass
  - moved-root-dft-router-loses-quarter-and-collides-two-to-one
  - first-uncancelled-g2-mixed-carrier-has-no-hall-deficit
---

# Separate fixed qutrit exactification from the off-diagonal Lin occurrence gate

## 1. What Theorem 3.2 says at (q=3)

Let (q=p^t).  Natarajan--Vidick, *Low-degree testing for quantum
states, and a quantum entangled games PCP for QMA*, Theorem 3.2, assumes
that (mathbb F_q) has a self-dual basis over (mathbb F_p).  For
(mathbb F_3/mathbb F_3), the field trace is the identity and the
one-element basis ({1}) has Gram matrix ((1)).  Thus (q=3) is
formally admissible.

The parameters obey

[
 h^mge n,qquad d=hm,                                  	ag{1}
]

and the stated self-testing error has the form

[
 delta=operatorname{poly}!left(
   operatorname{poly}(p)operatorname{poly}(arepsilon)
   +operatorname{poly}(d/q)ight).                    	ag{2}
]

At (q=3), equation (2) is not a modulus which the theorem proves tends
to zero with (arepsilon).  The (d/3) contribution remains when
(arepsilon) tends to zero.  This is a statement about the scope of
the published bound, not a claim that an exact (q=3) strategy must be
far from every ideal strategy.

The obstruction is scalable.  If (n) tends to infinity subject to
(1), then (d=hm) tends to infinity.  Indeed, for any fixed (D) there
are only finitely many positive integer pairs with (hmle D), and the
finite set of values (h^m) for those pairs has a finite maximum.
Consequently (d/3) cannot remain in the small-error regime along an
unbounded fixed-(q=3) family.

The same point is visible in the code distance.  The individual-degree
tensor code has relative distance

[
 left(1-rac h3ight)^m                               	ag{3}
]

when (h<3), and no useful positive-distance interpretation once the
individual-degree parameter reaches the field size.  For fixed positive
(h), (3) tends to zero with (m).  Thus the qutrit specialization
corrects the local cardinality objection--an affine line over
(mathbb F_3) has three points--but it does not supply a scalable
fixed-alphabet agreement theorem.

There is a second scope boundary.  The conclusion of the self-test is
after local isometries and includes an arbitrary auxiliary state.  It is
not a theorem asserting normalized-Hilbert--Schmidt stability of a fixed
group presentation in every tracial algebra.

## 2. The constant-size alternative is just a finite group

Suppose now that the number (k) of qutrit coordinates is fixed.  Let

[
 mathsf P_{3,k}
 =langle J,X_1,ldots,X_k,Z_1,ldots,Z_kangle
]

with (J^3=X_i^3=Z_i^3=1), (J) central,
([X_i,Z_i]=J), and all other basic commutators trivial.  Then

[
 |mathsf P_{3,k}|=3^{2k+1}.                             	ag{4}
]

This packet has a dimension-independent flexible
Hilbert--Schmidt exactification modulus for fixed (k).  One direct
route is the standard finite-group argument.  Choose one word
representative for each element of (mathsf P_{3,k}).  Because the
group is finite, every multiplication-table equality has some finite
relator-area in the chosen presentation; let (A_k) be the maximum of
these finitely many areas.  A presentation assignment of defect
(arepsilon) therefore gives an
(O(A_karepsilon))-approximate homomorphism on the whole finite
multiplication table.  Finite-group/Gowers--Hatami stability replaces it,
after an (o(1)) dimensional correction, by an exact unitary
representation.  All constants depend on the fixed packet, not on the
ambient matrix dimension.

Accordingly the low-degree test is not needed to exactify one fixed
qutrit packet.  Its useful positive content concerns a growing Pauli
family with a growing field, whereas the present compiler uses a fixed
finite head.

## 3. The central-character corner

Fix (omega=e^{2pi i/3}) and put

[
 p_omega=rac13(1+omega^{-1}J+omega^{-2}J^2).        	ag{5}
]

The Schrödinger representation on
(ell^2(mathbb F_3^k)) has dimension (D=3^k) and central
character (Jmapstoomega).  It is the unique irreducible
representation with that central character.  To see uniqueness, start
with a joint (Z)-eigenvector.  The (D) vectors obtained by applying
the (X(a)), (ainmathbb F_3^k), have distinct joint
(Z)-characters and span the standard irreducible module.

The central corner has complex dimension

[
 dim p_omegamathbb C[mathsf P_{3,k}]
 =rac{|mathsf P_{3,k}|}{3}=3^{2k}=D^2.               	ag{6}
]

The standard irreducible maps it onto (M_D(mathbb C)), so (6)
proves

[
 p_omega C^*(mathsf P_{3,k})p_omega
 cong M_D(mathbb C).                                  	ag{7}
]

For every unital occurrence algebra (A),

[
 p_omegaig(C^*(mathsf P_{3,k})otimes_{max}Aig)
 p_omega
 cong M_D(mathbb C)otimes_{max}A.                   	ag{8}
]

Let (P) be an occurrence projection in this corner.

* If (P) commutes with the whole recovered Pauli matrix factor, expand
  it against matrix units.  The equations
  ([P,e_{rs}otimes1]=0) force all off-diagonal coefficients to vanish
  and all diagonal coefficients to agree.  Hence

  [
   P=1otimes p                                           	ag{9}
  ]

  for a projection (pin A).

* If (P) is required to lie in the Pauli factor, then

  [
   P=fotimes1,qquad operatorname{tr}_D(f)
       =rac{operatorname{rank}f}{D}.                  	ag{10}
  ]

  It has a fixed finite matrix model and a rational trace.

Thus the fixed qutrit packet offers two automatically controlled faces:
a finite rigid face (10) and an arbitrary auxiliary face (9).  A
nonreducing mixed projection in (M_Dotimes A) is of course possible,
but neither the finite-group exactification nor Q-LOWDEG identifies one.
That is precisely extra occurrence data which a compiler must impose.

Every trace on (M_Dotimes A) factors.  If

[
 	au_A(a)=	au(1otimes a),
]

then traciality on matrix units gives

[
 	au(e_{rs}otimes a)=rac{delta_{rs}}D,	au_A(a),
 qquad 	au=operatorname{tr}_Dotimes	au_A.           	ag{11}
]

This is the operator-algebraic form of the arbitrary auxiliary state in
the self-test.

## 4. Exact polar decomposition over an occurrence PVM

The following calculation applies to any finite-dimensional head
algebra (M), not only to (M_D).  Let
((M,	au_M)) and ((A,	au_A)) be finite tracial algebras, and let

[
 p_ip_j=0 (i
e j),qquad sum_i p_i=1                 	ag{12}
]

be an occurrence PVM in (A).  For (b_iin M), define

[
 B=sum_i b_iotimes p_i.                               	ag{13}
]

Orthogonality gives

[
 B^*B=sum_i b_i^*b_iotimes p_i,qquad
 BB^*=sum_i b_ib_i^*otimes p_i.                       	ag{14}
]

Write (b_i=v_i|b_i|).  Functional calculus in the direct sum (14)
gives the polar decomposition

[
 B=V|B|,qquad V=sum_i v_iotimes p_i.                 	ag{15}
]

Therefore, with

[
 s_i=operatorname{supp}|b_i|,qquad
 q_i=operatorname{supp}|b_i^*|,
]

one has the exact identities

[
 operatorname{supp}|B|=sum_i s_iotimes p_i,qquad
 operatorname{supp}|B^*|=sum_i q_iotimes p_i.        	ag{16}
]

No number of diagonal occurrence blocks can make the head ranges add.
They remain weighted by their own multiplicity projections.

Let (Rin M) be a target projection and suppose

[
 q_ile R,qquad 	au_M(q_i)le r                       	ag{17}
]

for every positive occurrence block.  Put
(Q=operatorname{supp}|B^*|).  Since (Qle Rotimes1),

[
 egin{aligned}
 |Rotimes1-Q|_2^2
 &=	au_M(R)-sum_i	au_M(q_i)	au_A(p_i)\
 &ge 	au_M(R)-r.                                      	ag{18}
 end{aligned}
]

There is also a branchwise fullness criterion.  If
(Q=Rotimes1), multiplication by (1otimes p_i) gives

[
 (R-q_i)otimes p_i=0.                                  	ag{19}
]

Hence (q_i=R) for every nonzero (p_i).  Joins or averages across
different Lin outcomes cannot substitute for one full head branch.

## 5. Insert the qutrit rank tables

For the corrected collected moved-root target,

[
 	au_M(R)=	au(Ee_b)=rac1{18}.                       	ag{20}
]

The largest collected head range has trace (5/192); the other sign
rows have trace at most (3/128).  Equation (18) yields

[
 rac1{18}-rac5{192}
 =rac{32-15}{576}
 =rac{17}{576},                                       	ag{21}
]

and on a non-all-plus row

[
 rac1{18}-rac3{128}
 =rac{64-27}{1152}
 =rac{37}{1152}.                                      	ag{22}
]

These are squared normalized-Hilbert--Schmidt defects.  They are
independent of the number of occurrence outcomes, their matrix ranks,
and the dimension of the auxiliary algebra.

The first uncollected target-forcing carrier containing both raw
orientations is

[
 Ee_b g_2G_{sigma,	au}(VU_2)G_{sigma,	au}R.          	ag{23}
]

Its possible initial support traces before the last target compression
are

[
 rac{43}{1152},qquad rac7{192}
   =rac{42}{1152},                                    	ag{24}
]

while the target has trace

[
 rac1{18}=rac{64}{1152}.                            	ag{25}
]

Thus (23) has spare target capacity rather than a Hall excess.  Tensoring
(23) with any Lin occurrence PVM can only apply the block formula (16);
it cannot increase either number in (24).

The three-hidden-line sum repairs the source rank, but its collected
(h)-Fourier router loses a quarter and collides two-to-one, returning
exactly to the bounds used in (21)--(22).  Its uncollected selector is
not a full-(C=langle k,hangle) coefficient.  Qutrit Pauli
exactification changes none of these head calculations.

## 6. The exact surviving syntax

Let (mathcal D) be the algebra generated by the occurrence PVM
((p_i)).  It is the diagonal algebra

[
 mathcal D=left{sum_ilambda_i p_i:lambda_iin
 mathbb Cight}.                                     	ag{26}
]

Every head/occurrence expression in (Motimesmathcal D) has the
form (13), so (16)--(19) exhaust it.  Therefore an escape from the
diagonal occurrence theorem must use some occurrence operator
(ain A) with

[
 p_iap_j
e0qquad	ext{for some }i
e j.               	ag{27}
]

Equation (27) is necessary, not sufficient.  It says exactly that the
row is nonreducing across positive Lin atoms.  To address the current
head firewall, the same bounded expression must also retain raw positive
and negative Leavitt letters and have a genuine full-(C) Fourier
covariance.  Otherwise it falls respectively into the one-orientation
finite/RF envelopes or the collected rank bounds above.

This isolates the bounded mixed-row target without pretending that the
existing qutrit self-test supplies it:

[
 oxed{	ext{raw }S/T	ext{ coefficient}
 ;+;	ext{full-}C	ext{ covariance}
 ;+;p_iap_j
e0.}                                     	ag{28}
]

A uniform singular floor and full trace-(1/18) target are additional
analytic requirements.  The published qutrit low-degree theorem supplies
the coordinate packet only; equations (8), (16), and (27) show where the
occurrence compiler must add genuinely new mathematics.
