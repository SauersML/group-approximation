---
rg: 2
id: finite-corner-dilation-collapses-finite-rank-pauli-sign
kind: route
title: Arbitrary finite actor dilations collapse the finite-rank shared Pauli sign
target: very-flexible-actor-stability-closes-finite-rank-pauli-host
requires:
  - padded-actor-correction-collapses-finite-rank-pauli-sign
  - shared-center-pauli-tape-has-same-fp-gate
  - shared-center-extraspecial-wreath-has-fd-invisible-spin-sector
---

# Arbitrary finite actor dilations collapse the finite-rank shared Pauli sign

All Hilbert--Schmidt norms are normalized in the displayed matrix dimension.
This note removes the dimension-ratio hypothesis from the shared-Pauli actor
interface.  It does **not** assert that an actor satisfying the resulting
LLP--RFD hypothesis is presently known.

## 1. A unitary compression can be completed block diagonally

Let (Uin U(d)), (Win U(D)), (Dge d), and let
(V:mathbb C^d	omathbb C^D) be an isometry.  Put
[
 a=|V^*WV-U|_{2,d},qquad lambda=sqrt{d/D}.             	ag{1}
]
After one unitary change of coordinates in (mathbb C^D), write
[
 W=egin{pmatrix}A&B\\ C&Eend{pmatrix},qquad A=V^*WV.  	ag{2}
]
There is a unitary (Zin U(D-d)) such that
[
 oxed{quad
 |W-(Uoplus Z)|_{2,D}
 le lambdasqrt{a^2+6a}.
 quad}                                                    	ag{3}
]
For (D=d), interpret the lower-right block as zero-dimensional.

Here is the complete estimate.  With unnormalized Hilbert--Schmidt norm, set
[
 L^2=d-|A|_{m HS}^2.
]
The row and column identities for (W) give
[
 |B|_{m HS}^2=|C|_{m HS}^2=L^2.                    	ag{4}
]
Since (A) is a contraction and (|U|_{m HS}=sqrt d),
[
 L^2=(sqrt d-|A|_{m HS})(sqrt d+|A|_{m HS})
 le 2sqrt d,|U-A|_{m HS}
 =2ad.                                                     	ag{5}
]
Choose a singular-value decomposition
(E=Roperatorname{diag}(s_1,ldots,s_{D-d})S^*), and put
(Z=RS^*).  Since (0le s_jle1),
[
egin{aligned}
 |E-Z|_{m HS}^2
 &=sum_j(1-s_j)^2
 lesum_j(1-s_j^2)\\
 &=operatorname{Tr}(I-E^*E)
 =|B|_{m HS}^2=L^2.                                   	ag{6}
end{aligned}
]
Consequently
[
egin{aligned}
 |W-(Uoplus Z)|_{m HS}^2
 &le da^2+3L^2\\
 &le d(a^2+6a),
end{aligned}                                             	ag{7}
]
which is (3) after division by (D).

The complement (Z) is chosen independently for each unitary.  In
particular, no assertion that a family of complements is multiplicative is
being made or needed.

## 2. Cancellation of the dilation ratio

Let (Gcurvearrowright X=G/Gamma) be transitive and infinite.  Suppose
(Gamma) has a finite Kazhdan set (Q) with constant (kappa>0), and
choose representatives
[
 Gammaackslash G/Gamma
 ={Gamma,Gamma r_1Gamma,ldots,Gamma r_sGamma}.      	ag{8}
]
Put
[
 T=Qcup{r_1,ldots,r_s},qquad
 C_kappa=2+rac{16}{kappa},qquad
 K_kappa=4+rac{32}{kappa}=2C_kappa.                   	ag{9}
]

Let (A,B,J,u_tin U(d)), (tin T), and let (delta) be the maximum
defect of
[
 ABA^*B^*=J,qquad [A,u_q]=[B,u_q]=1quad(qin Q),          	ag{10}
]
and
[
 [C,u_{r_ell}D_0u_{r_ell}^*]=1
 quad(C,D_0in{A,B}, 1leellle s).                   	ag{11}
]
Suppose (ho:G	o U(D)) is a genuine finite-dimensional representation
and (V:mathbb C^d	omathbb C^D) is an isometry.  Define
[
 alpha=max_{tin T}|V^*ho(t)V-u_t|_{2,d}.             	ag{12}
]
Then
[
 oxed{quad
 |J-I_d|_{2,d}
 le C_kappadelta+
 K_kappasqrt{alpha^2+6alpha}.
 quad}                                                    	ag{13}
]

Indeed use the same coordinate change to make (Vmathbb C^d) the first
block for every (ho(t)).  Apply (3) separately to each (t), obtaining
unitaries (z_tin U(D-d)) with
[
 epsilon:=max_{tin T}
 |ho(t)-(u_toplus z_t)|_{2,D}
 lelambdasqrt{alpha^2+6alpha}.                        	ag{14}
]
The padded exact-actor estimate is
[
 lambda|J-I_d|_{2,d}
 lelambda C_kappadelta+K_kappaepsilon.               	ag{15}
]
Substitute (14) and cancel the positive factor (lambda).  This proves
(13).  The key point is that (15) explicitly allows arbitrary,
nonmultiplicative padding matrices (z_t), so polar completion has supplied
exactly the datum that its proof needs.

Equation (13) has no dependence on (D/d).  Thus even a finite exact actor
dilation of arbitrarily large dimension forces (J	o I) whenever
(delta,alpha	o0).

## 3. A conditional nonhyperlinearity theorem

Let
[
 E(X)=langle J,A_x,B_x (xin X)mid
 J^2=A_x^2=B_x^2=1, J {m central}, [A_x,B_x]=J,
]
[
 [A_x,A_y]=[A_x,B_y]=[B_x,B_y]=1 (x
e y)angle          	ag{16}
]
and let (G) permute the sites.  Write
[
 Pi(X)=E(X)times G.                                    	ag{17}
]
The displayed finite-support normal form gives (J
e1).

Assume the action satisfies (8), its stabilizer (Gamma) is Kazhdan, and
the full group (C^*)-algebra (C^*(G)) has the local lifting property and
is residually finite-dimensional.  Then
[
 oxed{Pi(X)	ext{ is not hyperlinear}.}                 	ag{18}
]

Suppose otherwise.  Choose an asymptotically faithful normalized
Hilbert--Schmidt representation
[
 Phi_n:Pi(X)	o U(d_n).                                  	ag{19}
]
Set (A_n=Phi_n(A_o)), (B_n=Phi_n(B_o)),
(J_n=Phi_n(J)), and (u_{n,t}=Phi_n(t)).  The finitely many relations
(10)--(11) have a common defect (delta_n	o0).  Restriction to (G) is an
asymptotic representation.

Fournier-Facio--Willett, arXiv:2603.18456v2, Theorem 1.1 (in the normalized
Hilbert--Schmidt instance made precise in Theorem 7.11), gives
finite-dimensional genuine representations
[
 ho_n:G	o U(D_n)
]
and isometries (V_n:mathbb C^{d_n}	omathbb C^{D_n}), with no bound on
(D_n/d_n), such that
[
 alpha_n=max_{tin T}
 |V_n^*ho_n(t)V_n-u_{n,t}|_{2,d_n}longrightarrow0.    	ag{20}
]
Applying (13) yields
[
 |J_n-I|_{2,d_n}longrightarrow0.                       	ag{21}
]
This contradicts asymptotic faithfulness at the nonidentity element (J).
For the canonical-trace form of a hyperlinear approximation the left side
would instead tend to (sqrt2), but no trace normalization is needed:
any positive asymptotic separation of (J) already contradicts (21).

If (G) is finitely presented, then (Pi(X)) is finitely presented as
well: a Kazhdan discrete group is finitely generated, and the shared-center
Pauli presentation criterion says that finite presentation of (G), finite
generation of (Gamma), and finiteness of (8) are necessary and
sufficient.

## 4. Exact status of the construction problem

The implication above is unconditional, but no actor satisfying all its
hypotheses is currently supplied by this repository or by the cited 2026
LLP--RFD theorem.  Such an actor would itself have relative property
((T)) with respect to the infinite subgroup (Gamma).  Therefore it
would answer positively both of the relevant open directions in
Fournier-Facio--Willett:

- their Question 1.9 asks for LLP in an infinite property-((T)) group or
  a group with relative property ((T)) with respect to an infinite
  subgroup;
- their Question 1.10 asks the analogous RFD question.

Their listed LLP--RFD/FD examples are a-T-menable and hence cannot contain
an infinite Kazhdan subgroup.  Thus (18) is a genuine closure theorem for a
future actor, not an assertion that the missing actor has already been
constructed.
