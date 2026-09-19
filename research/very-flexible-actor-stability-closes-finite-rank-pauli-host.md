---
rg: 2
id: very-flexible-actor-stability-closes-finite-rank-pauli-host
kind: claim
title: Finite-corner actor exactification closes the finite-rank shared-Pauli host
artifacts:
  - research/finite-corner-dilation-collapses-finite-rank-pauli-sign.md
distinct_from:
  finite-rank-pauli-sign-forces-local-flexible-actor-instability: that only treated block-diagonal corrections and needed sublinear padding; this converts an arbitrary compression of an exact finite-dimensional actor into such a correction and cancels the dimension ratio.
  tfd-finite-corner-collapse-and-rfd-firewall: that uses property (T;FD) to round arbitrary finite corners into near-equal-dimensional representations; this directly feeds each finite corner to the shared-Pauli wall and needs no property (T;FD) for the actor.
  shared-center-extraspecial-wreath-has-fd-invisible-spin-sector: that proves exact finite-dimensional invisibility of the sign but leaves approximate representations open; this closes approximate invisibility conditionally on finite-corner exactification of the actor.
---

**ESTABLISHED DIMENSION-FREE REDUCTION; AN LLP--RFD ACTOR IS NOT
CURRENTLY KNOWN.**

Let (Gcurvearrowright X=G/Gamma) be transitive and infinite.  Suppose
(Gamma) has Kazhdan pair ((Q,kappa)) and
[
 Gammaackslash G/Gamma
 ={Gamma,Gamma r_1Gamma,ldots,Gamma r_sGamma}.
]
Put
[
 T=Qcup{r_1,ldots,r_s},qquad
 C_kappa=2+rac{16}{kappa},qquad
 K_kappa=4+rac{32}{kappa}.
]

Let (A,B,J,u_tin U(d)), (tin T), and let (delta) be the largest
defect of the finite shared-Pauli rows
[
 ABA^*B^*=J,qquad [A,u_q]=[B,u_q]=1quad(qin Q),
]
and
[
 [C,u_{r_ell}D_0u_{r_ell}^*]=1
 quad(C,D_0in{A,B}, 1leellle s).
]
For any genuine finite-dimensional representation
(ho:G	o U(D)), (Dge d), and any isometry
(V:mathbb C^d	omathbb C^D), set
[
 alpha=max_{tin T}|V^*ho(t)V-u_t|_{2,d}.
]
Then
[
 oxed{quad
 |J-I_d|_{2,d}
 le C_kappadelta+
 K_kappasqrt{alpha^2+6alpha}.
 quad}                                                    	ag{VFC1}
]
There is no dependence on (D/d).

The underlying completion lemma is explicit.  If (Uin U(d)),
(Win U(D)), and
(a=|V^*WV-U|_{2,d}), then some (Zin U(D-d)) satisfies
[
 |W-(Uoplus Z)|_{2,D}
 lesqrt{rac dD}sqrt{a^2+6a}.                          	ag{VFC2}
]
The off-diagonal leakage has unnormalized squared norm at most (2ad);
polar-completing the lower-right block costs at most one more copy of that
leakage.  Apply (VFC2) separately on the fixed packet (T), then use the
padded shared-Pauli wall.  The factor (sqrt{d/D}) in (VFC2) cancels the
same factor carried by the embedded Pauli sign.

Consequently, if the full group (C^*)-algebra (C^*(G)) has LLP and is
RFD, then the shared-center Pauli semidirect product
[
 Pi(X)=E(X)times G
]
is **not hyperlinear**.  Indeed the Fournier-Facio--Willett finite-corner
theorem (arXiv:2603.18456v2, Theorems 1.1 and 7.11) compresses genuine
finite-dimensional actor representations onto every normalized-HS
asymptotic representation of (G).  Restricting a hypothetical hyperlinear
model of (Pi(X)) to (G), and applying (VFC1), forces its nontrivial
central involution (J) to converge to the identity, contradicting
asymptotic faithfulness.

If (G) is finitely presented, then (Pi(X)) is finitely presented by the
shared-Pauli presentation criterion: (Gamma) is finitely generated,
and the double-coset space is finite.

No present actor is asserted to satisfy LLP and RFD.  Because
(Gamma) is infinite Kazhdan, such a (G) has relative property ((T))
with respect to an infinite subgroup.  Producing this actor would therefore
also give positive examples for the two LLP/RFD questions isolated by
Fournier-Facio--Willett.  The claim is a complete conditional closure, not a
completed construction of a nonhyperlinear group.

DERIVATION
finite-corner-dilation-collapses-finite-rank-pauli-sign
