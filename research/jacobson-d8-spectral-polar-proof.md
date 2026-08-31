---
rg: 2
id: jacobson-d8-spectral-polar-proof
kind: proof
title: The t-sign polar has two exact full-source branches and no qutrit bias
target: jacobson-d8-spectral-polar-splits-residual-without-qutrit-selection
requires:
  - jacobson-residual-t-root-is-orthogonal-transport
  - jacobson-pre-reduction-square-forces-sqrt-half-leakage
  - thompson-27-cylinder-qutrit-cell-is-fd-invisible
---

# The t-sign polar has two exact full-source branches and no qutrit bias

Work in the canonical tracial group von Neumann algebra of the Jacobson host.
Put
[
 e={1over32}(1-w)(1-v)(1+d)(1-alpha)(1-r),
 qquad t=x_{23}(T),quad k=x_{31}(1),quad u=tktk=x_{21}(T).
]
All five factors defining (e) commute.  The established root calculations give
[
 [t,e]=0,qquad eue=0.
]
For (etain{+1,-1}), put
[
 p_eta={1+eta tover2},qquad
 V_eta=sqrt2,p_eta k e,qquad
 f_eta=V_eta V_eta^*.
]

## 1. Exact Gram calculation

The identity (u=tktk), together with (t^2=k^2=1), gives
[
 ktk=tu.
]
Consequently
[
egin{aligned}
 e k p_eta k e
 &= {1over2}e(1+eta ktk)e\
 &= {1over2}e+{etaover2}e t u e\
 &= {1over2}e.
end{aligned}
]
In the last line, ([t,e]=0) and (eue=0) give
(etue=teue=0).  Therefore
[
 V_eta^*V_eta=2e k p_eta k e=e.
]
Thus (V_eta) is an exact isometry with full source projection (e), and
(f_eta) is a projection Murray-von Neumann equivalent to (e).
Moreover (p_+p_-=0) and (f_etaleq p_eta), so
[
 f_+f_-=0.
]
This is a genuine two-branch polar decomposition before the fatal
compression (eue=0): neither branch loses any part of the residual source.

For comparison with the leakage formulation, if
(B=eke), (p_eta^0=ep_eta), and
(L_eta=p_eta(1-e)ke), then
[
 L_eta^*L_eta
 = e k p_eta k e-e k e p_eta e k e
 = {1over2}e-Bp_eta^0B.
]
The two sign branches therefore resolve the square-root-half leakage exactly.

## 2. An exact degree-four occurrence-typed packet

Consider the four involutions
[
 D=(x_{14}(Q),x_{43}(1),x_{15}(Q),x_{53}(1)).
]
They commute with every factor defining (e).  They also commute with
(t=x_{23}(T)) and with (u=x_{21}(T)).  The only potentially nontrivial
commutators with (u) have coefficient (TQ), and
[
 TQ=T(1-ST)=T-TST=0
]
because (TS=1).  The two nontrivial pair commutators are
[
 [x_{14}(Q),x_{43}(1)]=w,qquad
 [x_{15}(Q),x_{53}(1)]=w,
]
and all cross commutators vanish.  On the residual corner (e), where
(we=-e), these are two commuting Pauli pairs and generate
(M_4(mathbb C)) on their occurrence factor.

Since
[
 k p_eta k={1+eta tuover2}
]
commutes with every (D_j), the conjugate (kD_jk) commutes with
(p_eta).  Hence
[
egin{aligned}
 V_eta D_j
 &=sqrt2,p_eta k eD_j\
 &=sqrt2,p_eta kD_j e\
 &=igl(p_eta(kD_jk)p_etaigr)V_eta.
end{aligned}
]
The operator on the right preserves (f_eta), because the displayed
intertwining identity and (D_j^2=1) imply
[
 p_eta(kD_jk)p_eta,f_eta,
 p_eta(kD_jk)p_eta=f_eta.
]
Thus each sign branch carries the whole degree-four packet to an exact
degree-four packet on its range.  The construction is support-complete but
degree-neutral: it is (4)-to-(4), not a hidden (4)-to-(2) reduction.

## 3. Qutrit marginal calculation

Let (F_q=langle J,Z_1anglecong C_3^2) be the scalar qutrit subgroup.
The support of
[
 f_eta=2p_eta k e k p_eta
]
is contained in
[
 M=langle N,t,kNkangle,
]
where (N) is the elementary abelian group whose character cut is (e).
Every element of (M) is the identity on the other twenty-five scalar
outer coordinates.  On the other hand, a nonidentity element of (F_q)
moves at least eighteen of the twenty-seven qutrit leaves (its fixed set
has size zero or nine).  It follows that
[
 F_qcap M={1}.
]

If (ainmathbb C[F_q]) and (binmathbb C[M]), uniqueness of the
identity term in the product gives
[
 	au(ab)=	au(a)	au(b).
]
Indeed, a product (gm=1), with (gin F_q) and (min M), forces
(g=m=1).  Since (f_eta) is a projection equivalent to (e),
[
 	au(f_eta)=	au(e)={1over32}.
]
Apply the factorization to the qutrit projections (q,R,q-R), whose
traces are respectively (1/3,2/9,1/9).  Traciality and (f_eta^2=f_eta)
give
[
egin{array}{c|c}
 a & |f_eta a|_2^2=	au(af_eta)\ hline
 q & 1/96\
 R & 1/144\
 q-R & 1/288.
end{array}
]
The table is independent of (eta).  It is also exactly the residual
source profile.

Therefore the pre-reduction D8 polar is an exact and useful transport, but
its two orthogonal ranges are qutrit-neutral.  No (2)-to-(1) qutrit
selector, and hence no Hall deficit, follows from this square alone.
Any successful selector must insert an additional overlap that is not
contained in the active three-coordinate subgroup (M).
