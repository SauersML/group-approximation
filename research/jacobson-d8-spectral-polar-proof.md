---
rg: 2
id: jacobson-d8-spectral-polar-proof
kind: route
title: The t-sign polar has two exact full-source branches and no qutrit bias
target: jacobson-d8-spectral-polar-splits-residual-no-qutrit
requires:
  - jacobson-residual-t-root-is-orthogonal-transport
  - jacobson-pre-reduction-square-forces-sqrt-half-leakage
  - thompson-27-cylinder-qutrit-cell-is-fd-invisible
---

# The t-sign polar has two exact full-source branches and no qutrit bias

Work in the canonical tracial group von Neumann algebra of the Jacobson host.
Put
\[
 e={1\over32}(1-w)(1-v)(1+d)(1-\alpha)(1-r),
 \qquad t=x_{23}(T),\quad k=x_{31}(1),\quad u=tktk=x_{21}(T).
\]
All five factors defining \(e\) commute.  The established root calculations give
\[
 [t,e]=0,\qquad eue=0.
\]
For \(\eta\in\{+1,-1\}\), put
\[
 p_\eta={1+\eta t\over2},\qquad
 V_\eta=\sqrt2\,p_\eta k e,\qquad
 f_\eta=V_\eta V_\eta^*.
\]

## 1. Exact Gram calculation

The identity \(u=tktk\), together with \(t^2=k^2=1\), gives
\[
 ktk=tu.
\]
Consequently
\[
\begin{aligned}
 e k p_\eta k e
 &= {1\over2}e(1+\eta ktk)e\\
 &= {1\over2}e+{\eta\over2}e t u e\\
 &= {1\over2}e.
\end{aligned}
\]
In the last line, \([t,e]=0\) and \(eue=0\) give
\(etue=teue=0\).  Therefore
\[
 V_\eta^*V_\eta=2e k p_\eta k e=e.
\]
Thus \(V_\eta\) is an exact isometry with full source projection \(e\), and
\(f_\eta\) is a projection Murray-von Neumann equivalent to \(e\).
Moreover \(p_+p_-=0\) and \(f_\eta\leq p_\eta\), so
\[
 f_+f_-=0.
\]
This is a genuine two-branch polar decomposition before the fatal
compression \(eue=0\): neither branch loses any part of the residual source.

For comparison with the leakage formulation, if
\(B=eke\), \(p_\eta^0=ep_\eta\), and
\(L_\eta=p_\eta(1-e)ke\), then
\[
 L_\eta^*L_\eta
 = e k p_\eta k e-e k e p_\eta e k e
 = {1\over2}e-Bp_\eta^0B.
\]
The two sign branches therefore resolve the square-root-half leakage exactly.

## 2. An exact degree-four occurrence-typed packet

Consider the four involutions
\[
 D=(x_{14}(Q),x_{43}(1),x_{15}(Q),x_{53}(1)).
\]
They commute with every factor defining \(e\).  They also commute with
\(t=x_{23}(T)\) and with \(u=x_{21}(T)\).  The only potentially nontrivial
commutators with \(u\) have coefficient \(TQ\), and
\[
 TQ=T(1-ST)=T-TST=0
\]
because \(TS=1\).  The two nontrivial pair commutators are
\[
 [x_{14}(Q),x_{43}(1)]=w,\qquad
 [x_{15}(Q),x_{53}(1)]=w,
\]
and all cross commutators vanish.  On the residual corner \(e\), where
\(we=-e\), these are two commuting Pauli pairs and generate
\(M_4(\mathbb C)\) on their occurrence factor.

Since
\[
 k p_\eta k={1+\eta tu\over2}
\]
commutes with every \(D_j\), the conjugate \(kD_jk\) commutes with
\(p_\eta\).  Hence
\[
\begin{aligned}
 V_\eta D_j
 &=\sqrt2\,p_\eta k eD_j\\
 &=\sqrt2\,p_\eta kD_j e\\
 &=\bigl(p_\eta(kD_jk)p_\eta\bigr)V_\eta.
\end{aligned}
\]
The operator on the right preserves \(f_\eta\), because the displayed
intertwining identity and \(D_j^2=1\) imply
\[
 p_\eta(kD_jk)p_\eta\,f_\eta\,
 p_\eta(kD_jk)p_\eta=f_\eta.
\]
Thus each sign branch carries the whole degree-four packet to an exact
degree-four packet on its range.  The construction is support-complete but
degree-neutral: it is \(4\)-to-\(4\), not a hidden \(4\)-to-\(2\) reduction.

## 3. Qutrit marginal calculation

Let \(F_q=\langle J,X_1,Z_1,X_2,Z_2\rangle\) be the order-\(3^5\)
scalar qutrit packet, and put \(C=\langle J,Z_1\rangle\cong C_3^2\).
The support of
\[
 f_\eta=2p_\eta k e k p_\eta
\]
is contained in
\[
 M=\langle N,t,kNk\rangle,
\]
where \(N\) is the elementary abelian group whose character cut is \(e\).
Every element of \(M\) is the identity on the other twenty-five scalar
outer coordinates.  On the other hand, a nonidentity element of \(F_q\)
moves at least eighteen of the twenty-seven qutrit leaves (its fixed set
has size zero or nine).  It follows that
\[
 F_q\cap M=\{1\}.
\]

If \(a\in\mathbb C[F_q]\) and \(b\in\mathbb C[M]\), uniqueness of the
identity term in the product gives
\[
 \tau(ab)=\tau(a)\tau(b).
\]
Indeed, a product \(gm=1\), with \(g\in F_q\) and \(m\in M\), forces
\(g=m=1\).  Since \(f_\eta\) is a projection equivalent to \(e\),
\[
 \tau(f_\eta)=\tau(e)={1\over32}.
\]
Apply the factorization to the qutrit projections \(q,R,q-R\), whose
traces are respectively \(1/3,2/9,1/9\).  Traciality and \(f_\eta^2=f_\eta\)
give
\[
\begin{array}{c|c}
 a & \|f_\eta a\|_2^2=\tau(af_\eta)\\ \hline
 q & 1/96\\
 R & 1/144\\
 q-R & 1/288.
\end{array}
\]
The table is independent of \(\eta\).  It is also exactly the residual
source profile.

Therefore the pre-reduction D8 polar is an exact and useful transport, but
its two orthogonal ranges are qutrit-neutral.  No \(2\)-to-\(1\) qutrit
selector, and hence no Hall deficit, follows from this square alone.
Any successful selector must insert an additional overlap that is not
contained in the active three-coordinate subgroup \(M\).
