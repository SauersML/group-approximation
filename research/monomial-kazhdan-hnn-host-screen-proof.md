---
rg: 2
id: monomial-kazhdan-hnn-host-screen-proof
kind: route
title: Separate the monomial HNN by finite exponent tori and refute every finite-corner correction
target: monomial-kazhdan-hnn-is-rf-but-non-rfd-and-not-vfhs-stable
requires:
  - monomial-ascending-hnn-coset-action-sofic
  - sofic-action-gives-marked-pauli-central-product-microstates
  - strict-compressor-mixed-return-collapses-shared-pauli-sign
  - strict-kazhdan-compressor-forces-non-rfd
  - one-kt-compressor-has-pauli-microstates-with-low-band-leakage
---

# The exact screen for a one-compressor monomial Kazhdan host

Let
\[
 R_+=k[\mathbb N^d]=k[x_1,\ldots,x_d],\qquad
 R_{\mathrm{Laur}}=k[\mathbb Z^d],
\]
let \(T\in\operatorname{SL}_d(\mathbb Z)\) have nonnegative entries and
\(T\mathbb N^d<\mathbb N^d\), and put
\[
 \Gamma=\operatorname{EL}_{\ell}(R_+),\qquad \ell,d\ge3.
\]
The monomial substitution \(x^v\mapsto x^{Tv}\) induces a proper
injective endomorphism \(\alpha=\alpha_T\) of \(\Gamma\).  Let
\[
 V_T=\langle\Gamma,t\mid t\gamma t^{-1}=\alpha(\gamma),
                               \ \gamma\in\Gamma\rangle.   \tag{1}
\]

## 1. Embed the ascending kernel in Laurent elementary matrices

Define the nested monoid rings
\[
 R_j=k[T^{-j}\mathbb N^d]\subseteq R_{\mathrm{Laur}},
 \qquad
 R_\infty=\bigcup_{j\ge0}R_j.                             \tag{2}
\]
They are nested because \(T\mathbb N^d\subseteq\mathbb N^d\).  Multiplication
of exponents by \(T\) is an automorphism of \(R_\infty\): it maps every
stage \(R_{j+1}\) onto \(R_j\), while it maps \(R_0\) into \(R_0\).

The exponent map \(V_T\to\mathbb Z\), \(t\mapsto1\), has kernel
\[
 B=\bigcup_{j\ge0}t^{-j}\Gamma t^j.
\]
Since \(\alpha\) is injective, the usual normal form for an ascending HNN
extension identifies
\[
 B\cong\varinjlim(\Gamma,\alpha)
 \ \leq\ \operatorname{EL}_{\ell}(R_\infty)
 \ \leq\ \operatorname{EL}_{\ell}(R_{\mathrm{Laur}}),     \tag{3}
\]
and
\[
                   V_T=B\rtimes_T\mathbb Z.               \tag{4}
\]

## 2. Finite exponent tori prove residual finiteness

For \(M\ge1\), reduce Laurent exponents modulo \(M\):
\[
 R_{\mathrm{Laur}}\longrightarrow
 A_M=k[(\mathbb Z/M\mathbb Z)^d].                         \tag{5}
\]
This is a finite ring.  Since \(\det T=1\), the reduction of \(T\) is an
automorphism of \((\mathbb Z/M\mathbb Z)^d\), hence an automorphism of
\(A_M\).  Reduction therefore extends from (3)--(4) to a homomorphism
into the finite group
\[
 \rho_M:V_T\longrightarrow
 \operatorname{EL}_{\ell}(A_M)\rtimes
 \langle\overline T\rangle.                              \tag{6}
\]

Let \(g\in V_T\setminus\{1\}\).  If its exponent in \(\mathbb Z\) is
nonzero, a finite cyclic quotient of the exponent map separates it.
Otherwise \(g=b\in B\setminus\{1\}\).  In the matrix realization (3), some
entry \(f\) of \(b-I\) is a nonzero Laurent polynomial.  Its support is a
finite subset of \(\mathbb Z^d\).  Choose \(M\) so large that distinct
support exponents remain distinct modulo \(M\); for example, take \(M\)
larger than every nonzero coordinate difference occurring between two
support exponents.  Their basis vectors in \(A_M\) cannot cancel, so the
reduction of \(f\) is nonzero.  Thus \(\rho_M(b)\ne1\).

This proves that \(V_T\) is residually finite.  In particular it is sofic
and hyperlinear.

## 3. The strict Kazhdan compressor refutes C-star RFD

The universal-lattice property-\((T)\) theorem gives property \((T)\) for
\(\Gamma\), and
\[
                  t\Gamma t^{-1}=\alpha(\Gamma)<\Gamma.   \tag{7}
\]
Let \(p_\Gamma\) be the Kazhdan projection of \(\Gamma\) in the full group
C-star algebra and set
\[
                  e=t p_\Gamma t^{-1}-p_\Gamma.           \tag{8}
\]
By the strict-compressor Kazhdan-projection theorem, \(e\) is a nonzero
projection, while
\[
                  \pi(e)=0                               \tag{9}
\]
for every finite-dimensional representation \(\pi\) of \(V_T\).
Therefore \(C^*_{\max}(V_T)\) is not RFD.  This is fully compatible with
Section 2: the finite quotients separate group elements, not every element
of the full group C-star algebra.

For this monomial inclusion there is also a named noncommutative radical
element.  Put \(S=\alpha_T(R_+)\).  Choose \(f\in R_+\setminus S\), and,
using \(\ell\ge3\), let
\[
       \gamma=e_{23}(f)\in\Gamma,\qquad
       k_0=e_{12}(1)\in\alpha(\Gamma).                    \tag{10}
\]
Direct matrix multiplication gives
\[
       \gamma^{-1}k_0\gamma
          =e_{12}(1)e_{13}(f)\notin\alpha(\Gamma),         \tag{11}
\]
because every matrix in \(\alpha(\Gamma)\) has entries in \(S\).
Thus \(K=\alpha(\Gamma)\) is not normal in \(\Gamma\).

Write \(q=t p_\Gamma t^{-1}\), the Kazhdan projection of \(K\).
In the quasi-regular representation on \(\ell^2(V_T/K)\),
\(q\delta_K=\delta_K\), but (11) says that
\(\delta_{\gamma K}\) is not \(K\)-fixed.  Hence
\[
 [q,\gamma]\delta_K
   =q\delta_{\gamma K}-\delta_{\gamma K}\ne0.             \tag{12}
\]
In every finite-dimensional representation \(q=p_\Gamma\), and
\(p_\Gamma\) commutes with \(\Gamma\), so
\[
 [q,\gamma]\ne0,\qquad
 \pi([q,\gamma])=0\quad(\dim\pi<\infty).                  \tag{13}
\]
This commutator form needs nonnormality of \(K\) in \(\Gamma\); the
projection difference (8) only needs strictness.

## 4. The Pauli extension refutes very-flexible HS stability

Let \(X=V_T/\Gamma\), let \(P_X\) be the common-center Pauli group, and
put
\[
                         \Pi_T=P_X\rtimes V_T.             \tag{14}
\]
The action \(V_T\curvearrowright X\) is sofic by the monomial
ascending-HNN action theorem.  Since \(V_T\) itself is sofic, the marked
Pauli central-product theorem gives
\[
                         \Pi_T\text{ is sofic}.            \tag{15}
\]
Choose canonical permutation/HS microstates
\[
             \Phi_n:\Pi_T\longrightarrow U(d_n).
\]
For the common central involution \(J\), the marked construction gives
\[
             \|\Phi_n(J)-I\|_{2,d_n}\longrightarrow\sqrt2. \tag{16}
\]

Choose
\[
 \gamma_0\in\Gamma\setminus\alpha(\Gamma),\qquad
 r_0=t^{-1}\gamma_0t\notin\Gamma,                         \tag{17}
\]
and a finite Kazhdan set \(Q\) for \(\Gamma\), with constant \(\kappa\).
Write
\[
 A_n=\Phi_n(A_\Gamma),\quad B_n=\Phi_n(B_\Gamma),\quad
 J_n=\Phi_n(J),\quad u_{n,g}=\Phi_n(g).
\]
The group relations imply
\[
\begin{aligned}
 d_{0,n}&=\|A_nB_nA_n^*B_n^*-J_n\|_2\longrightarrow0,\\
 d_{H,n}&=\max_{q\in Q}\|[B_n,u_{n,q}]\|_2\longrightarrow0,\\
 d_{X,n}&=\|[A_n,u_{n,r_0}B_nu_{n,r_0}^*]\|_2
          \longrightarrow0.                              \tag{18}
\end{aligned}
\]

Assume, for contradiction, that \(V_T\) is very-flexibly normalized-HS
stable.  Apply the definition to the actor restrictions
\(u_n:V_T\to U(d_n)\).  There are exact finite-dimensional
representations
\[
 \rho_n:V_T\to U(D_n),\qquad D_n\ge d_n,
\]
and isometries \(W_n:\mathbb C^{d_n}\to\mathbb C^{D_n}\) such that
\[
 \alpha_n=
 \max_{s\in Q\cup\{r_0\}}
 \|W_n^*\rho_n(s)W_n-u_{n,s}\|_{2,d_n}\longrightarrow0.   \tag{19}
\]
No bound on \(D_n/d_n\) is assumed.

The dimension-free mixed-return estimate is
\[
 \|J_n-I\|_{2,d_n}
 \leq d_{0,n}+d_{X,n}+{4\over\kappa}d_{H,n}
      +\left(4+{8\over\kappa}\right)
       \sqrt{\alpha_n^2+6\alpha_n}.                       \tag{20}
\]
Equations (18)--(20) force \(\|J_n-I\|_2\to0\), contradicting (16).
Thus \(V_T\) is not very-flexibly HS-stable.  Since ordinary and flexible
HS stability each imply the very-flexible corner version, both stronger
properties fail as well.

The argument uses only one positive compressor and one mixed-return Pauli
row.  It does not decide the full two-compressor Laurent Kun--Thom actor,
whose Pauli charts require simultaneous noncommuting monomial directions.
