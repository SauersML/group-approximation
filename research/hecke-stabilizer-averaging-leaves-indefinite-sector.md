---
rg: 2
id: hecke-stabilizer-averaging-leaves-indefinite-sector
kind: claim
title: Exact Hecke stabilizer averaging leaves an indefinite sector
distinct_from:
  hecke-frame-failure-has-right-multiplier-dual: that gives an arbitrary Farkas separator for frame failure; this identifies the exact stabilizers under which it may be averaged and proves that a full-support indefinite separator can survive them.
  near-top-hecke-coverage-has-exact-hole-dual: that gives a positive majorant dual for optimal contractive coverage; this shows how such a dual may be centralized but why approximate residual symmetries do not preserve its sharp spectral band.
  regular-core-window-is-a-hecke-kraus-hull: that identifies the relative matrix range; this audits the symmetry reduction of the finite Hecke transfer problem.
---

Let \(G=\langle B,x\rangle\) be finite, let
\(D=(\lambda_G(B))'\), \(X_0=\lambda_G(x)\), and let
\(X=X^*=X^{-1}\) be a supplied extender. Put

\[
T_X(A)=E_D(X_0AX),\qquad
C_0=D\cap\{X_0\}',\qquad C_X=D\cap\{X\}'.              \tag{HSA1}
\]

Then

\[
C_0=\lambda_G(G)'=\mathbb C[G]^{\rm op},              \tag{HSA2}
\]

and the Hecke transfer is exactly bimodular in the following sense:

\[
T_X(LAR)=L\,T_X(A)\,R
\quad(L\in C_0,\ R\in C_X,\ A\in D).                  \tag{HSA3}
\]

Consequently every spectral subspace of \(T_X\), in particular

\[
{\cal H}_\epsilon
 =1_{[1-\epsilon,1]}(T_X)L^2(D),                      \tag{HSA4}
\]

is a \(C_0\)--\(C_X\) bimodule.

This gives the strongest canonical exact separator averaging. If
\(Z=Z^*\in D\) satisfies

\[
\tau(Z)>0,\qquad
P_\epsilon R_ZP_\epsilon\preceq0,                     \tag{HSA5}
\]

then Haar averaging over \(U(C_X)\) produces another separator

\[
\overline Z=\int_{U(C_X)}U ZU^*\,dU
 \in C_X'\cap D,\qquad \tau(\overline Z)=\tau(Z).       \tag{HSA6}
\]

The same averaging preserves positivity and the reverse inequality
\(P_\epsilon R_ZP_\epsilon\succeq P_\epsilon\) in the optimal-coverage
dual. The left stabilizer \(C_0=\mathbb C[G]^{\rm op}\) does not further
average \(Z\): left multiplication by \(C_0\) commutes with every right
multiplier \(R_Z\).

Crucially, (HSA6) does not eliminate the indefinite branch, even with full
right support and exact two-sided bimodule symmetry. For arbitrary
\(a,c\geq1\), take

\[
D=M_a\otimes M_2\otimes M_c,\quad
C_0=M_a\otimes1\otimes1,\quad C=1\otimes1\otimes M_c,
\]

and

\[
v=\begin{pmatrix}1&0\\0&2\end{pmatrix},\qquad
{\cal H}=M_a\otimes\mathbb Cv\otimes M_c.              \tag{HSA7}
\]

The subspace \({\cal H}\) is a \(C_0\)--\(C\) bimodule and contains the
invertible element \(1\otimes v\otimes1\), so it has full right support.
Nevertheless

\[
Z=1\otimes
 \begin{pmatrix}2&0\\0&-1\end{pmatrix}
 \otimes1\in C'\cap D                                  \tag{HSA8}
\]

has \(\tau(Z)=1/2\), while for every \(A\in{\cal H}\),

\[
\tau(ZA^*A)
 =-\frac25\|A\|_2^2<0\quad(A\ne0).                    \tag{HSA9}
\]

Thus \(Z\) is already stabilizer-averaged, indefinite, and separates the
unit from the Hecke-frame cone although that subspace has full support.
Taking \(T\) to be the orthogonal projection onto \({\cal H}\) realizes
\({\cal H}\) as the sharp top band of a selfadjoint bimodular contraction.
Hence bimodularity and stabilizer averaging alone cannot prove coverage.

Nor can vanishing approximate covariance be substituted for exact band
invariance. On \(\mathbb C^2\), let

\[
S_\eta=\operatorname{diag}(1,1-\eta),\qquad
W=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]

Then \(\|WS_\eta-S_\eta W\|=\eta\), but

\[
Q_\eta=1_{[1-\eta/2,1]}(S_\eta)
 =\operatorname{diag}(1,0),\qquad
\|WQ_\eta-Q_\eta W\|=1.                               \tag{HSA10}
\]

Therefore even an \(o(1)\) covariance estimate extracted from the four
Iwahori residuals does not justify averaging a certificate inside a moving
sharp near-top band without a spectral-margin estimate or a soft-filter
replacement.

For the regular congruence core,
\(D\cong M_{[G:B]}(\mathbb C[B]^{\rm op})\), and (HSA2)--(HSA6) are exact
at every level. They reduce a candidate certificate to the relative
commutant of the supplied extender's exact stabilizer, but (HSA7)--(HSA10)
show that this formal reduction cannot yield a uniform anti-separator
estimate. One must use additional arithmetic of the concrete Iwahori
Hecke matrix to rule out the surviving sector, or construct it in an
actual congruence sequence. Neither is currently known, so the
nonhyperlinear-group root remains open.

DERIVATION
hecke-stabilizer-indefinite-sector-proof
