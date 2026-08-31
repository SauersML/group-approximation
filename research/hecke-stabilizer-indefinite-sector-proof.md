---
rg: 2
id: hecke-stabilizer-indefinite-sector-proof
kind: route
title: Centralize the Hecke dual and exhibit its surviving middle sector
target: hecke-stabilizer-averaging-leaves-indefinite-sector
requires:
  - hecke-frame-failure-has-right-multiplier-dual
  - near-top-hecke-coverage-has-exact-hole-dual
  - regular-core-window-is-a-hecke-kraus-hull
---

Since \(G=\langle B,x\rangle\),

\[
D\cap\{X_0\}'=\{\lambda_G(B),\lambda_G(x)\}'
 =\lambda_G(G)'=\mathbb C[G]^{\rm op}.
\]

For \(L\) in this algebra and \(R\in D\cap\{X\}'\), commute \(L\) past
\(X_0\), commute \(R\) past \(X\), and use \(D\)-bimodularity of \(E_D\)
to obtain \(T_X(LAR)=LT_X(A)R\). Functional calculus makes every spectral
projection of \(T_X\) commute with the corresponding left and right
multiplication operators.

If \(U\in U(C_X)\), right multiplication \(\mathsf R_U:A\mapsto AU\)
preserves the spectral band and

\[
\mathsf R_U^*R_Z\mathsf R_U=R_{UZU^*}.
\]

Conjugating either compressed multiplier inequality and integrating over
\(U(C_X)\) proves the averaging statement. Left multiplication commutes
with \(R_Z\), so the canonical left stabilizer supplies no conjugation of
the multiplier.

For the finite model, reorder the outer tensor factors and write every
element of \({\cal H}\) as \(P\otimes v\), with
\(P\in M_a\otimes M_c\). With normalized traces,

\[
\tau_2\!\left(
 \begin{pmatrix}2&0\\0&-1\end{pmatrix}v^2
\right)=\frac{2-4}{2}=-1.
\]

Since \(\tau_2(v^2)=5/2\), this gives
\(\tau(ZA^*A)=-\tau(P^*P)=-(2/5)\|A\|_2^2\).
The invertibility of \(1\otimes v\otimes1\) proves full right support,
while the displayed strict inequality proves that no sum of
\(A_j^*A_j\) can equal the unit. The orthogonal projection onto this
two-sided module commutes with its left and right unitary actions, so it is
a selfadjoint bimodular contraction with precisely this top band.

Finally, direct multiplication gives
\(\|[W,S_\eta]\|=\eta\), whereas the indicated sharp spectral projection
is moved to its orthogonal complement by \(W\), giving commutator norm one.
This proves the sharp-band firewall.
