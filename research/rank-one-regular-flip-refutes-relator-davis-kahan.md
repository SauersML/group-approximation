---
rg: 2
id: rank-one-regular-flip-refutes-relator-davis-kahan
kind: claim
title: A rank-one regular flip refutes relator-to-Davis--Kahan control
distinct_from:
  prime-iwahori-endpoint-transfer-is-complete-graph-hecke: that gives a uniform spectral gap at the exact endpoint; this proves that normalized-HS Iwahori residuals do not put the supplied transfer in its operator-norm perturbation basin.
  exact-torsion-frame-has-rank-one-strict-counterpackets: that removes a boundary line from a Weil packet and obstructs same-dimensional exact repair; this stays in one full regular block and only refutes sharp spectral perturbation control.
  packed-d-coset-flip-has-full-bs-hull: that uses a sparse coordinate carrier with full BS hull; this uses the central constant line in the right-regular commutant and has an exactly computable Hecke transfer.
---

Let \(G=\langle B,x\rangle\) be any finite Iwahori quotient, let
\(X_0=\lambda_G(x)\), and retain the exact regular core
\(\lambda_G|_B\). Let \(P\) be the rank-one projection onto the constant
vector in \(\ell^2(G)\). Then

\[
P=\frac1{|G|}\sum_{g\in G}\varrho(g)
 \in\lambda_G(G)',\qquad
C=1-2P,\qquad X=CX_0.                                 \tag{RDK1}
\]

The operator \(C\) is a selfadjoint involution which commutes with every
left regular group operator. Consequently \(X\) is an involution and the
core inversion row is exact:

\[
X\lambda(r)X=\lambda(r^{-1}).                         \tag{RDK2}
\]

For the two square-free cubic words, the canonical endpoint factors commute
with \(C\), so

\[
(X\lambda(t))^3=C,\qquad
(X\lambda(t)^2\lambda(r))^3=C.                        \tag{RDK3}
\]

Thus both normalized-Hilbert--Schmidt residuals equal

\[
\|C-1\|_2=2\|P\|_2=\frac2{\sqrt{|G|}}\longrightarrow0 \tag{RDK4}
\]

along any growing congruence sequence. All other square-free rows are
literal.

Nevertheless the regular Hecke transfer stays maximally far in operator
norm from the canonical endpoint transfer. Since \(C\in D\) and commutes
with \(X_0\),

\[
T_X(A)=T_0(A)C,\qquad T_X=R_C T_0.                    \tag{RDK5}
\]

The vector \(P\) belongs to the canonical top space, and

\[
T_0(P)=P,\qquad T_X(P)=PC=-P.                         \tag{RDK6}
\]

Therefore

\[
\|T_X-T_0\|_{L^2(D)\to L^2(D)}=2.                    \tag{RDK7}
\]

At a prime Iwahori level, every transfer in the regular endpoint orbit is
unitarily conjugate to \(T_0\) and has spectrum \(\{1,-1/p\}\), whereas
\(-1\in\operatorname{spec}(T_X)\). Hence, for every \(U\in U(D)\),

\[
\left\|T_X-T_{U^*X_0U}\right\|_{2\to2}
 \geq1-\frac1p.                                       \tag{RDK8}
\]

For every \(0\leq\epsilon<2\), the sharp near-top spectral projector loses
the \(P\)-direction, so its operator-norm distance from the canonical top
projector is one.

Hence there is no dimension-free function \(f(s)\to0\) for which the
square-free normalized-HS relation defect \(s\) implies either

\[
\|T_X-T_Y\|_{2\to2}\leq f(s)
\]

for a preselected nearby regular endpoint \(Y\), or a Davis--Kahan bound
between their sharp top projectors. The failure occurs in the trivial
whole-group Fourier sector even though the exact endpoint gap is at least
one.

This is not a flexible-corner obstruction. The contraction

\[
A=1-P
\]

is an exact top eigenvector for \(T_X\), satisfies \(A^*A=1-P\), and misses
trace only \(1/|G|\). The almost-full-frame theorem gives

\[
\Delta^{\rm reg}_{G,B}(X)\leq\frac2{\sqrt{|G|}},
\]

which also equals \(\|X-X_0\|_2\). Thus the example identifies the correct
replacement for operator-norm Davis--Kahan: a valid theorem must allow a
spectrally discontinuous exceptional sector and charge only its physical
trace. Proving that trace-flexible statement for arbitrary Iwahori
microstates remains open.

DERIVATION
rank-one-regular-flip-davis-kahan-proof
