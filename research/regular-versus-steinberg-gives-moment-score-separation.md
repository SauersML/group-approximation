---
rg: 2
id: regular-versus-steinberg-gives-moment-score-separation
kind: route
title: Amplify Steinberg to regular dimension and compare fixed moments
target: bounded-moments-cannot-recover-plancherel-grouping-score
requires:
  - plancherel-score-recovers-reducible-endpoint-grouping
  - steinberg-endpoints-are-indecomposable-but-payload-width-one
---

# Fixed words cannot distinguish the two exact endpoints

Let \(w\in A\) be nontrivial. Choose a matrix representative over
\(\mathbb Z[1/2]\). Since \(w\neq1\) projectively, at least one entry of this
representative differs from the corresponding entry of both scalar matrices
by a nonzero dyadic rational. Only finitely many odd primes divide its
numerator. Hence
\[
 \operatorname{red}_p(w)\neq1
\]
for every sufficiently large odd prime \(p\).

The normalized character of the regular representation is zero away from
the identity. The Steinberg character of
\(\operatorname{PSL}_2(\mathbb F_p)\) has value \(p\) at the identity,
value zero on nontrivial unipotents, and value of absolute value one on
nonidentity semisimple elements. Amplification does not change normalized
characters, so for all sufficiently large \(p\),
\[
 \operatorname{tr}_{d_p}(R_p(w))=0,\qquad
 \left|\operatorname{tr}_{d_p}(S_p(w))\right|
 =\frac{|\chi_{\operatorname{St}_p}(\operatorname{red}_p(w))|}{p}
 \leq\frac1p.                                            \tag{1}
\]
If \(w=1\), both normalized traces are one. Taking the maximum over a fixed
finite set proves (BMS3).

A bounded-degree \(*\)-moment of exact group matrices is the normalized
trace of the single group word obtained by multiplying its entries and
inverses. A fixed finite moment family therefore produces only a fixed
finite word set, so the same argument applies verbatim.

# The full multiplicity scores remain one unit apart

For \(R_p\), the multiplicity of every irreducible \(\rho\) is
\(d_\rho\). Taking \(k=1\) in (PSG2) gives
\[
 \mathfrak R_{G_p}(R_p)=0.                               \tag{2}
\]

For \(S_p\), the only nonzero multiplicity is
\[
 m_{\operatorname{St}_p}=q_p=d_p/p.
\]
At \(k=0\), the numerator of (PSG2) is \(d_p\). For \(k\geq1\), it is
\[
 N_k=p|q_p-kp|+k(d_p-p^2).                               \tag{3}
\]
If \(q_p\geq kp\), then
\[
 N_k=d_p+k(d_p-2p^2)\geq d_p,                            \tag{4}
\]
because
\[
 d_p-2p^2=\frac p2(p^2-4p-1)\geq0
\]
for \(p\geq5\). If \(q_p<kp\), then
\[
 N_k=(k-1)d_p.                                           \tag{5}
\]
The inequality \(q_p>p\) forces \(k\geq2\) in this case, so (5) is again at
least \(d_p\). Thus the minimum numerator is exactly \(d_p\), attained at
\(k=0\), and
\[
 \mathfrak R_{G_p}(S_p)=1.                               \tag{6}
\]
Equations (2) and (6) prove (BMS4).

# Bounded moments do not select a unique moving modulus

For distinct large primes \(p,\ell\), define
\[
 \widetilde R_{p,\ell}
 =R_p^{\oplus |G_\ell|},\qquad
 \widetilde R_{\ell,p}
 =R_\ell^{\oplus |G_p|}.
\]
Both dimensions equal \(|G_p||G_\ell|\). Given a fixed finite word set,
choose \(p,\ell\) outside the finite exceptional prime set for every
nontrivial word in it. Each nontrivial word then has normalized trace zero
in both amplified regular representations, while every identity word has
trace one. Their entire fixed moment windows agree exactly although their
moduli are different.

The examples do not obstruct an adaptive algorithm which inspects a
growing multiplication table, and they do not obstruct congruence capture:
each model is already an exact endpoint. They prove only the sharp
information-theoretic limitation needed here: no dimension-independent
bounded scalar window can output the moving quotient table or the global
Plancherel grouping score.
