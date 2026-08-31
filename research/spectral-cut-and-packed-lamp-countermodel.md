---
rg: 2
id: spectral-cut-and-packed-lamp-countermodel
kind: route
title: Cut the normal Laplacian and test it on packed coordinate lamps
target: normal-row-averages-need-a-normal-gap
requires:
  - exact-core-domain-does-not-descend-to-normal-quotient
  - cayley-expansion-aligns-isometry-frame-coranges
  - packed-d-coset-flip-has-full-bs-hull
---

# The normal-packet Laplacian has the correct kernel

Every summand in (ANR1) is positive. Therefore

\[
 \ker L_{\mathcal R}
 =\bigcap_{r\in\mathcal R}\ker(\pi(r)-1).
\]

Since \(\mathcal R\) generates \(\Lambda\), this intersection is
\(\mathcal H^{\pi(\Lambda)}=\mathcal K\). Normality gives

\[
 \pi(g)\mathcal K=\mathcal K\qquad(g\in\Gamma),
\]

and unitarity gives the same assertion for \(\mathcal K^\perp\).
Consequently \(P\) commutes with \(\pi(\Gamma)\).

The packet energy is exactly the compression trace

\[
 D_{\mathcal R}(V)^2
 =\frac1d\operatorname{Tr}(V^*L_{\mathcal R}V).          \tag{1}
\]

Combining (1) with (ANR3) yields

\[
 \frac1d\operatorname{Tr}(V^*(1-P)V)\leq\delta.          \tag{2}
\]

This is the complete analytic content of the averaged rows. Without a
lower bound on \(\kappa\), (2) has no dimension-free consequence.

# Spectral cutting gives an exact relative quotient corner

Put

\[
 a=V^*PV.
\]

This is a positive contraction. Since \(P\) commutes with \(\pi(B)\) and
\(V\) intertwines \(\beta\),

\[
 a\in\beta(B)'.
\]

Let

\[
 e=1_{[1/2,1]}(a).
\]

On \(1-e\), the operator \(1-a\) is at least \(1/2\). Hence (2) gives

\[
 \operatorname{rank}(1-e)
 \leq2\operatorname{Tr}(1-a)
 \leq2\delta d.                                         \tag{3}
\]

The compression \(eae\) is invertible on \(e\mathbb C^d\). Define

\[
 W=PV e(eae)^{-1/2}.                                    \tag{4}
\]

Then \(W^*W=e\), its range is contained in \(\mathcal K\), and all factors
in (4) respect the \(B\)-actions. Thus

\[
 \pi(b)W=W\beta(b)e\qquad(b\in B).                       \tag{5}
\]

Because \(\pi|_{\mathcal K}\) kills \(\Lambda\), (5) is a relative corner
of an exact representation of \(\Gamma/\Lambda\).

Both \(W\) and \(Ve\) are isometries on the same domain, and

\[
 W^*Ve=(eae)^{1/2}.
\]

Therefore

\[
 \begin{aligned}
 \|W-Ve\|_{\mathrm F}^2
 &=2\operatorname{rank}e
   -2\operatorname{Tr}((eae)^{1/2})\\
 &\leq2\operatorname{Tr}(e(1-a))
 \leq2\delta d,                                         \tag{6}
 \end{aligned}
\]

where \(1-\sqrt{x}\leq1-x\) on \([0,1]\). Equations (3) and (6) prove
(ANR7).

# Packed lamps saturate the estimate

Identify \(\mathcal H_Q\) with the coordinate space having basis
\((e_q)_{q\in Q}\). The signed-permutation representation of
\((C_2)^Q\rtimes Q\) satisfies

\[
 q(1-2p_1)q^{-1}=1-2p_q.
\]

The hyperplane \(e_1^\perp\) is fixed pointwise by \(z_1\), proving
(ANR10). For \(q\neq1\), the restriction of
\(\pi_Q(z_q)-1=-2p_q\) to this hyperplane has squared Frobenius norm
exactly \(4\); for \(q=1\) it is zero. Thus

\[
 \frac1{M(M-1)}
 \sum_{q\in Q}\|(\pi_Q(z_q)-1)V_Q\|_{\mathrm F}^2
 =\frac{4(M-1)}{M(M-1)}=\frac4M.                        \tag{7}
\]

On the whole host,

\[
 \frac1M\sum_{q\in Q}
  (\pi_Q(z_q)-1)^*(\pi_Q(z_q)-1)
 =\frac4M\sum_{q\in Q}p_q
 =\frac4M I.                                            \tag{8}
\]

A vector fixed by every coordinate reflection has every coordinate zero.
Hence \(\mathcal K=0\). In this model
\(\kappa=4/M\), \(D^2=4/M\), and \(\delta=1\): the spectral-cut theorem is
sharp at the scale relevant to existence of any flat corner.

The actor \(Q\) only permutes the rank-one summands in (8). Thus its
Poincare inequality sees an already constant operator-valued average.
Taking the \(Q\)'s from a uniformly expanding quotient family changes
neither (7) nor (8).

# Why the Iwahori packet is finite but its gap is new

Fix a section \(q\mapsto\widetilde q\) of
\(\Gamma\to\Gamma/\Lambda\), with \(\widetilde1=1\). Reading a word in the
fixed symmetric marking and repeatedly returning to the chosen section
gives the factors

\[
 \widetilde{sq}^{\, -1}s\widetilde q\in\Lambda.
\]

The usual Schreier rewriting proves that these factors, for all quotient
vertices \(q\) and marked edges \(s\), generate \(\Lambda\). Applied to
\(\Lambda_N\triangleleft A\), this is the finite packet (ANR14). Its rows
are the algebraic return maps around the finite deck quotient; applying
the base relation to translated fibers is the equivalent conjugate-row
description.

Consequently a uniform lower bound for the corresponding (ANR1), on the
orthogonal complement of \(\Lambda_N\)-fixed vectors in every candidate
host, would close the averaged-holonomy step by (ANR7). Quotient Cayley
expansion instead concerns variation in the section variable \(q\).
Property \((T;FD)\) concerns the fixed \(A\)-marking. Neither identifies
the growing return operator (ANR1) with a uniformly gapped Laplacian.
The packed calculation (8) is the exact obstruction to making that
identification from equivariance and expansion alone.
