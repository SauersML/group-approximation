---
rg: 2
id: hecke-rank-controls-coverage-but-has-half-space-ceiling
kind: claim
title: Hecke spectral rank controls coverage but has a half-space ceiling
distinct_from:
  near-top-hecke-coverage-has-exact-hole-dual: that computes optimal contractive coverage by an SDP; this extracts a dimension lower bound from its positive dual and then computes why that bound cannot close the regular Iwahori problem.
  hecke-top-spectrum-coverage-controls-window: that asks for a unital frame in a near-top band; this separates operator-module coverage from the raw dimension of that band.
  regular-core-window-is-a-hecke-kraus-hull: that gives the finite Hecke transfer; this computes its ordinary supertrace on the regular core.
---

Use the regular finite-core notation, with \(q=[G:B]\),

\[
D=(\lambda_G(B))',\qquad
T_X(A)=E_D(X_0AX),\qquad
Q_\epsilon=1_{[1-\epsilon,1]}(T_X).
\]

Let \(c_\epsilon\) be the optimal contractive coverage from
'near-top-hecke-coverage-has-exact-hole-dual', and put

\[
r_\epsilon=\frac{\operatorname{rank}(Q_\epsilon)}
                  {\dim_{\mathbb C}D}.                 \tag{HRC1}
\]

Then

\[
c_\epsilon\geq r_\epsilon,\qquad
\Delta^{\rm reg}_{G,B}(X)
 \leq\sqrt{2\epsilon+4(1-r_\epsilon)}.                 \tag{HRC2}
\]

Thus near-full spectral rank would indeed produce the finite relative
corner.

For the regular core, however, near-full rank is impossible for a structural
reason. If \(x\notin B\), then for every selfadjoint unitary \(X\),

\[
\operatorname{Tr}_{L^2(D)}(T_X)=0.                    \tag{HRC3}
\]

Since \(T_X\) is a selfadjoint contraction, its eigenvalues lie in
\([-1,1]\). If \(k=\operatorname{rank}(Q_\epsilon)\) and
\(n=\dim_{\mathbb C}D\), (HRC3) gives

\[
0=\sum_{i=1}^n\lambda_i
 \geq k(1-\epsilon)-(n-k),
\]

and hence

\[
r_\epsilon\leq\frac1{2-\epsilon}.                     \tag{HRC4}
\]

In particular \(r_{\epsilon_n}\) cannot tend to one as
\(\epsilon_n\to0\); it is asymptotically at most one half. This applies
to every nondegenerate regular Iwahori quotient before using any of the
four residual estimates.

The trace calculation is exact. Writing \(\widehat B\) for the
irreducible representations of \(B\),

\[
\lambda_G|_B\cong
 \bigoplus_{\pi\in\widehat B}\pi\otimes1_{q d_\pi},
\qquad
D\cong\bigoplus_{\pi\in\widehat B}M_{q d_\pi}.         \tag{HRC5}
\]

For \(Z=(Z_\pi)_\pi\in D\),

\[
\tau(Z)=\frac1{|G|}\sum_\pi d_\pi\operatorname{Tr}(Z_\pi),
\qquad
\dim_{\mathbb C}D=q|G|,                               \tag{HRC6}
\]

so right multiplication satisfies

\[
\operatorname{Tr}_{L^2(D)}(R_Z)
 =\sum_\pi qd_\pi\operatorname{Tr}(Z_\pi)
 =(\dim_{\mathbb C}D)\tau(Z).                         \tag{HRC7}
\]

If \(Z\geq0\) is feasible in the coverage dual,
\(Q_\epsilon R_ZQ_\epsilon\succeq Q_\epsilon\), then

\[
\operatorname{rank}(Q_\epsilon)
 \leq\operatorname{Tr}(Q_\epsilon R_ZQ_\epsilon)
 \leq\operatorname{Tr}(R_Z)
 =(\dim_{\mathbb C}D)\tau(Z).
\]

Minimizing proves (HRC2).

For (HRC3), let \(P_D\) be the Reynolds projection onto \(D\):

\[
P_D=\frac1{|B|}\sum_{b\in B}
 L_{\lambda(b)}R_{\lambda(b)^*}.
\]

The trace of \(T_X\) on \(D\) is the supertrace of
\(P_D L_{X_0}R_XP_D\) on \(B(\ell^2G)\). Cyclicity and \(P_D^2=P_D\)
reduce this to a sum of supertraces of left-right multipliers. Every term
contains

\[
\operatorname{Tr}(\lambda(xb))=0\qquad(b\in B),
\]

because \(x\notin B\). Hence the sum is zero.

At an exact endpoint a much smaller top space already contains the unit
and has coverage one. Thus spectral rank is only a sufficient surrogate,
not the arithmetic invariant. The moving problem remains the
\(D\)-module position of the near-top vectors, equivalently the positive
hole dual, and the nonhyperlinear-group root remains open.

DERIVATION
hecke-rank-half-space-ceiling-proof
