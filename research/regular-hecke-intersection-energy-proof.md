---
rg: 2
id: regular-hecke-intersection-energy-proof
kind: route
title: Expand the squared transfer through the core double coset
target: regular-hecke-second-moment-is-intersection-energy
requires:
  - regular-core-window-is-a-hecke-kraus-hull
  - hecke-rank-controls-coverage-but-has-half-space-ceiling
---

Let \(P_D\) be the Reynolds projection onto \(D\) and let
\(S=L_{X_0}R_X\) on the full Hilbert--Schmidt space. Since \(S=S^*=S^{-1}\),
the operator \(S P_D S\) is the projection onto \(S D\), and

\[
(P_DSP_D)^*(P_DSP_D)=P_D(SP_DS)P_D.
\]

This proves the principal-angle formula (HMI0). The transfer is the
restriction of \(P_DSP_D\). Therefore

\[
\operatorname{Tr}_D(T_X^2)
 =\operatorname{Tr}_{B(\ell^2G)}(P_DSP_DSP_D)
 =\operatorname{Tr}_{B(\ell^2G)}(P_DSP_DS).
\]

Expand both Reynolds projections. The summand indexed by \(b,c\in B\) is
a left-right multiplier whose left factor is
\(\lambda(bxcx)\) and whose right factor is
\(X\lambda(c^{-1})X\lambda(b^{-1})\). Its supertrace is the product of
the two ordinary traces.

The regular trace of the left factor is nonzero exactly when

\[
bxcx=1.
\]

This occurs precisely for \(c\in I=B\cap xBx\), with
\(b=xc^{-1}x\), and the left trace is then \(|G|\). Substitution gives

\[
\operatorname{Tr}(T_X^2)
 =\frac{|G|}{|B|^2}\sum_{c\in I}
   \operatorname{Tr}\!\left(
   X\lambda(c^{-1})X\lambda(xcx)\right).
\]

Use \(\dim_{\mathbb C}D=q|G|=|G|^2/|B|\) and
\(\tau=\operatorname{Tr}/|G|\) to obtain (HMI1). The sum is real because
it equals the trace of the positive operator \(T_X^2\).

Every factor inside the normalized trace in (HMI1) is unitary, and

\[
\operatorname{Re}\tau(U)=1-\frac12\|U-1\|_2^2.
\]

Summing this identity proves (HMI2) and (HMI3). Finally, every eigenvalue
of \(T_X\) in the indicated near-top band has square at least
\((1-\epsilon)^2\). Its contribution to \(\operatorname{Tr}(T_X^2)\)
proves (HMI4). The prime Iwahori intersection calculation gives (HMI5).
