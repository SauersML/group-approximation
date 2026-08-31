---
rg: 2
id: right-core-cayley-toeplitz-window-proof
kind: route
title: Average right-core-equivariant Gram matrices over the finite quotient
target: right-core-cayley-average-gives-toeplitz-window
requires:
  - finite-positive-definite-window-is-a-relative-corner-selector
---

For a right-core-equivariant unitary field \(W_{tb}=Z_t\beta(b)\), set

\[
F(k)=|G|^{-1}\sum_gW_g^*W_{gk}.
\]

Reindexing \(a=cg_i\) writes every Toeplitz block as

\[
F(g_i^{-1}g_j)=|G|^{-1}\sum_cW_{cg_i}^*W_{cg_j},
\]

an average of Gram matrices.  Hence \(F\) is positive definite.
Right equivariance gives \(F(b)=\beta(b)\).  Cauchy--Schwarz applied to

\[
F(s)-U_s=|G|^{-1}\sum_gW_g^*(W_{gs}-W_gU_s)
\]

gives (RCA5).  If the optimized energy is zero, every edge equation holds;
following a presentation loop gives \(U_w=1\).  Conversely an exact
representation gives the zero-energy field \(W_g=U_g\).  Compactness of the
finite product of unitary groups gives attainment and the fixed-level
positive gap off the endpoint set.
