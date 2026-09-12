---
rg: 2
id: stw58-simple-finite-pure-split-stable-surjectivity
kind: claim
title: Unital simple finite pure algebras have compatible split surjections onto stable K-theory in every positive degree
distinct_from:
  stw58-simple-pure-k1-bijective: this concerns all positive homotopy degrees and compatible group splittings across matrix sizes in the finite simple slice, rather than degree-zero K1 bijectivity.
artifacts:
  - research/artifacts/stw58-compatible-split-stable-surjectivity-2026-09-05.md
---

Let \(B\) be a nonzero unital simple finite pure C*-algebra.
For every fixed \(k\ge1\), set
\[
G_m=\pi_k(U(M_m(B)),1_m),\qquad K=K_{k+1}(B).
\]
Let \(t_m:G_m\to G_{m+1}\) be corner stabilization and
\(\sigma_m:G_m\to K\) its stable K-theory map.

There are group homomorphisms \(s_m:K\to G_m\) satisfying
\[
\sigma_ms_m=\operatorname{id}_K,\qquad t_ms_m=s_{m+1}.
\]
Writing \(N_m=\ker\sigma_m\), they give compatible decompositions
\[
G_m\cong K\oplus N_m,\qquad
t_m=\operatorname{id}_K\oplus(t_m|_{N_m}),\qquad
\varinjlim_mN_m=0.
\]

The choice is allowed to depend on \(k\), and is not asserted to come
from a continuous section of unitary spaces. No separability,
nuclearity, exactness, or trace hypothesis is added.

This proves surjectivity onto stable K-theory, not surjectivity of
each consecutive stabilization map and not vanishing of the kernels.
It does not settle STW LVIII.

The same construction also proves that for every locally compact
Hausdorff space \(X\), the canonical map from supported size-one
unitary components of \(C_0(X,B)\) onto \(K_1(C_0(X,B))\) is
surjective. For compact \(X\), use the ordinary unitary group
of \(C(X,B)\). No purity or K1-injectivity of this function algebra
is asserted.

ROUTES

stw58-full-endpoint-matrix-piece-splitting-proof
