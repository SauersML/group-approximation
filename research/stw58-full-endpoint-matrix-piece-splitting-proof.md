---
rg: 2
id: stw58-full-endpoint-matrix-piece-splitting-proof
kind: route
title: Use one full hereditary dimension-drop endpoint piece to split every stable homotopy map compatibly
target: stw58-simple-finite-pure-split-stable-surjectivity
requires: []
artifacts:
  - research/artifacts/stw58-compatible-split-stable-surjectivity-2026-09-05.md
  - research/artifacts/stw58-local-factorization-and-overlap-cancellation-2026-09-05.md
  - notes/stw58-soft-module-compression-attempt-2026-09-05.md
---

Fix \(k\ge1\) and \(N\ge k+2\).

1. Lin's published pure-algebra dichotomy gives stable rank one for
   the unital simple finite pure algebra \(B\).
2. Almost divisibility gives \(Nx\le[1_B]\le(N+1)x\) in
   \(\mathrm{Cu}(B)\). Finite-matrix approximation and compactness of
   \([1_B]\) give the same inequalities for an element of \(W(B)\).
   Rørdam--Winter Proposition 5.1 then supplies a unital homomorphism
   \(Z_{N,N+1}\to B\).
3. At least one of its canonical order-zero supports \(h_i\) is
   nonzero, since \(h_0+h_1=1\). Its hereditary algebra \(C\) is full
   by simplicity. Supporting multiplier matrix units identify
   \(C\cong M_{N+i}(D)\) with \(\operatorname{sr}(D)=1\).
4. The reviewed matrix-piece lemma gives canonical isomorphisms
   \(\pi_kU_m(C)\to K_{k+1}(C)\) for every \(m\ge1\), since
   \(m(N+i)\ge k+2\). Its proof uses
   \(\operatorname{sr}C(S^k,\widetilde D)\le k+2\), Rieffel's
   degree-zero Theorem 2.10, and splitting evaluation and the scalar
   quotient. It does not assume general degree-one injectivity from
   stable rank one.
5. Compose with full hereditary K-theory invariance to obtain
   \(\alpha_m:\pi_kU_m(C)\cong K_{k+1}(B)\). If \(j_m\) is supported
   inclusion, define \(s_m=j_m\alpha_m^{-1}\). Naturality gives both
   \(\sigma_ms_m=1\) and \(t_ms_m=s_{m+1}\).
6. The explicit decomposition
   \(x\mapsto(\sigma_mx,x-s_m\sigma_mx)\) has transition maps equal
   to the identity on K-theory plus the corresponding kernel maps.
   Stable K-theory as the matrix direct limit implies
   \(\varinjlim\ker\sigma_m=0\).
7. For the function-algebra corollary, a matrix unitary over any
   compact Hausdorff \(X\) is approximated by finitely many scalar
   coordinate functions with joint range \(Y\subset[0,1]^r\).
   Polar correction gives its K1-class from \(C(Y,B)\).
   Choose the endpoint size \(N\ge r+2\). The torus/quotient bound
   \(\operatorname{sr}C(Y,\widetilde D)\le r+1\), the split scalar
   quotient, and full hereditary K-theory invariance give a size-one
   representative over \(Y\), hence over \(X\). For locally compact
   \(X\), use the split evaluation extension at infinity and replace
   the representing unitary \(u\) by \(u\,u(\infty)^*\).

Only one nonzero full piece is used. No overlap, sphere fragmentation,
or homotopy-pushout hypothesis is required.

The standalone artifact supplies all proofs, source locations,
nonunital conventions, and the precise remaining injectivity issue.
The published inputs are prior art; no novelty priority is asserted.
