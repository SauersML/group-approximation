---
rg: 2
id: rational-shell-permutations-are-eventually-periodic
kind: claim
title: A suffix-preserving shell permutation is a rational homeomorphism exactly when it is eventually periodic by translation
artifacts:
  - research/artifacts/boone-higman-arithmetic-shell-benchmark-2026-09-08.md
---

Let pi be a permutation of N={0,1,...}. Define h_pi on the binary
Cantor set by fixing p=0^infinity and mapping

    0^n*1*z -> 0^(pi(n))*1*z.

Then h_pi is representable by a finite-state deterministic
asynchronous transducer if and only if some integers m>=1,N>=0
satisfy pi(n+m)=pi(n)+m for all n>=N.

In particular every rational homeomorphism of this precise form
has bounded shell-index displacement |pi(n)-n|. Piecewise-affine
formulas on residue classes with different eventual slopes do
not suffice for deterministic finite-state realization of h_pi.
This is a statement about the specified shell action.
