---
rg: 2
id: klein-level-one-splitting-is-outside-adjoint-image
kind: claim
title: The one-level amplification and compression that split the Klein expectation lie outside the adjoint image
distinct_from:
  ternary-adjoint-image-is-balanced: that is the invariant of the adjoint image; this applies it to prefix-code amplifications and kills the literal operator splitting of the Klein expectation.
  projective-ternary-klein-idempotent-is-full: that is the corner equation itself; this only excludes one candidate pair of image-level witnesses.
artifacts:
  - research/artifacts/klein-target-balanced-invariant-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `k = F_3`, `R = L_k(1,2)`, `PG = R^x/{±1}`, and `rho : k[PG] -> R (x) R^op` the adjoint evaluation.
For a complete prefix code `C` put `delta_C = sum_(alpha in C) S[alpha] (x) T[alpha]^op` and, when
`3` does not divide `|C|`, `Psi_C = |C|^-1 sum_(alpha in C) T[alpha] (x) S[alpha]^op`. Then
`Psi_C delta_C = 1 (x) 1`, and each of `delta_C`, `Psi_C` lies in the balanced subalgebra `N` iff
`|C| = 1 mod 3`.

In particular `delta = s_0 (x) t_0 + s_1 (x) t_1` and `Psi = 2(t_0 (x) s_0 + t_1 (x) s_1)`, the
splitting of `rho(e_K) = delta Psi`, have `mu = 1` and `mu' = 2`, so neither lies in `rho(k[PG])`. The
program "realize `delta Psi` in the span of the `Ad(g)`" is dead.

Because `R` is central simple, the same holds for the operators `delta`, `Psi` on `R`. That transfer
cites the simplicity of `R (x) R^op` and is not needed for the tensor statement. Proof: Sections 3 and
4 of the artifact.
