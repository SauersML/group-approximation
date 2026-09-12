---
rg: 2
id: leavitt-tensor-k1-coefficient-swindle-proof
kind: route
title: The corner endomorphism fixes B ⊗ 1 and doubles K_1 classes, so those classes vanish
target: leavitt-tensor-kills-k1-of-coefficient-matrices
requires: []
artifacts:
  - research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md
---

Write `s_0 = 1 ⊗ e`, `s_1 = 1 ⊗ f`, `t_0 = 1 ⊗ e*`, `t_1 = 1 ⊗ f*` in
`R = B ⊗ L`, so `t_i s_j = δ_ij` and `s_0 t_0 + s_1 t_1 = 1`.

1. **The corner endomorphism.** `φ(r) = s_0 r t_0 + s_1 r t_1` is a unital ring
   endomorphism of `R`: `φ(r) φ(r') = s_0 r (t_0 s_0) r' t_0 + s_1 r (t_1 s_1) r' t_1
   = φ(r r')`, since the cross terms contain `t_0 s_1 = t_1 s_0 = 0`. Apply it
   entrywise to matrices.
2. **It fixes `B ⊗ 1`.** Each `s_i`, `t_i` commutes with `b ⊗ 1`, so
   `φ(b ⊗ 1) = (b ⊗ 1)(s_0 t_0 + s_1 t_1) = b ⊗ 1`. Hence `φ(X) = X` for
   `X ∈ GL_N(B ⊗ 1)`.
3. **It doubles classes.** Let `S` be the `N × 2N` matrix `(s_0 I_N, s_1 I_N)`
   and `T` the `2N × N` matrix `(t_0 I_N ; t_1 I_N)`. Then `S T = I_N`,
   `T S = I_(2N)`, and `φ(X) = S diag(X, X) T`. Put
   `U = [[S, 0],[0, T]]` and `V = [[T, 0],[0, S]]` in `M_(3N)(R)`, with blocks
   sized `(N | 2N)` by `(2N | N)` and conversely. Then `U V = I` and `V U = I`,
   and `U diag(diag(X,X), I_N) V = diag(S diag(X,X) T, T S) = diag(φ(X), I_(2N))`.
   Conjugation does not change a class in the abelian group `K_1(R)`, so
   `[φ(X)] = [diag(X, X)] = 2[X]`.
4. **Conclusion.** For `X ∈ GL_N(B ⊗ 1)`, `[X] = [φ(X)] = 2[X]`, so `[X] = 0`.
   Since `K_1(R) = GL(R)/E(R)`, some stabilization `diag(X, I_j)` lies in
   `E_(N+j)(R)`. `∎`
