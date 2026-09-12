---
rg: 2
id: leavitt-tensor-powers-k-theory-via-coherence
kind: route
title: Coherent tensor powers of finite global dimension are regular coherent, so one more Leavitt factor kills K_1 and K_2
target: leavitt-tensor-powers-have-trivial-k-theory
requires:
  - leavitt-tensor-powers-are-left-coherent
  - leavitt-tensor-global-dimension-bound
  - regular-coherent-coefficients-kill-leavitt-tensor-k-theory
---

Let `k = F_2`, `L = L_k(1,2)`, `d >= 3` and `R = L^(⊗(d-1))`, so `d − 1 >= 2`.

1. `R` is left coherent (`leavitt-tensor-powers-are-left-coherent`), and so
   right coherent through its involution.
2. `l.gl.dim R = d − 1 < ∞` (`leavitt-tensor-global-dimension-bound`), on both
   sides. So every finitely presented module has finite projective dimension,
   and `R` is regular coherent.
3. By `regular-coherent-coefficients-kill-leavitt-tensor-k-theory`,
   `K_n(R ⊗ L) = 0` for `n >= 1`. Since `R ⊗ L = L^(⊗d)`,
   `K_1(L^(⊗d)) = K_2(L^(⊗d)) = 0`.
