---
rg: 2
id: kt-kernel-overgroup-reduces-to-rank-one-transvections
kind: claim
title: A polynomial-content overgroup of SL_r(A) is polynomial iff its conjugated transvections are, and those with a two-frame of syzygies always are
distinct_from:
  kt-compressor-stable-kernel-overgroups-are-polynomial: that is the open kernel claim for whole groups; this reduces it to the rank-one transvections h e_12(1) h^(-1) and settles those whose column has a unimodular two-frame of syzygies
  kt-compressor-sandwich-equivalent-to-kernel-polynomiality: that removes the SL_d(Z) projection; this works entirely inside SL_r(R)
---

**ESTABLISHED (proposed; proof in `kt-kernel-overgroup-rank-one-transvections-proof`).**
Let `A = F_q[x_1,…,x_d] ⊂ R = F_q[x_1^(±1),…,x_d^(±1)]`, `r ≥ 3`, and let `H ≤ SL_r(R)`
contain `SL_r(A)` with `H ∩ U_ij(R) = U_ij(A)` for all `i ≠ j`. No compressor
stability is assumed. For `h ∈ H` and `i ≠ j` write

```text
T = h e_ij(1) h^(-1) = I + u v^T,   u = h e_i,   v^T = e_j^T h^(-1),   v^T u = 0.
```

1. **(Transvection criterion.)** `H ≤ SL_r(A)` iff `u v^T ∈ M_r(A)` for every such `T`.
   So `kt-compressor-stable-kernel-overgroups-are-polynomial` is equivalent to the same
   statement for the rank-one unipotents `h e_12(1) h^(-1)` in `H`.
2. **(Zero-entry extraction.)** If `u_n = 0` then `v_m u ∈ A^r` for every `m ≠ n`. If
   `v_m = 0` then `u_n v ∈ A^r` for every `n ≠ m`.
3. **(Two-frame case.)** Let `Syz(u) = {c ∈ A^r : c·u = 0}`. If `Syz(u)` contains two
   rows of some `g ∈ SL_r(A)` (a unimodular 2-frame), then `u v^T ∈ M_r(A)`. The same
   holds with `v` in place of `u`.

So a counterexample to the kernel claim, and by
`kt-compressor-sandwich-equivalent-to-kernel-polynomiality` to the whole compressor
sandwich, must contain a transvection `I + uv^T` with non-polynomial `uv^T` in which
neither `Syz(u)` nor `Syz(v)` contains a unimodular 2-frame. This holds for instance for
`u` proportional to `(x_1, x_2, x_3)`: its syzygies are Koszul and lie in
`(x_1,x_2,x_3)A^3`. Such `u` exist in every rank `r`, e.g. `r` distinct monomials of one
degree in two variables. Monomial compressors can move `u` out of the residual class
(`x_1 ↦ x_1x_2^k` creates divisibility and a zero entry). But part 3 then certifies only
`P·(uv^T) ∈ M_r(A)`, i.e. exponents in the cone `∩_P P^(-1)(N^d) ⊋ N^d`. Transferring
polynomiality from `P·Y` back to `Y` is the exact missing step (proof, §4).
