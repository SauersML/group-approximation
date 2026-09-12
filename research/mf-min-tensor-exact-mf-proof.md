---
rg: 2
id: mf-min-tensor-exact-mf-proof
kind: route
title: Embed A in a matrix corona and use exactness of C to move the quotient inside the tensor product
target: mf-min-tensor-exact-mf-is-mf
requires: []
---

1. **Embed A.** `A` is MF, so `A ⊂ Q := ∏_n M_{k_n} / ⊕_n M_{k_n}`
   (Blackadar--Kirchberg, Definition 3.2.1 and Theorem 3.2.2).
2. **Injectivity of min.** The min tensor product is injective, so
   `A ⊗_min C ⊂ Q ⊗_min C` isometrically.
3. **Exactness of C.** Since `C` is exact,
   `0 → (⊕M_{k_n}) ⊗_min C → (∏M_{k_n}) ⊗_min C → Q ⊗_min C → 0` is exact. So
   `Q ⊗_min C = (∏M ⊗_min C)/(⊕M ⊗_min C)`.
4. **Spatial product.** Represent `C` faithfully on `H`. Both `∏M ⊗_min C` and
   `∏_n (M_{k_n} ⊗ C)` act on `(⊕_n ℂ^{k_n}) ⊗ H`, so
   `∏M ⊗_min C ⊂ ∏_n (M_{k_n} ⊗ C)` isometrically.
5. **Intersection.** An element `x ∈ ∏M ⊗_min C` whose components `x_n` tend to 0
   lies in `⊕M ⊗_min C`. With `P_N` the central projection onto the first `N`
   blocks, `(P_N ⊗ 1)x ∈ (⊕_{n≤N} M_{k_n}) ⊗ C` and
   `‖x − (P_N ⊗ 1)x‖ = sup_{n>N} ‖x_n‖ → 0`.
6. By 3–5, `Q ⊗_min C` embeds in `∏_n (M_{k_n} ⊗ C) / ⊕_n (M_{k_n} ⊗ C)`.
7. **MF of the corona.** Each `B_n = M_{k_n} ⊗ C` is MF. A separable subalgebra `D`
   of `∏ B_n/⊕ B_n` is MF by the local characterization (Blackadar--Kirchberg
   Theorem 3.2.2). Given a finite `F ⊂ D` and `ε > 0`, lift each element to a
   sequence `(b_n)`.
   - **Choosing indices:** pick finitely many large indices at which every lift
     nearly attains its norm `limsup_n ‖b_n‖`. At every large index the lifts
     are `ε`-multiplicative and have norm at most `‖d‖ + ε`.
   - **Assembling the model:** take a local matrix model of each chosen `B_n` and
     form their direct sum. It is approximately multiplicative and approximately
     isometric on `F`.
8. So `A ⊗_min C` is MF. MF algebras are stably finite (Blackadar--Kirchberg).
