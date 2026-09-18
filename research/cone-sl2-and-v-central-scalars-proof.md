---
rg: 2
id: cone-sl2-and-v-central-scalars-proof
kind: route
title: V moves the cone diagonal diag(λ, λ^-1) to any cone pair, two such moves telescope to a single cone scalar, and two cone scalars multiply to λ
target: cone-sl2-and-v-put-central-scalars-in-derived-subgroup
requires:
  - thompson-v-finitely-presented-infinite-simple
  - leavitt-scalar-commutators-block-fp-central-quotients
---

For `λ ∈ K^x` and a nonempty word `c` put `e_c(λ) = λ p_c + (1 - p_c)`. It is a unit with
inverse `e_c(λ^(-1))`, since `λ` is central. Elements `e_c(λ)` for pairwise comparable or
disjoint cones commute, and `e_c(λ) = e_(c1)(λ) e_(c2)(λ)` because
`p_c = p_(c1) + p_(c2)`. For disjoint `x, y` put `h_(x,y)(λ) = e_x(λ) e_y(λ)^(-1)`.

1. **The diagonal is in [H,H].** `h_(a,b)(λ)` is the image of `diag(λ, λ^(-1))` in the cone
   copy of `SL_2(K)`. `SL_2(K)` is perfect because `K` is infinite, so its cone copy lies in
   `[H, H]`. Hence `h_(a,b)(λ) ∈ [H, H]`.
2. **V moves it to every admissible pair.** Let `(x, y)` be disjoint cones with
   `p_x + p_y ≠ 1`.
   - The complements of `a ∪ b` and of `x ∪ y` are nonempty finite unions of cones.
     Choose complete prefix codes `(a, b, α_3, ..., α_r)` and `(x, y, β_3, ..., β_r)` of
     equal size `r ≥ 3`, splitting complement words to equalize sizes.
   - Then `g = s_x t_a + s_y t_b + Σ_(i≥3) s_(β_i) t_(α_i) ∈ V` satisfies `g p_a g^(-1) = p_x`
     and `g p_b g^(-1) = p_y`, so `g h_(a,b)(λ) g^(-1) = h_(x,y)(λ)`.
   - `V ≤ H` and `[H,H] ⊴ H`, so `h_(x,y)(λ) ∈ [H, H]`.

   If `R = 0` everything is trivial. Otherwise `V` is a faithful copy by simplicity of `V`
   (`thompson-v-finitely-presented-infinite-simple`), but only the elements `g` are used.
3. **A single cone scalar.** The pairs `(1, 21)` and `(21, 11)` are admissible, with
   nonempty complements `22` and `12 ∪ 22`. So
   ```text
   h_(1,21)(λ) h_(21,11)(λ) = e_1(λ) e_21(λ)^(-1) e_21(λ) e_11(λ)^(-1) = e_1(λ) e_11(λ)^(-1) = e_12(λ)
   ```
   lies in `[H, H]`.
4. **Every cone scalar, then λ.** For a nonempty word `c`, a `V`-element with `g p_12 g^(-1) = p_c`
   exists as in step 2, using codes containing `12` and `c`. It gives
   `e_c(λ) = g e_12(λ) g^(-1) ∈ [H, H]`. Hence `λ·1 = e_1(λ) e_2(λ) ∈ [H, H]`. It is central
   in `R^x`, hence in `Z(H)`. This proves part 1.
5. **Part 2.** `K^x` is not finitely generated, since `K` is infinite. By part 1,
   `K^x ≤ Z(H) ∩ [H,H]`. Part 0, the group lemma of
   `leavitt-scalar-commutators-block-fp-central-quotients`, then says `H/C` is not finitely
   presented for any `C` with `K^x ≤ C ≤ Z(H)`.

QED
