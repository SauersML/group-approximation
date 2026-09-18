---
rg: 2
id: lifted-thompson-t-embeds-in-cantor-integer-maps-by-v-proof
kind: route
title: "Winding labels form a C(C,Z)-valued crossed homomorphism over T whose kernel is trivial"
target: lifted-thompson-t-embeds-in-cantor-integer-maps-by-v
requires:
  - cantor-maps-by-v-embed-in-next-brin-thompson-group
---

Notation as in the claim. Let `r : C → [0,1]` be the binary-value map. Call `y ∈ C` *generic*
if `r(y)` is not a dyadic rational. The generic points are dense in `C`, `r` is injective on
them, and `r(ā y) = ā(r(y))` for `ā ∈ T` and generic `y`, where `ā` also denotes the circle map
on `[0,1) = R/Z`. Generic points go to generic points, because elements of `T` preserve
`Z[1/2]/Z`.

1. **The label is locally constant.** Fix `a ∈ T̄`. Choose a dyadic subdivision
   `[0,1) = ⊔ I_(β_i)` on which `ā` is affine, such that no interval `ā(I_(β_i))` contains `0` in
   its interior. The lift `a` is continuous and increasing on `I_(β_i)`, and it maps `I_(β_i)` onto
   a half-open interval `J + n_i` with `J ⊆ [0,1)`. So `⌊a(x)⌋ = n_i` on `I_(β_i)`. This is step 1
   of `tbar-embeds-in-laurent-leavitt-unit-group-proof`.

   Set `n_a = n_i` on the cone `[β_i]`. This is a locally constant function `C → Z`, and on
   generic `y` it equals `⌊a(r(y))⌋`. Refining the subdivision does not change it.
2. **Cocycle identity.** For `a, b ∈ T̄` and `x ∈ [0,1)` not dyadic, write `b(x) = {b(x)} + n_b(x)`,
   where `{b(x)} = b̄(x)` is the fractional part. Since `a` commutes with integer translation,

   ```text
   a(b(x)) = a(b̄(x)) + n_b(x),   so   ⌊ab(x)⌋ = ⌊a(b̄ x)⌋ + n_b(x).
   ```

   That is, `n_(ab) = n_a ∘ b̄ + n_b` on generic points. Both sides are locally constant on `C`
   and the generic points are dense, so the identity holds on all of `C`.
3. **Homomorphism.** Put `F_a = n_a ∘ ā^(-1)`, so `Φ(a) = (F_a, ā)`. Then

   ```text
   F_(ab) = n_(ab) ∘ (āb̄)^(-1)
          = n_a ∘ ā^(-1) + n_b ∘ b̄^(-1) ∘ ā^(-1)
          = F_a + ā·F_b,
   ```

   using `(ā·f)(y) = f(ā^(-1) y)`. Hence
   `Φ(a)Φ(b) = (F_a + ā·F_b, āb̄) = Φ(ab)`.
4. **Centre.** `z` has `z̄ = id` and `⌊x + 1⌋ = 1` on `[0,1)`, so `Φ(z) = (1_C, id)`.
5. **Injective.** If `Φ(a) = (0, id)`, then `ā = id`. So `a` is a lift of the identity that
   commutes with `z`, which forces `a = z^k`. Then `F_a = k·1_C = 0` gives `k = 0`.
6. **Into 2V.** `T ≤ V`, so `Φ(T̄) ≤ C(C,Z) ⋊ V`. Take `Γ = Z`, embedded in `V` as any cyclic
   subgroup of infinite order. Then `cantor-maps-by-v-embed-in-next-brin-thompson-group` gives
   `C(C,Z) ⋊ V ≤ 2V`. Finally `2V ≤ nV` for `n ≥ 2` by `g ↦ g × id`. ∎

**Check of step 2 on a rotation.** Let `a = b` be the lift of the rotation by `1/2`, that is
`x ↦ x + 1/2`. Then `n_a = 1_([1])`, and `n_(a²) = n_a ∘ ā + n_a = 1_([0]) + 1_([1]) = 1_C`. This
agrees with `a² = z`.
