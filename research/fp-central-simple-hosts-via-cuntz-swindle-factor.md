---
rg: 2
id: fp-central-simple-hosts-via-cuntz-swindle-factor
kind: route
title: Tensor a K-free central simple host with one fixed finitely presented central simple Cuntz swindle algebra, which kills K_1 and K_2 of the Leavitt tensor for every input at once
target: decidable-group-algebras-have-fp-central-simple-hosts
requires:
  - decidable-group-algebras-embed-in-fp-central-simple-algebras
  - fp-central-simple-cuntz-swindle-algebra-exists
  - cuntz-swindle-factors-kill-k-theory-of-every-tensor
  - tensor-product-algebra-fp-iff-factors-fp
---

Let `k = F_2`, `L = L_k(1,2)` and `⊗ = ⊗_k`. Let `G` be finitely generated with solvable word problem.

**Step 1 (inputs).** By `decidable-group-algebras-embed-in-fp-central-simple-algebras` there is a
finitely presented central simple `B` and a unital injective `j : k[G] -> B`. By
`fp-central-simple-cuntz-swindle-algebra-exists` there is a finitely presented central simple `A`
with a Cuntz swindle structure. Put `B' = B ⊗ A`.

**Step 2 (embedding).** The map `b -> b ⊗ 1` is unital and injective, because `A ≠ 0` and `k` is a
field. So `k[G] -> B -> B'` is unital and injective.

**Step 3 (finite presentation).** Finitely presented `k`-algebras have finitely presented tensor
products. Present `B'` by the disjoint union of the generators and relations of `B` and of `A`,
together with the commutators `[x, y]` for `x` a generator of `B` and `y` a generator of `A`. This
is the easy direction of `tensor-product-algebra-fp-iff-factors-fp`.

**Step 4 (central simplicity).** Let `B, A` be central simple over `k`. Every element of `B'` can be
written `x = Σ_(i=1)^n b_i ⊗ a_i` with the `a_i` linearly independent.
- **Centre.** If `x` is central, then for every `b ∈ B`, `0 = [b ⊗ 1, x] = Σ [b, b_i] ⊗ a_i`. Hence
  `[b, b_i] = 0` for all `i`, so `b_i ∈ Z(B) = k` and `x = 1 ⊗ a`. Commuting with `1 ⊗ A` gives
  `a ∈ Z(A) = k`. So `Z(B') = k`.
- **Simplicity.** Let `I ≠ 0` be an ideal of `B'`. Choose `0 ≠ x ∈ I` of minimal length `n`, so the
  `b_i` and the `a_i` are both linearly independent.
  - Since `B` is simple, there are `p_j, q_j ∈ B` with `Σ_j p_j b_1 q_j = 1`.
  - Then `x' = Σ_j (p_j ⊗ 1) x (q_j ⊗ 1) = 1 ⊗ a_1 + Σ_(i>=2) b_i' ⊗ a_i` lies in `I`. It is nonzero
    because the `a_i` are independent, so it again has length `n`.
  - For `b ∈ B`, the element `[b ⊗ 1, x'] = Σ_(i>=2) [b, b_i'] ⊗ a_i` lies in `I` and has length
    `< n`, so it is `0`. Hence `b_i' ∈ Z(B) = k` and `x' = 1 ⊗ a` with `a ≠ 0`.
  - Since `A` is simple, `A a A = A`, so `1 ⊗ 1 ∈ I` and `I = B'`.

**Step 5 (the K-gate).** `B' ⊗ L = B ⊗ A ⊗ L ≅ (B ⊗ L) ⊗ A`. By item 1 of
`cuntz-swindle-factors-kill-k-theory-of-every-tensor` with `D = B ⊗ L`, `K_q(B' ⊗ L) = 0` for
every `q ∈ Z`, and in particular `K_1 = K_2 = 0`.

Steps 2–5 give the target for `G`. `∎`

## Remarks

- **Other routes.** Steps 4–5 do not use the form of `B`. Any route that produces a finitely
  presented central simple host and then waits on its Leavitt K-gate can tensor with the same `A`.
  Examples are `boone-higman-via-essential-shell-germ-algebras`, whose second hole is
  `essential-shell-germ-leavitt-tensors-have-fng-steinberg-kernels`, and the Cantor crossed product
  lanes. After tensoring, the K-gate is replaced by the one input-free existence claim
  `fp-central-simple-cuntz-swindle-algebra-exists`.
- **Independence.** The two open prerequisites can fail separately. The embedding claim depends on
  `G` and says nothing about K-theory. The swindle claim is about one algebra and does not mention
  `G`.
