---
rg: 2
id: renormalizable-thompson-elements-give-negative-baumslag-solitar
kind: claim
title: An element of kV with a height-m renormalization also gives BS(1,-m) inside (k+1)V
requires:
  - renormalizable-thompson-elements-give-baumslag-solitar
distinct_from:
  renormalizable-thompson-elements-give-baumslag-solitar: that gives u with u s u^-1 = s^m; this symmetrizes the element so that it is also conjugate to its inverse, and gets u s u^-1 = s^-m.
  bs-1-m-embeds-in-brin-thompson-3v-for-odd-m: that is BS(1,m) for odd m; the corollary here is BS(1,-m) for the same m.
---

**ESTABLISHED** (lane bh-free-18, elementary lane proof, not reviewed; no priority claimed).

**Statement.** Let `T ∈ kV` act on `X = C^k` with a height-`m` renormalization `(A, φ)`, in the sense of
items 1–3 of `renormalizable-thompson-elements-give-baumslag-solitar`.
- For `j ∈ {0, 1}` put `ι_j(w_1, w_2, …, w_k) = (j w_1, w_2, …, w_k)`.
- Put `T̃ = ι_0 T ι_0^-1 ⊔ ι_1 T^-1 ι_1^-1`. It is `T` on the cone `0·` and `T^-1` on the cone `1·`.
- Let `σ` be the swap `(j w_1, …) ↦ ((1-j) w_1, …)`.

Then:
1. `T̃ ∈ kV`, and `T̃` has the height-`m` renormalization `Ã = ι_0 A ⊔ ι_1 A`,
   `φ̃ = ι_0 φ ι_0^-1 ⊔ ι_1 φ ι_1^-1`;
2. `σ T̃ σ^-1 = T̃^-1`;
3. let `s = T̃ × id`, and let `u ∈ (k+1)V` be given by the criterion, so that `u s u^-1 = s^m`. Then
   `t = u (σ × id)` satisfies `t s t^-1 = s^-m`. So
   `BS(1,-m) = ⟨a, t | t a t^-1 = a^-m⟩ ≅ ⟨s, t⟩ ≤ (k+1)V`, and also `BS(1,m) ≅ ⟨s, u⟩` in the same group.

**Proof.**
1. **`T̃` lies in `kV`.** `ι_j` is a prefix insertion, so `T̃` and `σ` lie in `kV`.
2. **The renormalization.**
   - **The tower.** For `0 ≤ j < m`, `T^-j A = T^{m-j} A`, so the sets `T^-j A` partition `X`, and
     `T^-m A = A`. Hence `Ã, T̃Ã, …, T̃^{m-1}Ã` partition `C^k`, and `T̃^m Ã = Ã`.
   - **The identity on the second copy.** For `a ∈ A`, `T^-m a ∈ A`, and `φ T^m = T φ` gives
     `φ(a) = T φ(T^-m a)`, that is `φ T^-m = T^-1 φ` on `A`. So `φ̃ T̃^m = T̃ φ̃` on `Ã`.
   - **Brick-locality.** `φ̃` is brick-local, because conjugating by `ι_j` preserves brick-locality.
3. **Item 2** is immediate: `σ` swaps the two cones.
4. **Item 3.** `(σ × id) s (σ × id)^-1 = s^-1`, so `t s t^-1 = u s^-1 u^-1 = s^-m`.
5. **Faithfulness.**
   - `s` has infinite order (automatic from the renormalization).
   - `BS(1,-m) = Z[1/m] ⋊ Z`, with `t` acting by `-m`. Let `N` be the kernel of `a ↦ s, t ↦ t`.
   - If `N` meets `Z[1/m]` nontrivially, it contains a nonzero integer multiple of `a`, since it is
     invariant under multiplication by `m`. Then `s` would have finite order.
   - Otherwise `N` embeds in `Z`. For `(q, t^j) ∈ N`, the commutator with `a` lies in `N ∩ Z[1/m] = 0`,
     so `(-m)^j = 1`, `j = 0`, and `N = 1`. ∎

**Corollary** (`bs-1-minus-m-embeds-in-brin-thompson-3v-for-odd-m`). `BS(1,-m) ≤ 3V` for every odd `m ≥ 3`.
