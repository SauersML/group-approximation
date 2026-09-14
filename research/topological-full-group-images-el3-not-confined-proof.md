---
rg: 2
id: topological-full-group-images-el3-not-confined-proof
kind: route
title: Conjugating diag(a,b,1) by e_31(u^N) writes u^N(a−1) into entry (3,1), so conjugates intersect trivially
target: topological-full-group-images-in-el3-are-not-confined
requires: []
---

**Lemma A.** If `H ≤ G` and there are `k_1, k_2, … ∈ G` with `k_m H k_m^{-1} ∩ k_l H k_l^{-1} = {1}` for `m ≠ l`, then `H`,
and every subgroup of `H`, is not confined.

*Proof.* A finite `P ⊆ G \ {1}` meets at most `|P|` of the conjugates. ∎

**Lemma B.** For `N ≠ M`, `u^N − u^M` is a left non-zero-divisor in `R`.

*Proof.* `u^N − u^M = u^M(u^{d} − 1)` with `d = N − M ≠ 0`, and `u^M` is a unit. Write `r = Σ_{j∈S} f_j u^j ≠ 0`, with `S`
finite and `f_j ≠ 0`. Then `u^d r = Σ_j (f_j∘T^{-d}) u^{j+d}`. If `d > 0`, the exponent `max S + d` occurs in `u^d r` with a
nonzero coefficient but not in `r`, so `u^d r ≠ r`. For `d < 0` use `min S`. ∎

**Computation.** Let `s = u^N`, `k_N = e_31(s) = I + sE_31`, so `k_N^{-1} = I − sE_31`, and let `p = diag(a,b,1)`.
- `(I + sE_31)p = p + saE_31`, because row 1 of `p` is `(a,0,0)`.
- `(p + saE_31)(I − sE_31) = p − psE_31 + saE_31 − saE_31sE_31`.
- Here `psE_31 = sE_31`, because column 3 of `p` is `(0,0,1)^T`, and `E_31E_31 = 0`.
- So `k_N p k_N^{-1} = p + u^N(a − 1)E_31`.

**Intersections.** Suppose `k_N p k_N^{-1} = k_M p' k_M^{-1}` with `p, p' ∈ H` and `N ≠ M`.
- Comparing the diagonal entries gives `a = a'` and `b = b'`, so `p = p'`.
- Comparing entry `(3,1)` gives `(u^N − u^M)(a − 1) = 0`, so `a = 1` by Lemma B.
- By injectivity of the first coordinate on `H`, `p = I`.

So conjugates by `k_1, k_2, …` intersect trivially, and Lemma A applies. ∎

**Instances.**
- For `g ↦ diag(w_g,1,1)` on `[[T]]'`, the first coordinate is `w_g`, and `g ↦ w_g` is injective.
- For `g ↦ diag(w_g,u^{−I(g)},1)` on `[[T]]`, the first coordinate is again `w_g`.

**Firewall.** The hypothesis is needed. `diag(1,b,1)` commutes with every `e_31(r)`, and `diag(1, w_g, 1)` lies in `G` for
`g ∈ [[T]]'`. For subgroups whose elements have first coordinate `1`, use `e_32(u^N)` instead.
