---
rg: 2
id: sl3-congruence-transfer-kills-abelianization-proof
kind: route
title: Evaluate the transfer through the orbit formula; the index term dies mod d^2 and the conjugation term is a commutator with the sum of coset representatives, which is a multiple of X
target: sl3-congruence-transfer-kills-abelianization
requires: []
---

Lane proof (gq-deep-adelic-1), not independently reviewed. Notation as in the target. `G = Γ_d`,
`H = Γ_(d^2)`, `N = n^2 - 1 >= 8`, and `B = G/H ≅ sl_n(Z/d) ≅ (Z/d)^N` via `θ_d`. `H^ab` is identified
with `sl_n(Z/d^2)` through `θ_(d^2)(I + d^2 Z) = Z mod d^2`.

1. **Transfer formula.**
   - Let `x = I + dX ∈ G` and let `f` be the order of `xH` in `B`, i.e. of `X mod d`. So `f | d`, and
     `fX = dW_1` for an integer matrix `W_1`.
   - `H` is normal and `B` abelian, so every `⟨x⟩`-orbit on `G/H` has length `f`.
   - The transfer evaluation formula (e.g. Isaacs, *Finite Group Theory*, Lemma 5.5) gives
     `V(x) = Π_(t ∈ T) t^(-1) x^f t` in `H^ab`, where `T` is a set of representatives of
     `G/⟨x⟩H`, of size `d^N/f`.
2. **The class of x^f.** `x^f = I + Σ_(j>=1) C(f,j) d^j X^j`, so `x^f = I + d^2 W` with
   `W = W_1 + C(f,2) X^2 + d(...)`. Both `W_1` and `X^2` commute with `X`.
3. **Conjugates.** For `t = I + dY_t`, we have `t^(-1) = I - dY_t mod d^2`. So
   `θ_(d^2)(t^(-1) x^f t) = W + d[W, Y_t] mod d^2`.
4. **Sum.** `V(x) ≡ (d^N/f) W + d[W, S] mod d^2`, with `S = Σ_(t∈T) Y_t`.
   - The first term vanishes, since `d^N/f` is a multiple of `d^(N-1)`, hence of `d^2`.
   - The second depends only on `W mod d` and `S mod d`.
5. **The sum of representatives.**
   - The images of the `Y_t` in `Q = B/A`, with `A = ⟨X mod d⟩`, run through `Q` once each. So
     `S mod d` maps to `Σ_(q ∈ Q) q`.
   - In a finite abelian group, elements pair with their inverses. So the sum of all elements equals
     the sum of the elements of order at most `2`, i.e. of `Q[2]`, and this is `0` unless `Q[2]` has
     order `2`.
     - For odd `d`, `Q[2] = 0`.
     - For even `d`, `rank Q[2] = rank Q/2Q >= N - 1 >= 2`, since `A` is cyclic, and the sum of all
       elements of `(Z/2)^r`, `r >= 2`, is `0`.
   - So `Σ_Q q = 0`, and `S ≡ jX mod d` for some integer `j`.
6. **Conclusion.**
   - `[W, S] ≡ j[W_1 + C(f,2)X^2, X] = 0 mod d`, so `d[W, S] ≡ 0 mod d^2` and `θ_(d^2)(V(x)) = 0`.
   - `θ_(d^2)` is injective on `H^ab`, so `V(x) = 0`. This is part 1.
   - Part 2 follows because transfers compose along `Γ_e ⊆ Γ_(d^2) ⊆ Γ_d`. In the direct system every
     class at level `d` dies at level `d^2`, and homology commutes with filtered colimits.
