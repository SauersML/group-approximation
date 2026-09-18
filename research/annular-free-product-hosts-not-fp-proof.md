---
rg: 2
id: annular-free-product-hosts-not-fp-proof
kind: route
title: Short words see a bounded window of depths, and inside the window the ping-pong free product decides triviality, so one deep annulus can be changed without changing short relations
target: annular-free-product-germ-hosts-are-not-finitely-presented
---

**Item 1.** Suppose `x'` satisfies the relators. Then `s ↦ s`, `x_i ↦ x'_i` extends to a
homomorphism `ψ` from `Γ`, which is the identity on `V`.
- Let `W` be a clopen set disjoint from `sing(x_i)` and `b ∈ V` supported in `W`. Then
  `c = x_i b x_i^(-1)` is `V`-local everywhere:
  - off `x_i(W)` it is the identity near each point;
  - on `x_i(W)` it is a composite of `V`-local germs, since `W` avoids `sing(x_i)` and
    `x_i(W)` avoids `sing(x_i^(-1)) = x_i(sing(x_i))`.

  So `c ∈ V`, because `V` is full, and `x_i b x_i^(-1) = c` is a relation.
- Applying `ψ` gives `x'_i b x'_i^(-1) = c`. So `h = x_i^(-1) x'_i` commutes with every
  `b ∈ V` supported in `W`.
- For a clopen `U ⊆ W`, take `b` swapping the two halves of `U`. It has support `U`, so
  `h(U) = supp(h b h^(-1)) = U`. Clopen sets separate points, so `h` is the identity on
  `W`.
- The union of such `W` is `C ∖ sing(x_i)`, which is dense, so `x'_i = x_i`.

For annular data, apply this with `x_i = ĝ_i`, `sing(ĝ_i) = {p}`.

**Item 2.**
1. *Perturbation.* Let `g_1 != 1`. For large `L`, `q = ρ_L(g_1) != 1` maps `D_L` onto the
   block `E_(L,q) ⊆ X_L`. Take `1 != κ ∈ V` supported in `E_(L,q)`, and put
   `ρ'_L = κ ρ_L κ^(-1)`, with `ρ'_n = ρ_n` for `n != L`.
   - Since `κ` preserves `X_L`, the conjugated `Q_L` still sends `D_L` into `X_L`. So
     ping-pong position, and the whole host node, hold for `ρ'`.
   - For `y ∈ D_L` with `κ(q y) != q y`, `ρ'_L(g_1)(y) = κ(q(y)) != q(y)`. So
     `ρ'_L(g_1) != ρ_L(g_1)`.
2. *Constants.*
   - `c` bounds the prefix lengths in the tables of `S_V^(±1)`.
   - `ℓ_m` bounds those of `ρ_m(g_i)^(±1)`.
   - `M_0 = 0` and `M_(j+1) = M_j + max(c, ℓ_0, ..., ℓ_(M_j))`. Put `B = M_R`, which depends
     only on `R` and on `ρ_m` for `m <= B`.
   - `d` is least such that no nontrivial element of the `R`-ball of `G` lies in `N_d`.
   - `L(R) = d + 2B + max_(m <= B) ℓ_m + 1`.
3. *Two regimes.* Fix a word `w = a_1 ... a_R` and a point `x`, with trajectory
   `x^(R) = x` and `x^(j-1) = a_j(x^(j))`. `ĝ_i` and `ĝ'_i` differ only on `A_L`.
   - *(i)* If no `Ĝ`-letter is applied at a point of `A_L`, the two trajectories coincide.
   - *(ii)* Otherwise, at such a step the point is `0^L 1 z`. By induction in both
     directions, every `x^(j)` has the form `P_j 0^(k_j) 1 z_j`, with `|P_j| <= B` and
     `k_j >= L - B`.
     - A `V`-letter rewrites at most `c` leading symbols.
     - A `Ĝ`-letter at depth `m < |P_j|` rewrites at most `ℓ_m` symbols inside `P_j 0^(k_j)`,
       because `k_j >= ℓ_m`.
     - A `Ĝ`-letter at a point `0^m 1 z_j` keeps `0^m 1` and replaces `z_j` by `ρ_m(g)(z_j)`.
       Here `m ∈ [L - B, L + B]`: a *tail step*.
   - The pair `(P_j, k_j)` evolves by rules that do not depend on `z_j` or on any `ρ_m`
     with `m > B`. So the regime of `x`, and its shallow data, are the same for `ρ` and
     `ρ'`. The regime-(ii) points form cylinders `P 0^k 1 C`, where `0^k` is the unique run
     of length at least `L - B` starting in the first `B + 1` places.
4. *Deciding regime (ii).* On a cylinder `P 0^k 1 C`, `w` acts by
   `P 0^k 1 z ↦ P' 0^(k') 1 Π(z)`, where `(P', k')` is the same for `ρ` and `ρ'`.
   - `Π = ∏_i ρ_(m_i)(h_i)` is taken over the tail steps, with `h_i` generators or inverses
     and `m_i` in the window.
   - Merge consecutive factors with equal `m`, which gives elements of the `R`-ball.
     Delete those trivial in `G`, which are exactly those trivial in `Q_m`, since
     `m >= L - B >= d`.
   - What is left is a reduced word in `*_m Q_m`. By ping-pong, `Π = 1` exactly when it is
     empty, and the same holds for `Π' = ∏ ρ'_(m_i)(h_i)`. So `w` is the identity on the
     cylinder for `ρ` exactly when it is for `ρ'`.
5. *Conclusion.* Together with (i), `w = 1` in `Γ_ρ` exactly when `w = 1` in `Γ_ρ'`.

**Item 3.** If `<V, Ĝ>` were finitely presented with relators of length at most `R_0`,
take `L >= L(R_0)` and `ρ'` from item 2. The relators hold for `ĝ'_i`, so `ĝ'_i = ĝ_i`
by item 1, contradicting `ρ'_L(g_1) != ρ_L(g_1)`.
- `Γ = <V, Ĝ>`. Given `f ∈ Γ`, remove its singular points one at a time. At a singular
  point `q`, compose with `v' s v`, where `v, v' ∈ V`, `s ∈ <Ĝ, τ>`, and `sing(v' s v) = {q}`,
  choosing it to match the germ of `f` at `q`. What remains lies in `V`.
- Finite presentation does not depend on the finite generating set.
