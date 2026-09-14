---
rg: 2
id: tower-simplicity-topologically-free-proof
kind: route
title: Dense free points replace the small-set partition in the tower proof of simplicity
target: tower-simplicity-holds-for-topologically-free-actions
requires: []
---

Let `L` be finitely generated acting minimally and topologically freely on a Cantor set `Z`, `R = LC(Z,F_2) ⋊ L`,
`G = EL_n(R)`, `n ≥ 3`. Write `u_ℓ` for the unit of `ℓ ∈ L`, `e_U` for the indicator of a clopen `U`, and fix word
balls `B_r` for a finite generating set of `L`. Every element of `R` is uniquely `Σ_ℓ f_ℓ u_ℓ` with `f_ℓ ∈ LC(Z,F_2)`,
and `u_ℓ f u_ℓ^(-1) = f ∘ ℓ^(-1)`, so `f u_α · f' u_β = f (f' ∘ α^(-1)) u_(αβ)`.

Let `1 ≠ N ⊴ G` and `1 ≠ g ∈ N`. Let `w` bound the word lengths of the `ℓ` with `f_ℓ ≠ 0` in some entry of `g` or
`g^(-1)`. Call a clopen `V` **small** if `V ∩ ℓV = ∅` for every `ℓ ≠ 1` in `B_(2w)`, and `f ∘ α` is constant on `V`
for every `α ∈ B_w` and every coefficient `f` of an entry of `g^(±1)`.

**1. Small sets are dense.** Each `Fix(ℓ)`, `ℓ ≠ 1`, is closed with empty interior, and `L` is countable, so the free
points are dense by Baire. Given a nonempty clopen `U`, pick a free `x ∈ U`. Then `ℓx ≠ x` for the finitely many
`ℓ ≠ 1` in `B_(2w)`, so some clopen `V` with `x ∈ V ⊆ U` has `V ∩ ℓV = ∅` for all of them; shrinking `V` further makes
the finitely many locally constant functions `f ∘ α` constant on `V`. So **every nonempty clopen set contains a small
one**. (Freeness would give the stronger statement that every clopen set is a finite disjoint union of small ones; that
is the only place the manuscript uses freeness, and it is not needed.)

**2. Some `h = e_(ij)(e_V)` with `V` small does not commute with `g`.** Since `e_(ij)(r) = I + rE_(ij)`, `g` commutes
with `e_(ij)(r)` if and only if `g rE_(ij) = rE_(ij) g`, that is
`g_(pi) r = 0` for `p ≠ i`, `r g_(jq) = 0` for `q ≠ j`, and `g_(ii) r = r g_(jj)`.
Suppose `g` commutes with every `e_(ij)(e_V)`, `V` small, `i ≠ j`.
- Writing `c = Σ_ℓ f_ℓ u_ℓ`, we have `c e_V = Σ_ℓ f_ℓ e_(ℓV) u_ℓ`, since `u_ℓ e_V = e_(ℓV) u_ℓ`.
- If `c e_V = 0` for every small `V`, then `c = 0`: otherwise some `f_ℓ = 1` on a nonempty clopen `U`, and a small
  `V ⊆ ℓ^(-1)U` gives `f_ℓ e_(ℓV) ≠ 0`. The same argument gives `c = 0` from `e_V c = 0` for every small `V`.
- So `g_(pi) = 0` for `p ≠ i` and `g_(jq) = 0` for `q ≠ j`. Letting `i, j` range over all pairs `i ≠ j`, `g` is
  diagonal, say `g = diag(c_1, …, c_n)`, and `c_i e_V = e_V c_j` for `i ≠ j` and every small `V`.
- Compare coefficients at `ℓ`: `f_ℓ e_(ℓV) = e_V f'_ℓ`, where `c_i = Σ f_ℓ u_ℓ` and `c_j = Σ f'_ℓ u_ℓ`. For `ℓ ≠ 1`
  the two sides are supported in the disjoint sets `ℓV` and `V`, so both vanish, and `f_ℓ = 0` by the previous
  bullet. So `c_i, c_j ∈ LC(Z,F_2)`, and `c_i = c_j` on `V` for every small `V`, hence on a dense set, hence
  everywhere.
- So `g = cI` with `c ∈ LC(Z,F_2)` invertible. Over `F_2` the only such `c` is `1`, so `g = 1`, a contradiction.

**3. The tower.** Fix such `h = e_(ij)(e_V)`, put `d = n|B_w|`, and for `a, b ∈ B_w` put `ε_(ab) = e_(aV) u_(ab^(-1))`.
Then `ε_(ab) ε_(a'b') = e_(aV) e_(ab^(-1)a'V) u_(ab'^(-1))`, which is `ε_(ab')` when `b = a'` and `0` otherwise, since
`b^(-1)a' ∈ B_(2w)` and `V` is small. Indexing `F_2^d` by pairs `(p,a)`, `1 ≤ p ≤ n`, `a ∈ B_w`, the map
`ψ(E_((p,a),(q,b))) = ε_(ab) E_(pq)` is linear, injective and multiplicative, and `A ↦ I - ψ(I_d) + ψ(A)` embeds
`GL_d(F_2)` into `GL_n(R)`. Its image `H` lies in `G`: transvections generate `GL_d(F_2)`, one between `(p,a)` and
`(q,b)` with `p ≠ q` is `e_(pq)(ε_(ab))`, and for `p = q` it is a commutator of two such with a third index.

**4. `k = [g,h] ∈ H`.** For `α, β ∈ B_w` and coefficients `f, f'` of entries of `g^(±1)`,
`f u_α · e_V · f' u_β = f e_(αV) (f' ∘ α^(-1)) u_(αβ)`, and `f`, `f' ∘ α^(-1)` are constant on `αV` by smallness, so
this is `0` or `ε_(α, β^(-1))`. The entries of `ghg^(-1) - I = g e_V E_(ij) g^(-1)` are sums of such products, and
`h^(-1) = h`, so `k - I = (ghg^(-1) - h)h` and `k^(-1) - I = h(ghg^(-1) - h)` lie in `ψ(M_d(F_2))`; as `ψ` is
injective and multiplicative, `k ∈ H`. Also `k ≠ 1`.

**5. Conclusion.** `N ∩ H` is a nontrivial normal subgroup of `H ≅ GL_d(F_2) = PSL_d(F_2)`, simple for `d ≥ 3`, so
`H ⊆ N` and `e_(pq)(e_V) ∈ N` for `p ≠ q`. The level `J = {r : e_(pq)(r) ∈ N for all p ≠ q}` is a two-sided ideal
containing `e_V`, so it contains every `e_(ℓV) = u_ℓ e_V u_ℓ^(-1)`. By minimality and compactness finitely many `ℓ_iV`
cover `Z`, so `1 = 1 - Π_i(1 - e_(ℓ_iV)) ∈ J` and `N = G`.

`G` is finitely generated when `R` is, infinite because `e_(12)(LC(Z,F_2))` is infinite, and has property (T) by
`elementary-groups-over-fg-rings-have-property-t` when `R` is a finitely generated ring.

**Model tests.**
- Infinite minimal `Z`-subshift: no periodic points, so every point is free and this recovers the manuscript's proof.
- `L = Z/2 ≀ Δ` on `2^Δ`: free points are the aperiodic configurations, dense; non-free points exist, so the partition
  form genuinely fails and this route is the one that applies.
- Finite `Z`, or a fixed point of the whole action: minimality fails, `L` has a nontrivial quotient acting trivially,
  and the covering step in 5 fails, as it must.
- Non-topologically-free action, for example `L` acting through a proper quotient with a global fixed clopen set: step
  1 fails, and simplicity is false, since the kernel of the restriction gives a proper normal subgroup.
