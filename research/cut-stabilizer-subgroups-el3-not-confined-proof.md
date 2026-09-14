---
rg: 2
id: cut-stabilizer-subgroups-el3-not-confined-proof
kind: route
title: An elementary conjugator removes diagonal survivors (Neumann covering), then far diagonal cuts expel every element with an off-diagonal entry
target: cut-stabilizer-subgroups-of-el3-are-not-confined
requires: []
---

Notation as in the target. Over `F_2`, signs are irrelevant. `D` denotes the diagonal matrices in `G`. `X` is infinite and minimal,
so it has no isolated points and `T` has no periodic points. Every nonempty open `O ⊆ X` is visited by the orbit of `y` at a
set of times with gaps at most some `L_O`: finitely many translates `T^{-s}O` cover `X`.

`π_y` is a representation, because `π_y(ufu^{-1})δ_t = f(T^{t−1}y)δ_t = π_y(f∘T^{-1})δ_t`. Put `σ = π_y(u)`, `σδ_t = δ_{t+1}`, and
`V^{<m} = span{δ_t : t < m}`, `V^{≥m} = span{δ_t : t ≥ m}`. So `σ^m V^{<0} = V^{<m}` and `σ^m V^{≥0} = V^{≥m}`.

**Lemma C (far cuts).**
- Let `q ∈ G` have a nonzero entry `q_ij`, `i ≠ j`. Write `q_ij = Σ_{|k|≤w} r_k u^k`, with `r_{k_0} ≠ 0`, and let `L` be the gap
  bound for `{r_{k_0} = 1}`.
- Let `c = diag(u^{N_1},u^{N_2},u^{N_3}) ∈ G` with `|N_i − N_j| ≥ w + L + 1`. Then `c^{-1}qc ∉ S_y`.

*Proof.*
- The `(i,j)` entry of `c^{-1}qc` is `u^{−N_i}q_iju^{N_j}`, with `π_y` equal to `σ^{−N_i}π_y(q_ij)σ^{N_j}`.
- This preserves `V^{<0}` and `V^{≥0}` iff `π_y(q_ij)` maps `V^{≥N_j}` into `V^{≥N_i}` and `V^{<N_j}` into `V^{<N_i}`.
- Now `π_y(q_ij)δ_t = Σ_k r_k(T^{t+k}y)δ_{t+k}`, and different `k` give different basis vectors.
- **Case `N_i − N_j ≥ w + L + 1`.** The integers `t ∈ [N_j, N_i − w − 1]` number at least `L+1`. So some such `t` has
  `r_{k_0}(T^{t+k_0}y) = 1`. Then `δ_t ∈ V^{≥N_j}`, while `π_y(q_ij)δ_t` has a nonzero component at `t + k_0 < N_i`, so it is
  not in `V^{≥N_i}`.
- **Case `N_j − N_i ≥ w + L + 1`.** Use `t ∈ [N_i + w, N_j − 1]`. Then `δ_t ∈ V^{<N_j}`, and the component at `t + k_0 ≥ N_i`
  is nonzero. ∎

**Lemma D (Neumann).** If a group `A` is a finite union of cosets `x_iH_i`, then some `H_i` has finite index.

*Proof.* Induct on the number of distinct subgroups among the `H_i`.
- With one subgroup, `A` is a finite union of its cosets.
- Otherwise suppose `[A:H_1] = ∞`. Pick a coset `yH_1` different from every `x_iH_1` with `H_i = H_1`. Then
  `yH_1 ⊆ ⋃_{H_i≠H_1} x_iH_i`.
- So each `x_jH_1 = x_jy^{-1}(yH_1)` is covered by cosets of subgroups other than `H_1`.
- Now `A` is covered by cosets of fewer distinct subgroups, and induction applies. ∎

**Lemma E (removing diagonal survivors).** Let `P ⊆ G \ {1}` be finite. There are clopen `V, V'` such that
`l = e_12(e_V)e_13(e_{V'})` satisfies `l^{-1}pl ∉ D` for every `p ∈ P`.

*Proof.*
- `l = I + e_VE_12 + e_{V'}E_13 = l^{-1}`.
- For `q = diag(a,b,c) ∈ D`, a direct computation gives `lql^{-1} = q + (e_Vb + ae_V)E_12 + (e_{V'}c + ae_{V'})E_13`.
- So `p ∈ lDl^{-1}` forces `p_21 = p_23 = p_31 = p_32 = 0`, the diagonal entries `a = p_11`, `b = p_22`, `c = p_33` to be units,
  `p_12 = φ_p(V)` and `p_13 = φ'_p(V')`. Here `φ_p(V) = e_Vb + ae_V` and `φ'_p(V') = e_{V'}c + ae_{V'}`.
- Make the clopen sets a group under `Δ`. Then `e_{VΔV_2} = e_V + e_{V_2}`, so `φ_p` and `φ'_p` are homomorphisms.
- So the set of bad pairs `(V,V')` for `p` is empty or a coset of `ker φ_p × ker φ'_p`.
- If no good pair existed, Lemma D would give some `p` with `ker φ_p × ker φ'_p` of finite index. Both kernels would then have
  finite index, and Lemma F below gives `a = b = c = 1`. Then `p_12 = e_V + e_V = 0` and `p_13 = 0`, so `p = I`, a
  contradiction. ∎

**Lemma F.** Let `a, b ∈ R^×` and `φ(V) = e_Vb + ae_V`. If `ker φ` has finite index, then `a = b = 1`.

*Proof.* The only unit of `R` inside `LC(X,F_2)` is `1`.

**(i) `a ∉ LC(X,F_2)`.**
- Then some coefficient `a_j`, `j ≠ 0`, is `1` on a nonempty clopen `O`.
- Since `ae_W = Σ_m a_me_{T^mW}u^m`, the `u^j` coefficient of `(1 + e_W)ae_W` is `a_je_{T^jW∖W}`.
- Also `φ(W) = 0` implies `(1 + e_W)ae_W = (1 + e_W)e_Wb = 0`.
- For every `k`, choose points `z_0,…,z_k ∈ O` such that the points `z_i` and `T^{-j}z_i` are pairwise distinct. This is
  possible since `O` is infinite and `T` has no periodic points.
- Choose disjoint clopen neighbourhoods `W_i ∋ T^{-j}z_i` that contain no `z_{i'}` and satisfy `T^jW_i ⊆ O`.
- For every nonempty union `W` of the `W_i`, some `z_i ∈ T^jW ∖ W` has `a_j(z_i) = 1`, so `φ(W) ≠ 0`.
- So `S ↦ ⋃_{i∈S}W_i` injects `F_2^{k+1}` into the quotient by `ker φ`, and the index is at least `2^{k+1}` for every `k`.

**(ii) `a = 1`.** Then `φ(W) = e_W(b − 1)`. If `b ≠ 1`, some coefficient of `b − 1` is `1` on a nonempty clopen `O`.
Disjoint nonempty clopens `W_0,…,W_k ⊆ O` have `φ(W) ≠ 0` for every nonempty union, so the index is infinite again. ∎

**Proof of the theorem.** Let `P ⊆ G \ {1}` be finite.
1. Lemma E gives `l`. Then every element of `Q = l^{-1}Pl` is nontrivial and not diagonal, so it has a nonzero off-diagonal
   entry.
2. Let `K` exceed `w + L + 1` for every `q ∈ Q` and its chosen entry.
3. Put `c = diag(u^{−K},1,u^{K})`. This is the Whitehead matrix `diag(a,a^{-1})` in the `(1,3)` block, with `a = u^{−K}`, so
   `c ∈ G`. All three pairwise cut differences are at least `K`.
4. By Lemma C, `c^{-1}qc ∉ S_y` for every `q ∈ Q`.
5. With `g = lc` this says `g^{-1}Pg ∩ S_y = ∅`, i.e. `P ∩ gS_yg^{-1} = ∅`.

So `S_y` is not confined. A set confining a subgroup of `S_y` also confines `S_y`, so no subgroup of `S_y` is confined. ∎

**Tower groups.**
- Take a Kakutani–Rokhlin partition with base `B ∋ y`. Let `τ_m` be the visit times of the orbit of `y` to `B`, with `τ_0 = 0`.
- `π_y(e_{T^aW'}u^{a−b})δ_t` is nonzero only if `T^{t−b}y ∈ W' ⊆ B` with `0 ≤ b < h(W')`. So `t` and `t + a − b` lie in one
  interval `[τ_m, τ_{m+1})`.
- `0` is an endpoint of these intervals, so entries of `GL_3(A(𝒫))` preserve the cut, and `GL_3(A(𝒫)) ∩ G ≤ S_y`.

**Model tests.**
- A finite orbit (periodic `X`) breaks the choice of the points `z_i` in Lemma F, as it should: in finite quotient groups every
  subgroup is confined.
- For `F_3` coefficients, `φ` is no longer additive in `e_V` with this sign convention, and the diagonal torus survives. The
  statement is only claimed over `F_2`.
- The Fibonacci subshift satisfies all hypotheses.
