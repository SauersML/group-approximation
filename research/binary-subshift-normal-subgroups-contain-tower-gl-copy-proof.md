---
rg: 2
id: binary-subshift-normal-subgroups-contain-tower-gl-copy-proof
kind: route
title: Pick the small clopen set where the coefficients of g are constant along the tower, so the commutator is a matrix in one copy of GL_d(F_2)
target: binary-subshift-normal-subgroups-contain-tower-gl-copy
requires: []
artifacts:
  - research/artifacts/sk-simplicity-short-b-proposal-2026-09-13.md
---

Direct proof. The note-ready LaTeX and a verifier checklist are in the artifact. Let `1 ≠ N ⊴ G`, `1 ≠ g ∈ N`, and `w` as in the claim.

1. **Small sets.** Call a clopen `V` small if both hold:
   - `V ∩ T^jV = ∅` for `0 < |j| ≤ 2w`;
   - `f∘T^i` is constant on `V` for all `|i| ≤ w` and every coefficient `f` of an entry of `g` or `g^(-1)`.

   `T` has no periodic points (minimal and infinite), and these finitely many functions are locally constant. So every point has a small clopen neighbourhood. By compactness every clopen set is a finite disjoint union of small ones.

2. **A non-commuting small transvection.** Suppose `g` commutes with `e_ij(e_V)` for all small `V` and all `i ≠ j`.
   - `e_ij` is additive, so `g` commutes with `e_ij(e_V)` for every clopen `V`.
   - `V = X` gives `g = cI_3` with `c = Σ f_j u^j`.
   - Then `e_V c − c e_V = Σ f_j (e_V − e_(T^jV)) u^j = 0` for every `V`.
   - Suppose `f_j(x) = 1` with `j ≠ 0`. Pick a clopen `V ∋ x` with `T^(-j)x ∉ V`. The `u^j` coefficient is then `1` at `x`, a contradiction.
   - So `c ∈ LC(X,F_2)^× = {1}` and `g = 1`, a contradiction.

   So some `h = e_ij(e_V)` with `V` small and nonempty does not commute with `g`.

3. **Tower copy.** For `|a|, |b| ≤ w` put `E_ab = e_(T^aV) u^(a-b)`.
   - `E_ab E_cd = e_(T^aV ∩ T^(a-b+c)V) u^(a-b+c-d) = δ_bc E_ad`, because `0 < |c−b| ≤ 2w` when `b ≠ c`.
   - `φ: M_d(F_2) → M_3(R)`, `E_((p,a),(q,b)) ↦ E_ab E_pq`, is multiplicative and injective, with `φ(I_d) = e_(∪_a T^aV) I_3`.
   - So `A ↦ I_3 − φ(I_d) + φ(A)` is an injective homomorphism `GL_d(F_2) → GL_3(R)`. Call its image `H_V`.
   - `I_d + E_((p,a),(q,b))` with `p ≠ q` maps to `e_pq(E_ab) ∈ G`.
   - For `a ≠ b`, `I_d + E_((p,a),(p,b)) = [I_d + E_((p,a),(q,c)), I_d + E_((q,c),(p,b))]` with `q ≠ p`.
   - Transvections generate `GL_d(F_2) = SL_d(F_2)`, so `H_V ⊆ G`.

4. **The commutator lies in `H_V`.** Let `f, f'` be coefficients as in 1, and `|i|, |j| ≤ w`.
   - `f u^i e_V f' u^j = f e_(T^iV) (f'∘T^(-i)) u^(i+j)`.
   - The coefficient is the indicator of `T^i{x ∈ V : f(T^ix) = f'(x) = 1}`, which is `T^iV` or empty. So the product is `E_(i,-j)` or `0`.
   - The entries of `Y = g h g^(-1) − I_3 = g e_V E_ij g^(-1)` are sums of such products, so `Y ∈ φ(M_d(F_2))`.
   - `h = h^(-1) = I_3 + E_00 E_ij`, so `k = [g,h] = (I_3+Y)h` and `k^(-1) = h(I_3+Y)` lie in `I_3 + φ(M_d(F_2))`.
   - Injectivity of `φ` makes the corresponding `d × d` matrices mutually inverse. So `k ∈ H_V`, and `k ≠ 1`.

5. **Finite simple group.** `N ∩ H_V` is a nontrivial normal subgroup of `H_V ≅ GL_d(F_2) = PSL_d(F_2)`, which is simple for `d ≥ 3`. So `H_V ⊆ N`, and `e_pq(e_V) = e_pq(E_00) ∈ N` for all `p ≠ q`.

6. **Spreading.** Take distinct `i, j, l` and `r, s ∈ R`.
   - `e_il(r e_V) = [e_ij(r), e_jl(e_V)] ∈ N`, then `e_ij(r e_V s) = [e_il(r e_V), e_lj(s)] ∈ N`.
   - By minimality finitely many `T^nV` cover `X`, and `e_(T^nV) = u^n e_V u^(-n)`.
   - So `1 = 1 − Π_n (1 − e_(T^nV))` is a sum of products `r e_V s`, and so is every element of `R`.
   - So `N` contains every `e_ij(r)`, and `N = G`.
