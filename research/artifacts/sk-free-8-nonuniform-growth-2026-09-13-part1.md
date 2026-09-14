# sk-free-8: Kazhdan groups of non-uniform exponential growth from self-similar rings (part 1: the engine)

Lane sk-free-8, 2026-09-13. Status: established by this lane, UNREVIEWED (queued with sk-verify-13).
- Part 1 is the growth estimate for elementary groups EL_{3·2^n}(A) over any finitely generated ring A of characteristic 2.
- Part 2 derives non-uniform exponential growth for EL_3(R) whenever R ≅ M_2(R), and applies it to G_X and to Leavitt algebras.

The engine transfers Sauer–Schesler's estimate for Aut(F_{4·2^n}) (arXiv:2606.15945, §§3–4) to elementary matrix groups. The combinatorics of the Grigorchuk group is theirs. What is new: the elementary-group version and the self-similar ring input (part 2).

## 0. Growth notation
- For a group G with finite generating set S, γ_G^S(ℓ) = |B_S(ℓ)|.
- γ is submultiplicative, so ω(G,S) := lim_ℓ γ_G^S(ℓ)^{1/ℓ} = inf_ℓ γ_G^S(ℓ)^{1/ℓ} (Fekete).
- ω(G) := inf_S ω(G,S). G has *non-uniform exponential growth* if G has exponential growth and ω(G) = 1.

**Lemma 0.** If γ_G^S(ℓ) ≤ exp(C ℓ^β) for all ℓ ≤ L, with β < 1, then ω(G,S) ≤ exp(C L^{β−1}).
*Proof.* ω(G,S) ≤ γ_G^S(L)^{1/L}. ∎

## 1. Inputs, read at source on MSI (arXiv e-prints, 2026-09-13)
Right actions throughout, as in Sauer–Schesler.
- **𝒢** is the first Grigorchuk group with generators S = {a,b,c,d}, acting on the binary tree with levels X_n = {0,1}^n.
- **𝒢_n** is the image of 𝒢 in Sym(X_n), and S_n = {a_n,b_n,c_n,d_n} are the truncated generators (involutions).
- **Γ_n** is the Schreier graph of 𝒢 on X_n. The fixed vertices are ρ_n = 1^n, η_n = 1^{n−1}0 and θ_n = ρ_n a_n = 01^{n−1}.
- **r_n** = 2^{⌊n/2⌋}.
- For a word w = s_1⋯s_ℓ, the inverted orbit is 𝒪_ω(w) = {ω, ωs_ℓ, ωs_{ℓ−1}s_ℓ, …, ωs_1⋯s_ℓ}.

Inputs:
- **(G1) Grigorchuk,** as restated in arXiv:2606.15945 `thm:G-subexponential`: there are C>0 and 1/2<γ<1 with γ_𝒢^S(n) ≤ exp(Cn^γ).
- **(G2) Bartholdi–Erschler,** Prop. 4.4 and Lemma 4.9 of [BE12], as restated in `thm:BE`: Δ_ρ^S(n) ≤ Cn^α and N_ρ^S(n) ≤ exp(Cn^α), with 0<α<1. Here Δ is the maximal size of an inverted orbit of a word of length ≤ n, and N the number of distinct such orbits.
- **(G3) Sauer–Schesler** `prop:BE-finite`: for all large n, ξ_n ∈ {ρ_n,η_n} and k ≤ r_n, Δ^{S_n}_{ξ_n}(k) ≤ Ck^α and N^{S_n}_{ξ_n}(k) ≤ exp(Ck^α), for the action of 𝒢_n on X_n. The proof is local convergence of Γ_n at ρ_n and η_n to the boundary Schreier graph at 1^∞, via the contracting property.
- **(G4) Sauer–Schesler** `lem:separation`: d_{Γ_n}(ρ_n,η_n) ≥ 2^{n−3} for n ≥ 4.
- **(G5) Sauer–Schesler,** arXiv:2605.30163, proof of Theorem 5.4 (l.1392): the graph on X_n whose edges are the 𝒢_n-translates of {θ_n,ρ_n} is K_{2^{n−1},2^{n−1}}, hence connected. It uses 2-point homogeneity [Bekka–de la Harpe–Grigorchuk, Appendix A2].
- **(G6)** 𝒢 is spherically transitive, so 𝒢_n acts transitively on X_n.

## 2. The generating sets
- Let A be a unital ring of characteristic 2, generated as a ring by a finite set Σ.
- Put Y_n = X_n × {1,2,3}, so |Y_n| = 3·2^n. GL_{Y_n}(A) is the group of invertible Y_n×Y_n matrices, and EL_{Y_n}(A) = ⟨e_{yy′}(r) : y≠y′, r∈A⟩, where e_{yy′}(r) = I + rE_{yy′}.
- For π ∈ Sym(Y_n), P_π is the permutation matrix with P_π^{−1} e_{yy′}(r) P_π = e_{yπ,y′π}(r).
- A matrix g is *supported on* Z ⊆ Y_n if g_{yy′} = δ_{yy′} whenever y ∉ Z or y′ ∉ Z. Matrices supported on disjoint sets commute (block-diagonal in complementary blocks). P_π^{−1} g P_π is supported on Zπ.

**Definition.** T_n(Σ) ⊆ GL_{Y_n}(A) consists of four types.
1. **Type 1:** for s ∈ S_n, the permutation matrix of (x,i) ↦ (xs,i).
2. **Type 2:** the group M_n ≅ Sym(3) of permutation matrices permuting (η_n,1),(η_n,2),(η_n,3) and fixing all other indices.
3. **Type 3:** τ_n, the permutation matrix of the transposition of (ρ_n,1) and (θ_n,1).
4. **Type 4:** ν_n(σ) = e_{(ρ_n,2),(ρ_n,3)}(σ), for σ ∈ Σ ∪ {1}.

So |T_n(Σ)| = 4 + 6 + 1 + |Σ ∪ {1}|, bounded independently of n.

**Lemma 1 (generation).** T_n(Σ) ⊆ EL_{Y_n}(A), and T_n(Σ) generates EL_{Y_n}(A).

*Proof.*
1. **Membership.** Over F_2 the transposition matrix [[0,1],[1,0]] equals e_12(1)e_21(1)e_12(1), since 1+1 = 0. So every permutation matrix lies in EL(F_2), whose image in GL_{Y_n}(A) lies in EL_{Y_n}(A). Types 1–3 are permutation matrices, and type 4 is elementary.
2. **Permutations.** By (G6), conjugates of M_n by words in S_n give Sym({x}×[3]) for every x ∈ X_n, so every transposition inside a fibre lies in ⟨T_n⟩. The 𝒢_n-conjugates of τ_n are the transpositions of (ρ_n g,1) and (θ_n g,1), which are the edges of the connected graph of (G5) on sheet 1. Fibre transpositions and these sheet-1 transpositions are the edges of a connected graph on Y_n, so they generate Sym(Y_n). Hence P_π ∈ ⟨T_n⟩ for all π.
3. **Elementary matrices.** Sym(Y_n) is 2-transitive, so conjugating ν_n(σ) gives e_{yy′}(σ) for all y ≠ y′ and σ ∈ Σ∪{1}. The set {r ∈ A : e_{yy′}(r) ∈ ⟨T_n⟩ for all y≠y′} is closed under sums (e_{yy′}(r)e_{yy′}(s) = e_{yy′}(r+s)) and under products ([e_{yk}(r),e_{ky′}(s)] = e_{yy′}(rs) for k ∉ {y,y′}, using |Y_n| ≥ 3). In characteristic 2, negatives are the elements themselves. So it contains the subring generated by Σ∪{1}, which is A. ∎

**Lemma 2 (commuting supports; S–S `lem:commuting-supports`).** Let n ≥ 5 and let g,h be words over S_n of length ≤ r_n/3. Then every element of M_n^h commutes with τ_n^g and with ν_n(σ)^g. Every τ_n^g commutes with every ν_n(σ)^{g′}, and the ν_n(σ)^g pairwise commute.

*Proof.*
- **Supports.** M_n^h is supported on {η_n h}×[3]; τ_n^g on {(ρ_n g,1),(θ_n g,1)}; ν_n(σ)^g on {(ρ_n g,2),(ρ_n g,3)}.
- **Type 2 against types 3 and 4.** If η_n h = ρ_n g, then d_{Γ_n}(ρ_n,η_n) ≤ 2r_n/3. If η_n h = θ_n g = ρ_n a_n g, it is ≤ 1+2r_n/3. For n ≥ 5 both are < 2^{n−3}, contradicting (G4). So the supports are disjoint.
- **Type 3 against type 4.** The supports lie in sheet 1 and in sheets {2,3}.
- **Type 4 among themselves.** ν_n(σ)^g = e_{(x,2),(x,3)}(σ) with x = ρ_n g. Two such elements with different x have disjoint supports; with the same x they commute, since e_{yy′}(r)e_{yy′}(s) = e_{yy′}(r+s). ∎

**Lemma 3 (normal form; S–S `lem:normal-form`).** Let n ≥ 5 and let w be a word over T_n(Σ)^{±1} of length ℓ ≤ r_n/3. Then w represents p_1p_2p_3p_4, where:
- p_1 is represented by g_1⋯g_ℓ with g_i ∈ S_n ∪ {1};
- p_j = (a_1^{(j)})^{g_1⋯g_ℓ}(a_2^{(j)})^{g_2⋯g_ℓ}⋯(a_ℓ^{(j)})^{g_ℓ} for j = 2,3,4;
- a_i^{(2)} ∈ M_n, a_i^{(3)} ∈ {τ_n,1} and a_i^{(4)} ∈ {ν_n(σ) : σ∈Σ∪{1}} ∪ {1}, with x^g := g^{−1}xg.

*Proof.*
1. Each letter is a type-1 involution, an element of the group M_n, the involution τ_n, or ν_n(σ)^{±1} = ν_n(σ) (characteristic 2). So write the letter t_i as a_i^{(2)}a_i^{(3)}a_i^{(4)}g_i with at most one of the four factors nontrivial.
2. Pushing the g_i to the left gives t_1⋯t_ℓ = g_1⋯g_ℓ ∏_i (a_i^{(2)}a_i^{(3)}a_i^{(4)})^{g_i⋯g_ℓ}.
3. Every suffix g_i⋯g_ℓ has length ≤ r_n/3. By Lemma 2, type-2 conjugates commute with all type-3 and type-4 conjugates, and type-3 conjugates commute with type-4 conjugates. So the product separates as p_2p_3p_4, keeping the relative order within each type. ∎

## 3. The estimate
**Theorem B.** There are C > 0 and β ∈ (0,1), depending only on |Σ|, with the following property. For every unital ring A of characteristic 2 generated as a ring by Σ, all sufficiently large n, and all ℓ ≤ r_n/3,
  γ^{T_n(Σ)}_{EL_{Y_n}(A)}(ℓ) ≤ exp(C ℓ^β).

*Proof.* Let P_j(ℓ) be the set of possible factors p_j in Lemma 3 for words of length ≤ ℓ ≤ r_n/3, and let C_0, α be as in (G3).
- **|P_1(ℓ)|.** p_1 ∈ 𝒢_n is the image of an element of 𝒢 of length ≤ ℓ, so |P_1(ℓ)| ≤ exp(C_1 ℓ^γ) by (G1).
- **|P_2(ℓ)|.** Put u = g_1⋯g_ℓ. The conjugate (a_i^{(2)})^{g_i⋯g_ℓ} is supported on the fibre over η_n g_i⋯g_ℓ ∈ 𝒪_{η_n}(u). There are ≤ exp(C_0ℓ^α) inverted orbits, each of size ≤ C_0ℓ^α (G3). For a fixed orbit O, p_2 lies in ∏_{x∈O} Sym({x}×[3]). So |P_2(ℓ)| ≤ exp(C_0ℓ^α)·6^{C_0ℓ^α}.
- **|P_3(ℓ)|.** The nontrivial conjugates of τ_n are the transpositions of (ρ_n g_i⋯g_ℓ,1) and (θ_n g_i⋯g_ℓ,1).
  - Let ũ = (a_n g_1 a_n)(a_n g_2 a_n)⋯(a_n g_{ℓ−1} a_n)(a_n g_ℓ), a word of length ≤ 3ℓ ≤ r_n.
  - Since θ_n = ρ_n a_n and a_n² = 1, its suffixes give exactly the points ρ_n g_i⋯g_ℓ and θ_n g_i⋯g_ℓ. So p_3 is a permutation of 𝒪_{ρ_n}(ũ)×{1}.
  - Hence |P_3(ℓ)| ≤ exp(C_0(3ℓ)^α)·(C_0(3ℓ)^α)! ≤ exp(C_3 ℓ^α log ℓ).
- **|P_4(ℓ)|.** The conjugates are e_{(x,2),(x,3)}(σ) with x ∈ 𝒪_{ρ_n}(u). By Lemma 2 they commute, and p_4 = ∏_{x∈O} e_{(x,2),(x,3)}(r_x) with r_x in the F_2-span of Σ∪{1}. So |P_4(ℓ)| ≤ exp(C_0ℓ^α)·2^{(|Σ|+1)C_0ℓ^α}.

The ℓ-ball is contained in P_1P_2P_3P_4. Choose β ∈ (max{α,γ},1) and use ℓ^α log ℓ ≤ C_β ℓ^β; the product is ≤ exp(Cℓ^β). ∎

**Remark (scope).** Characteristic 2 is used only in two places: permutation matrices lie in EL, and ν^{−1} = ν. In other characteristics, use signed permutation matrices and count exponents in [−ℓ,ℓ] at each point, as S–S do for Nielsen transvections.

**Corollary B1 (finite simple groups).** With A = F_2 and Σ = ∅, the simple groups SL_{3·2^n}(F_2) have generating sets T_n of bounded size with γ(ℓ) ≤ exp(Cℓ^β) for ℓ ≤ 2^{⌊n/2⌋}/3.
