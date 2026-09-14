# sk-cornulier-q7: derived full groups of dyadic substitution subshifts have non-uniform exponential growth (part 2: counting and conclusion)

Lane sk-cornulier-q7, 2026-09-13. Status: UNREVIEWED. Part 1: `research/artifacts/sk-cornulier-q7-nonuniform-growth-2026-09-13-part1.md` (notation §§1–3, and W_n = [[T]]′ in §4).

## 5. Commuting conjugates and normal form
Notation. For g a word in S_n and u ∈ [[T]], put u^g = L_g^{−1} u L_g.
- If u is supported on V × Z for Z ⊆ Y_n, then u^g is supported on V × Zg.
- Type 1 acts trivially on sheets and on V-labels. So if g, g′ both map a point x to x′, then u^g = u^{g′} for every u supported on V×F_x: L_{g′g^{−1}} fixes F_x pointwise.

**Lemma 5.1 (Sauer–Schesler `lem:commuting-conjugates`).** For n large and words g, g′ in S_n of length ≤ r_n, conjugates u^g and (u′)^{g′} of generators of different types among {2,3,4} have disjoint supports, so they commute.
- **Type 3 against type 4:** δ_n lives on sheets {1,2}; type 4 on sheets {3,…,7}; type 1 preserves sheets.
- **Type 2 against types 3 and 4:** the X_n-projections are {η_n g′} and ⊆ {ρ_n g, θ_n g}. Equality would give d_{Γ_n}(ρ_n,η_n) ≤ 2r_n+1 < 2^{n−3}, contradicting (SS3). ∎

**Lemma 5.2 (normal form; S–S `lem:normal-form`).** For n large, every word w over T_n^{±1} of length ℓ ≤ r_n represents p_1p_2p_3p_4, where:
- p_1 = g_1⋯g_ℓ with g_i ∈ S_n ∪ {1};
- p_j = ∏_{i=1}^{ℓ} (a_i^{(j)})^{g_i⋯g_ℓ} for j = 2,3,4;
- a_i^{(2)} ∈ Alt(8)_{η_n}, a_i^{(3)} ∈ {δ_n, 1}, a_i^{(4)} ∈ A_{ρ_n} ∪ {1}.

*Proof.* Each letter is a type-1 involution, an element of the group Alt(8)_{η_n}, the involution δ_n, or an element of the group A_{ρ_n}. Write it as a·g with at most one nontrivial factor and push the g's left:
w = g_1⋯g_ℓ ∏_i a_i^{g_i⋯g_ℓ}.
Every suffix has length ≤ r_n, so by Lemma 5.1 the conjugates of different types commute. Separating types keeps the order within each type. ∎

## 6. Counting
Let P_j(ℓ) be the set of possible j-th factors for words of length ≤ ℓ ≤ r_n/3.
- **|P_1(ℓ)| ≤ exp(C_1ℓ^γ).** p_1 is the image of an element of 𝒢 of length ≤ ℓ (SS1).
- **|P_2(ℓ)| ≤ exp(C_2ℓ^α).**
  - Types 1 and 2 generate the permutational wreath product (∏_x Alt(F_x)) ⋊ 𝒢_n.
  - (a_i^{(2)})^{g_i⋯g_ℓ} lies in Alt(F_x) for x = η_n g_i⋯g_ℓ ∈ 𝒪_{η_n}(g_1⋯g_ℓ).
  - So p_2 is a choice of one element of Alt(8) per point of an inverted orbit.
  - By (SS2): ≤ exp(Cℓ^α)·20160^{Cℓ^α}.
- **|P_3(ℓ)| ≤ exp(C_3ℓ^α log ℓ).**
  - Each nontrivial conjugate δ_n^{g_i⋯g_ℓ} is the same transposition of X_n-points on sheets 1 and 2. So p_3 acts on sheets 1 and 2 by one permutation of X_n, supported on 𝒪_{ρ_n}(w′) with w′ = (a_n g_1 a_n)⋯(a_n g_{ℓ−1} a_n)(a_n g_ℓ), a word of length ≤ 3ℓ ≤ r_n, as in S–S `lem:count-p3`.
  - By (SS2): ≤ (C(3ℓ)^α)!·exp(C(3ℓ)^α).
- **|P_4(ℓ)| ≤ exp(C_4ℓ^α log ℓ).**
  - Types 1 and 4 generate (∏_x A_x) ⋊ 𝒢_n, with A_x ≅ (Z/3)^{|A|} × Z supported on V×F_x; conjugates at the same point agree by §5.
  - (a_i^{(4)})^{g_i⋯g_ℓ} ∈ A_x for x = ρ_n g_i⋯g_ℓ ∈ 𝒪_{ρ_n}(g_1⋯g_ℓ).
  - p_4 is a choice of z_x ∈ A_x per point of an inverted orbit, with the Z-coordinate in [−ℓ,ℓ].
  - By (SS2): ≤ (3^{|A|}(2ℓ+1))^{Cℓ^α}·exp(Cℓ^α).

**Theorem 6.1.** There are C > 0 and β ∈ (0,1), depending only on |A|, such that for all large n and all ℓ ≤ r_n/3,
  γ^{T_n}_{[[T]]′}(ℓ) ≤ exp(Cℓ^β).
*Proof.* By Lemma 5.2 the ℓ-ball lies in P_1(ℓ)P_2(ℓ)P_3(ℓ)P_4(ℓ). Choose β ∈ (max{α,γ},1). ∎

## 7. Conclusion
- **ω([[T]]′) = 1.** W_n = [[T]]′ (part 1 §4), so ω([[T]]′) ≤ ω([[T]]′,T_n) ≤ γ(⌊r_n/3⌋)^{1/⌊r_n/3⌋} ≤ exp(C⌊r_n/3⌋^{β−1}) → 1.
- **Exponential growth** holds by (M3). **So Theorem Q holds.** ∎
- **Corollary Q1.** Thue–Morse and period doubling are primitive substitutions of constant length 2 with non-periodic fixed points. Their derived full groups are infinite, finitely generated and simple (Matui), amenable (Juschenko–Monod), and of non-uniform exponential growth.

**Scope and extensions (not claimed as nodes).**
- The proof uses (i) towers of height 2^m over clopen V_m with T^{2^m}V_m = V_m, and (ii) (V_m, T^{2^m}) a subshift whose letter partition has bounded size. The count is 3^{|A_m|}.
  - Constant length 2^k works by using m ≡ 0 mod k.
  - Constant length q ≠ 2^k needs a non-dyadic replacement for the Grigorchuk levels, and is not claimed.
- **Sturmian subshifts** have no constant towers. Cornulier's question stays open for them, and in general.
- **Cornulier's other clauses** ("diamètre semi-libre/sans torsion uniforme"): not addressed.

## 8. Credit, novelty, checks
- **Credit.** The method is Sauer–Schesler's (arXiv:2605.30163 §§3–5). The Grigorchuk inputs are Grigorchuk and Bartholdi–Erschler, as imported there. The full-group inputs are Matui, Juschenko–Monod and Cornulier's Lemme `eng_cb`. The tower partition is Mossé (via `constant-length-substitution-tower-partition`).
- **Novelty, bounded.**
  - Three web searches ("topological full group minimal subshift uniform exponential growth"; "simple amenable group non-uniform exponential growth"; "\"topological full group\" \"non-uniform exponential growth\"") found no result on growth rates of [[φ]]′.
  - The introduction of arXiv:2605.30163 names V as the simple example and does not mention full groups.
  - Main grep: only the open node `topological-full-group-derived-uniform-exponential-growth` and sk-free-8's matrix transfer.
- **Where sk-free-8's attempted transfer died, and the fix.** Its Attempt noted that level permutations plus T_{V_n} generate only "uniform" elements, and that fibre-dependent generators need a finite or abelian per-point group.
  - Here the fibre-dependent generators are the ζ_a: partial 3-cycles over the disjoint letter cylinders, so they commute.
  - σ_n is the only infinite-order local generator, on disjoint sheets.
  - Their non-commutative interplay only arises through conjugation by long words, via Step 2 of part 1.
- **Checked at source.** Cornulier bou1064.tex l.216 (question 7), l.564–586 (Théorème `fg`, Définition `d_bon`, Lemme `eng_cb`), l.166/780 (Matui's exponential growth); Sauer–Schesler 2605.30163 l.713–1420 (generators, `lem:commuting-conjugates`, `lem:normal-form`, `lem:count-p1..p4`, main proof).
- **Not re-read at source.** Matui 2006 Lemma 5.1 (used inside `eng_cb`), Matui's lamplighter paper [Ma2], Mossé 1996, Bartholdi–Erschler.
- **Model tests.**
  - For the odometer (constant towers but not a subshift), finitely generated subgroups have polynomial growth (Cornulier l.798). The proof does not apply, since the clopen algebra of V_m is not finitely generated under S_m, so |A_m| is unbounded. This is consistent.
  - For N < 5 (tiny n) the parity and 3-transitivity arguments fail, so large n is required. This is consistent.
