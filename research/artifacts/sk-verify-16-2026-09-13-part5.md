# sk-verify-16 part 5: wave-11 queue lines 74–75, sk-cstar-idempotent (2026-09-14)

Lane sk-verify-16. I independently reviewed `research/artifacts/sk-cstar-idempotent-2026-09-13-part1.md` and its claim and route nodes on main at tip b55f73c7a6.

**Source.** The MSI master was down, so the TeX lines l.419–694 could not be opened. I read the same content in the arXiv PDF of A. Le Boudec, N. Matte Bon, *A commutator lemma for confined subgroups and applications to groups acting on rooted trees*, arXiv:2006.08677v4 (5 Jul 2023), pp. 10–16, §3.1–3.5 in full.

## 0. Verdicts
| line | claim | verdict |
|---|---|---|
| 74 | `unit-group-confined-subgroups-idempotent-commutator-lemma` | **PASS-WITH-FIXES** (locators and one wording clause; the mathematics is correct) |
| 75 | `idempotent-displacement-fails-for-polynomially-small-units` | **PASS** (one optional wording clause) |

No FAIL, no GAP.

## 1. The source, v4 numbering
- **Def 3.1:** confined pair.
- **Def 3.7:** (C1) equal or disjoint; (C2) σ(Ω_σ) is disjoint from ⋃_α Ω_α.
- **Def 3.8:** M_σ = {ρ : σ(Ω_ρ) disjoint from ⋃Ω_α} and F_σ = {ρ : σ fixes Ω_ρ pointwise}. "Clearly M_σ and F_σ are disjoint, and σ ∈ M_σ thanks to condition (C2)."
- **Def 3.9:** p_ρ and π_σ are restriction maps.
- **Lemma 3.10:** (i) A_{σ,k} is supported in ⋃_{ρ∈P∖F_σ} Ω_ρ ∪ σ⁻¹(Ω_ρ); (ii) it preserves Ω_ρ for ρ ∈ M_σ, and π_σ(A_{σ,k}) = π_σ(D_{σ,k}).
- **Lemma 3.11:** Neumann covering.
- **Def 3.14 (displacement configuration):** (C1); (C3) σ fixes Ω_ρ pointwise or σ(Ω_ρ) is disjoint from ⋃Ω_α; (C4) σ(Ω_σ) is disjoint from ⋃Ω_α and from ⋃σ⁻¹(Ω_α).
- **Remark 3.15:** (C4) implies (C2); (C3) is equivalent to P = M_σ ∪ F_σ; for ρ ∈ M_σ, σ⁻¹(Ω_ρ) is disjoint from ⋃Ω_α.
- **Lemma 3.16:** B_λ = λσλ⁻¹A λσ⁻¹λ⁻¹ is supported in ⋃_{M_σ}Ω_ρ ∪ σ(Ω_ρ), and π_σ(B_λ) ≤ π_σ(R).
- **Def 3.17:** A^ρ_{σ,k}.
- **Lemma 3.18:** (R_G(Ω_ρ) : p_ρ(A^ρ)) ≤ (R : D).
- **Theorem 3.19:** n-tuples, FC_{≤nr} = 1.
- **Proposition 3.20:** with its Claim.
- **Theorem 3.21:** the case n = 1.

The lane's statement is Theorem 3.19 with n = 1, so r = |P|. Its "Theorem 3.17" is the numbering used by the authors' restatement in arXiv:2012.03997.

## 2. Line 74: Theorem A, re-derived in the ring
**Basic facts (M a unital ring, L = M^×).**
- For g ∈ Stab(E), EghE = (EgE)(EhE), since hE = EhE. So p_E is a homomorphism into (EME)^×.
- g − 1 ∈ EME gives gE = Eg and g = 1 − E + p_E(g). g⁻¹ is also supported in E: g⁻¹ commutes with E and (1−E)g⁻¹(1−E) = 1−E.
- For a pairwise orthogonal family 𝔉, the elements 1 + Σ_{E∈𝔉} x_E (x_E ∈ EME, invertible within the corner) form a subgroup, and each p_E is multiplicative on it, because x_Ey_{E′} = 0 for E ≠ E′.
- With R_σ = R_ρ whenever E_σ = E_ρ, the R_E for distinct E commute and meet trivially, so R = ∏_E R_E and every γ ∈ R is block diagonal over {E_α}.

**Support families; every pair is equal or orthogonal.**
1. **{E_α}:** (C1).
2. **σ⁻¹E_ρσ versus E_α, for ρ ∈ M_σ.**
   - If α ∈ M_σ: σ⁻¹E_ρσE_α = σ⁻¹(E_ρ·σE_ασ⁻¹)σ = 0, and E_ασ⁻¹E_ρσ = σ⁻¹(σE_ασ⁻¹·E_ρ)σ = 0.
   - If α ∈ F_σ: σE_α = E_α = E_ασ, so σ⁻¹E_ρσE_α = σ⁻¹E_ρE_α and E_ασ⁻¹E_ρσ = E_αE_ρσ.
   - If E_ρ = E_α, then E_ρ = σE_ρσ⁻¹ ⊥ E_ρ, so E_ρ = 0, which is excluded. So E_ρ ⊥ E_α by (C1), and both products vanish.
   - This is the ring form of Remark 3.15 and of F_σ ∩ M_σ = ∅.
3. **σE_ρσ⁻¹ versus E_α, for ρ ∈ M_σ:** the definition of M_σ.
4. **Translates of one list:** conjugates of (C1).
5. **σE_σσ⁻¹ versus E_α and versus σ⁻¹E_ασ:** (C4). σ ∈ M_σ by the first half of (C4).

**Lemma 3.10.**
- For γ, δ ∈ R, c = σ⁻¹δ⁻¹γσ is block diagonal over the conjugated family σ⁻¹{E}σ.
- That family is {E_α : α ∈ F_σ} ∪ {σ⁻¹E_ρσ : ρ ∈ M_σ}, well defined by pair 2.
- So γ, δ and c, hence a_{δ,γ} = δcγ⁻¹, are all block diagonal over the orthogonal family 𝔉_σ = {E_α} ∪ {σ⁻¹E_ρσ}_{ρ∈M_σ}.
- On E_α with α ∈ F_σ, E_αcE_α = E_αδ⁻¹γE_α, so p_{E_α}(a) = E_α: (i).
- c is trivial on E_ρ for ρ ∈ M_σ (pair 2), so p_{E_ρ}(a) = p_{E_ρ}(δγ⁻¹): (ii).

**Lemma 3.11:** the same formal group theory.

**Lemma 3.16.**
- λ ∈ R is trivial on σ^{±1}E_ρσ^{∓1} (pairs 2, 3) and commutes with E_ρ. So u = λσλ⁻¹ maps σ⁻¹E_ρσ ↦ E_ρ and E_ρ ↦ σE_ρσ⁻¹, and B_λ is block diagonal over {E_ρ, σE_ρσ⁻¹}_{ρ∈M_σ}.
- In λσλ⁻¹aλσ⁻¹λ⁻¹ = λ(σλ⁻¹δσ⁻¹)(δ⁻¹γ)(σγ⁻¹λσ⁻¹)λ⁻¹, the middle factors are supported in σFσ⁻¹.
- σFσ⁻¹ = Σ_{F_σ}E_α + Σ_{M_σ}σE_ασ⁻¹ ⊥ E_ρ for ρ ∈ M_σ (pairs 1 and 3). So π_σ(B_λ) ≤ π_σ(R).

**Lemma 3.18.**
- For d ∈ D ∩ R_ρ, Lemma 3.10(ii) gives a ∈ A with π_σ(a) = π_σ(d).
- Then a is trivial on E_α for α ∈ M_σ with E_α ≠ E_ρ, and block diagonal, so a ∈ A^ρ.
- So p_ρ(A^ρ) ⊇ p_ρ(D ∩ R_ρ), and the index bound follows (R_ρ identified with p_ρ(R_ρ)).

**Claim of Prop 3.20.**
- f ∈ A^σ with p_σ(f) ≠ 1 exists by the index count.
- If f is trivial on every σ⁻¹E_ρσ, then f is supported in E_σ and p_σ(f) ∈ p_σ(R_σ), so f ∈ R_σ ∩ H by injectivity.
- Otherwise h = ufu⁻¹ satisfies E_ρhE_ρ = u(σ⁻¹E_ρσ·f·σ⁻¹E_ρσ)u⁻¹ ≠ E_ρ, with p_ρ(h) ∈ p_ρ(R_ρ).
- a ∈ A^ρ is nontrivial only on the blocks E_ρ and σ⁻¹E_ασ (α ∈ M_σ). h is nontrivial only on the blocks E_α (α ∈ M_σ) and σE_σσ⁻¹.
- The union 𝔊 = {E_ρ} ∪ {σ⁻¹E_ασ}_{M_σ} ∪ {E_α}_{M_σ, ≠ρ} ∪ {σE_σσ⁻¹} is pairwise orthogonal by pairs 1, 2, 4, 5. The only mixed pair beyond Lemma 3.10 is σE_σσ⁻¹ ⊥ σ⁻¹E_ασ, the second half of (C4).
- So [a,h] = 1 − E_ρ + [p_ρ(a), p_ρ(h)], with p_ρ(a) ∈ p_ρ(D) ⊆ p_ρ(R_ρ) by Lemma 3.10(ii), and p_ρ(h) ∈ p_ρ(R_ρ) by Lemma 3.16. So [a,h] ∈ H ∩ R_ρ.
- Nontriviality: p_ρ(A^ρ) has index ≤ r, and the centralizer of p_ρ(h) has index > r, since FC_{≤r}(R_ρ) = 1.

**Conclusion of Prop 3.20 and Theorem 3.19.**
- a h_0 a⁻¹ = 1 − E_ρ + p_ρ(a)p_ρ(h_0)p_ρ(a)⁻¹ ∈ R_ρ, since a preserves E_ρ.
- Conjugation of R_ρ by elements of A_S or of D depends only on p_ρ, and p_ρ(A_S) = p_ρ(D). So N = ⟨a h_0 a⁻¹⟩ ≤ H ∩ R_ρ is normalized by D.
- p_ρ: R → R_ρ is onto, so (R_ρ : p_ρ(D)) ≤ (R : D) ≤ r.

**Rigid groups.** Only "R_σ ≤ G is supported in E_σ" and R = ∏R_E are used, so chosen subgroups suffice, as the lane says.

**Fixes (verbatim).**
- **F1 (locators).** In the artifact §§0, 2, and in the route, cite "arXiv:2006.08677v4, Theorem 3.19 with n = 1 (Theorem 3.21); Def 3.7, 3.8, 3.14, Remark 3.15, Lemmas 3.10, 3.11, 3.16, 3.18, and the Claim in the proof of Proposition 3.20". Also note: "Theorem 3.17 in the version restated in arXiv:2012.03997". The "Remark after Def. 3.12" is the sentence "Clearly M_σ and F_σ are disjoint" in Def 3.8.
- **F2 (wording, Corollary A′).** Replace "Infinite simple groups have trivial FC-center, since the FC-center is normal" with: "An infinite simple group has trivial FC-center: the FC-center is normal, and if it were the whole group, the normal closure of an element g ≠ 1 would be a finitely generated FC-group, hence virtually abelian, and equal to the group by simplicity, which is impossible for an infinite simple group."
- **W1 (optional).** In the Claim, attribute p_ρ(a) ∈ p_ρ(R_ρ) to the ring form of Lemma 3.10(ii), and p_ρ(h) ∈ p_ρ(R_ρ) to Lemma 3.16.

## 3. Line 75: Lemma B and instances
- **Lemma.** E = E·1·E = Σ_k c_kEσ^kE = 0 for central c_k.
- **Zeros.** E ⊥ σEσ⁻¹ ⟺ EσE = 0 = Eσ⁻¹E: right-multiply EσEσ⁻¹ = 0 by σ, left-multiply σEσ⁻¹E = 0 by σ⁻¹, and conversely.
- (C4) at α = σ for E = E_σ gives σEσ⁻²Eσ = 0 and σ⁻¹Eσ²Eσ⁻¹ = 0, so Eσ^{±2}E = 0.
- **Consequence.** 1 ∈ span_{F_2}{σ^{±1}, σ^{±2}} forces E_σ = 0, contradicting nonzero. The coefficients are 0/1 integers, so they are central in any unital ring. So no displacement configuration containing σ exists in any unital ring in which that relation holds. σ + σ⁻¹ = 1 blocks single displacement.
- **Involutions.** σ² = 1.
- **σ = I + N, N = E_12 + E_23 over F_2.** N² = E_13 and N³ = 0. σ⁻¹ = I + N + N² (the product is I + 2N + 2N²), σ² = I + N², and σ + σ⁻¹ + σ² = 3I + 2N + 2N² = I. σ has order 4.
- **Singer cycle, α³ = α + 1 in F_8.** α⁵ = α² + α + 1 = α⁻², α⁶ = α² + 1 = α⁻¹, so 1 = α⁻¹ + α². Singer cycles lie in GL_3(F_2) = SL_3(F_2) = E_3(F_2) ≤ G_X.
- **Order 3.** σ² + σ + 1 = 0 would make F_2³ a vector space over F_4, of even dimension. Correct.
- **W2 (optional wording).** In the claim node, "in any ring containing σ" → "in any unital ring containing σ, since the relation has integer coefficients".

## 4. Not checked
- The TeX l.419–694 (MSI down); v4 PDF pp. 10–16 read instead.
- The open steps (L3) and (L4) in artifact §3, which are not claims.
- Novelty beyond the lane's bound.
