# Review: genus-3 Birman sequence does not virtually split

Lane `birman-genus3-review` (adversarial), 2026-09-12.

**Under review:**
- `birman-sequence-genus-three-does-not-virtually-split`, route `birman-genus-three-no-virtual-splitting-proof`;
- corollary `genus-three-mcg-has-no-covering-lift-to-marked-covers`;
- commit 53f80e1e6, artifact `research/artifacts/bh-birman-genus3-section-2026-09-12.md`.

**Sources, read here:**
- Chen–Salter, arXiv:1804.11235v1, all 787 extracted lines (MSI `/scratch.global/sauer354/bh-outfn-mcg/1804.11235v1.txt`).
- Luo–Watanabe, arXiv:2502.14343v2: abstract, §1, acknowledgement.

## Verdict: PASS

I found no error and no gap in the genus-3 argument. I checked every Lemma A–D step against the source and tested each H₁ and rank claim. Remarks below; none changes the claim or the graph.

## 1. Where Chen–Salter need g ≥ 4

The artifact's list G1–G5 is complete for the steps the genus-3 proof replaces. Verbatim anchors:
- **G1.** Lemma 2.9 preamble "When g > 3, we have that 2g − 3 > 3", and Claim 2.11 "since g ≥ 4 and hence 2g − 3 > 3".
- **G2.** "as long as both components of Σg \{c} have genus two or greater".
- **G3.** Lemma 2.15 "since p ≥ 2 and q ≥ 2 by assumption", and Lemma 2.16's hypothesis "each component … has genus at least 2".
- **G4.** §3 "By the hypothesis that g ≥ 4 … p, q ≥ 2 … Without loss of generality, we assume that the marked point ∗ ∈ Σp,1".
- **G5.** Lemma 3.6 "Since p ≥ 2", and §3.4 χ(Σp) ≠ 0.

Two further mentions, neither needing new work:
- **(G6)** Lemma 3.2's proof again takes c with p, q ≥ 2 so that σ(T_c^k) is a single twist. That is the same c as G4, supplied in genus 3 by Lemmas C–D.
- **(G7)** Claim 2.12 (Step 3) uses a separating curve s ⊂ C and asserts CRS(σ(T_s^m)) is one or two lifts of s. That is the separating-twist case, which needs both sides of s to have genus ≥ 2. The genus-3 Step 3 does not use this: it uses (F) plus McCarthy instead (§2 below).

**Minor imprecision in the artifact's G3 remark.** For q = 1 the disk-pushing kernel of Σ_{1,1} is not π1(UT Σ_1) ≅ Z³: point pushing on the torus degenerates, and Mod(Σ_{1,1}) ≅ B₃ with Torelli ⟨T_∂⟩. So Lemma 2.15 is inapplicable for q = 1, rather than failing by the 7-versus-6 Betti count. This does not matter: Lemma C uses only the genus-2 side.

## 2. The genus-3 repairs, line by line

**(R), the rank bound.**
- Pants decompositions of Σ₃ have 3g − 3 = 6 curves, both through a bounding pair (2 + 2 + 2) and through a torus-bounding separating curve (1 + 4 + 1). Twist powers in L give Z⁶, and σ is injective, so σ(Z⁶) ≅ Z⁶.
- **Centralizer bound, Lemma A Step 2.** The element is pA on C ≅ Σ_{2,2} and the pants P has trivial pure MCG. After passing to finite index, the centralizer is a central extension, by twists about M̃, of a subgroup of a virtually cyclic group. Hence it is virtually abelian of rank ≤ |M̃| + 1 ≤ 3 < 6. Correct.

**Lemma A.**
- **Step 1.** Case 1 is Prop 2.3 plus Prop 2.5 for x^k, unchanged. Case 2 uses a crossing δ ⊂ S_i, so T_δ commutes with x; valid.
- **Step 2.** Empty CRS gives pA with virtually cyclic centralizer containing Z⁶. With CRS ⊆ lifts of b, the pA-on-C case contradicts (R); the identity-on-C case would give x^{kN} = T_b^j. Valid.
- **Step 3.** ψ, φ commute in Mod(C̃^), with φ pA. McCarthy gives ψ^j = φ^i. Under forget_∗ via (F): φ ↦ ρ_S(x^k) = 1, a boundary multitwist collapsed to punctures, and ψ ↦ T_δ^r, of infinite order in Mod(Σ_{1,2}^). So T_δ^{rj} = 1, a contradiction.
  - This also holds when i = 0.
  - This step is more robust than Chen–Salter's Claim 2.12, which leans on the separating-twist case (G7).
- **Exponents.** p fixes the exponents, which gives the stated form. The formula holds after enlarging k. Roots are unique in π1(Σ₂), so s(α^k) is determined for every k with α^k ∈ H̄.

**Lemma B.** Every essential separating curve of Σ₃ bounds a one-holed torus. Steps 1–3 transfer, since T = Σ_{1,1} and R = Σ_{2,1} both contain nonperipheral δ, and the pants P admits no pA. Valid.

**Lemma C.**
- **The subgroup.** h ∈ D'' ≤ π1(UT Σ₂) ∩ L commutes with T_c, so σ(h) preserves {c_T, c_R}. By (F), ρ_T̃(σ(h)) = ρ_T(h) = 1, and ρ_P = 1 (thrice-punctured sphere).
- **Cutting.** The cutting kernel is ⟨T_{c_T}, T_{c_R}⟩, and Mod(R̃) → Mod(R̃^) is surjective. So σ(h) ∈ Mod(R̃)·⟨T_{c_T}⟩.
- **Injectivity.** The product is Mod(R̃) × Z in Mod(Σ_{3,∗}):
  - supports are disjoint;
  - T_{c_T}^n is not supported on R̃ for n ≠ 0, since it moves arcs through P ∪ T̃ that cross c_T;
  - Mod(R̃) injects (FM Thm 3.18, since the complement T̃ ∪ P contains genus).

  So ν is a homomorphism with ν(T_c^{kN}) ≠ 0.
- **Contradiction.** D'' is a central extension of a closed surface group, with rational Euler class a nonzero multiple of e(UT Σ₂). By the five-term sequence, the center is 0 in H₁(D''; Q), so ν(center) = 0. Contradiction.
- **Sanity check.** H₁(π1(UT Σ₂); Z) ≅ Z⁴ ⊕ Z/2, and the fiber is the torsion Z/(χ) = Z/2. That matches b₁(D'') = b₁(quotient).
- **Correct.** It is a cleaner replacement for Lemmas 2.15–2.16.

**Lemma D.**
- Commuting lifts give disjoint c̃₁, c̃₂ (Props 2.4, 2.5).
- If c̃₂ ⊂ T̃₁ = Σ_{1,1}(,∗), then c̃₂ is either parallel to c̃₁ or bounds a genus-1 side with ∗ on the annulus side. Either way c₂ ≃ c₁ after forgetting ∗.
- Hence c̃₂ ⊂ R̃₁ and c̃₁ ⊂ R̃₂. T̃₁ is connected and disjoint from c̃₂, and c̃₁ ∉ T̃₂, so T̃₁ ⊂ R̃₂ and the two tori are disjoint.
- So ∗ lies in some R̃_i. Valid.

**Section 3 with p = 2.**
- **Support.** The support claim follows from (F), as the artifact says.
- **Lemmas 3.1, 3.2 and 3.7.** Lemma 3.1 needs only σ(T_c^k) = T_{c̃}^k (Lemma C). Lemma 3.2's (10)–(11) are unchanged for nonseparating α (a, b, c pants in R, with Lemma A). Lemma 3.7 needs no Torelli hypothesis: the forgetful diagram commutes for Mod.
- **Lemmas 3.3, 3.5, 3.6, 3.8 and §3.4.** They use only π1(Σ_p) with p ≥ 2:
  - roots are unique;
  - commuting elements are commensurable;
  - separating curves fill Σ₂;
  - Lemma 3.9.

**Remark: a written gap in Chen–Salter, patched here.**
- Lemma 3.2 derives s(α^k) = α^m only through bounding pairs, i.e. for nonseparating simple α. Its claimed "one-to-one correspondence" with all simple curves on Σ_p is inaccurate for separating α.
- But Lemma 3.3's hypothesis, and Corollary 3.4(B) as used in Lemma 3.6 (the γ_i conjugate to a separating d), need separating α.
- **In genus 3 the artifact supplies it.** For separating α ⊂ Σ₂, both α_L and α_R bound one-holed tori in Σ₃, so Lemma C gives single lifts and s(α^k) ∈ {1, α^{±k}}.
- **Lemma 3.3 extends to mixed pairs.** Take β nonseparating and α separating.
  - In Case (B), m(β, ℓ) = 0 forces m(α, k) = 0, because a separating α and a nonseparating β are never commensurable.
  - In Case (A), swapping the roles forces m(α, k) = k.
- **For g ≥ 4** the same one-sided argument patches separating α that bound a torus, since the other side then has genus ≥ 2.

## 3. Scope and credit

- **Scope.** The claim covers every finite-index L ≤ Mod(Σ₃) with p∘σ = id_L, which is Chen–Salter's definition of virtual splitting. The Torelli-level form is correctly not claimed.
- **Luo–Watanabe Theorem 1** (verbatim in the artifact) covers finite-index subgroups containing K₃, profinitely, and hence discretely. The genus-3 claim contains their discrete consequence. Their introduction (p. 2) and acknowledgement (pp. 3–4) state that the finite-index result is Chen–Salter's, for g ≥ 4, and that "Our results partially extend theirs in certain specific cases". So as of v2 (April 2025) the general genus-3 case was not known to them.
- **Novelty search** (bounded; arXiv full-text search from MSI, titles only):
  - queries: "Birman exact sequence", "virtually split", "universal curve" section genus, "no sections" universal curve;
  - hits: Chen–Salter; Luo–Watanabe; Chen 1710.00786 (full Torelli); Watanabe 1710.00485, 1410.3020, 1609.04124 and 2306.06278 (algebraic/profinite sections, hyperelliptic); Hain 1001.5008.
  - None states the discrete genus-3 statement for arbitrary finite-index subgroups. Journal literature after 2025 was not searched.

## 4. Not re-read (as in the artifact)

FM Prop 3.20 and Thm 3.18, McCarthy's centralizer theorem, Kra's theorem. The proof uses them only in their standard forms.

No graph change: the verdict is PASS, the claim and route stand, and nothing is invalidated.
