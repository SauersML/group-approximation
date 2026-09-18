import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarQuadStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Four relative conjugates: reduction to the generic (rank-two) case

Lane `bh-met-93q`, statement module.  `P = k2DilateSt_pullback s`, `A` a domain, `s ≠ 0`.

* `k2KarQuad_GenericAt s`: `R1` for products `z₁ z₂ z₃ z₄` of four relative conjugates such
  that NEITHER `padMat (z₁ z₂)` NOR `padMat (z₂ z₃)` is of rank-one form `1 + V Wᵀ`
  (`W ⬝ᵥ V = 0`).
* **`k2KarQuad_boundedAt_four_of_generic`**: `GenericAt s → k2KarRel_BoundedAt s 4`.  Lengths
  `≤ 3` are `k2KarTri_boundedAt_three`; the rank-one adjacent-pair cases are
  `k2KarQuad_stDies_of_pair12` and `k2KarQuad_stDies_of_pair23` (proved).
* `k2KarQuad_PosGenericStatement`, **`k2KarQuad_quad_of_generic`** (`→ k2KarTri_QuadStatement`)
  and `k2KarQuad_generic_of_pos` (`k2Karoubi_PosStatement →` it).

## Truth check (scripts in the scratchpad, `bh-met-93q/`)

* **LOUD: the `m ≤ 3` method cannot reach `m = 4`.**  Over `R = ℚ` (a domain), with
  `z₁ = x₁₂(1)`, `z₂ = x₂₁(16/5)`, `g = z₁ z₂ ~ diag(5, 1/5)` and `k ~ diag(2, 1/2)` in the
  centralizer torus of `g`, the four root conjugates `z₁, z₂, k z₂⁻¹ k⁻¹, k z₁⁻¹ k⁻¹` have
  trivial matrix product (`field_counterexample.py`), while their Steinberg product is
  `⁅g̃, k̃⁆`, whose class is `{5, 2}^{±2} ∈ K₂(ℚ)`; its tame symbol at `5` is `2^{∓2} = 4 ≠ 1`
  in `𝔽₅^×`, so it does NOT die after any padding.  Hence "four root conjugates over a domain
  with trivial matrix die" is FALSE: unlike `m ≤ 3`, any proof of `m = 4` must use relativity
  (`fst b = 0`) or the structure of `P`, and the residual below cannot be closed by the
  rank-one calculus of lanes `bh-met-93e`/`bh-met-93k` alone.
* The residual is non-vacuous with relativity (`residual_nonvacuous.py`: over `ℚ[X]`,
  `z₁ = x₁₂(X)`, `z₂ = x₂₁(X)`, `z₃ = g z₂⁻¹ g⁻¹`, `z₄ = g z₁⁻¹ g⁻¹`, both adjacent-pair matrices
  have `det (M - 1) ≠ 0`).  It contains all commutators `⁅z₁ z₂, k̃⁆` with `padMat k`
  commuting with `padMat (z₁ z₂)`, i.e. exactly the shape of the counterexample above.

## LOUD: status

* `k2KarQuad_GenericAt s` is a special case of `k2KarRel_BoundedAt s 4` (hence implied by
  `R1`); with the proved reduction it is **LOGICALLY EQUIVALENT** to `BoundedAt s 4`.  It is
  **strictly smaller in proof content only**: the rank-one adjacent-pair cases are proved.
  Its truth is **OPEN** here (true if `R1` is).  `k2KarTri_QuadStatement` is NOT closed, and
  neither is `R1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

section KarQuadStatementDef

/-- **The generic four-conjugate case**: both adjacent-pair matrices are not rank-one. -/
def k2KarQuad_GenericAt {A : Type*} [CommRing A] (s : A) : Prop :=
  ∀ (M : ℕ) (z₁ z₂ z₃ z₄ : SteinbergGroup (Fin M) (k2DilateSt_pullback s)),
    z₁ ∈ k2KarRel_gens s M → z₂ ∈ k2KarRel_gens s M → z₃ ∈ k2KarRel_gens s M →
      z₄ ∈ k2KarRel_gens s M → ringMap (k2PullRel_snd s) (z₁ * z₂ * z₃ * z₄) = 1 →
        ¬ k2KarQuad_PairRankOne (z₁ * z₂) → ¬ k2KarQuad_PairRankOne (z₂ * z₃) →
          cubeDiagDilate_StDies (z₁ * z₂ * z₃ * z₄)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuad_GenericAt

/-- `BoundedAt s 4` gives the generic case (it is a special case). -/
theorem k2KarQuad_genericAt_of_boundedAt {A : Type*} [CommRing A] {s : A}
    (h : k2KarRel_BoundedAt s 4) : k2KarQuad_GenericAt s := by
  intro M z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hsnd _ _
  have e : [z₁, z₂, z₃, z₄].prod = z₁ * z₂ * z₃ * z₄ := by
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [← e] at hsnd ⊢
  refine h M _ (by simp) (fun z hz ↦ ?_) hsnd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuad_genericAt_of_boundedAt

end KarQuadStatementDef

section KarQuadStatement

variable {A : Type*} [CommRing A] [IsDomain A] {s : A}

/-- **The reduction**: the generic case gives `R1` for four relative conjugates. -/
theorem k2KarQuad_boundedAt_four_of_generic (hs : s ≠ 0) (h : k2KarQuad_GenericAt s) :
    k2KarRel_BoundedAt s 4 := by
  intro M l hlen hl hsnd
  rcases l with _ | ⟨z₁, _ | ⟨z₂, _ | ⟨z₃, _ | ⟨z₄, _ | ⟨z₅, l⟩⟩⟩⟩⟩
  · exact k2KarTri_boundedAt_three hs M [] (by simp) hl hsnd
  · exact k2KarTri_boundedAt_three hs M [z₁] (by simp) hl hsnd
  · exact k2KarTri_boundedAt_three hs M [z₁, z₂] (by simp) hl hsnd
  · exact k2KarTri_boundedAt_three hs M [z₁, z₂, z₃] (by simp) hl hsnd
  · have e : [z₁, z₂, z₃, z₄].prod = z₁ * z₂ * z₃ * z₄ := by
      simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    rw [e] at hsnd ⊢
    have h₁ := hl z₁ (by simp)
    have h₂ := hl z₂ (by simp)
    have h₃ := hl z₃ (by simp)
    have h₄ := hl z₄ (by simp)
    have hm := k2KarInd_padMat_eq_one hs hsnd
    by_cases hp : k2KarQuad_PairRankOne (z₁ * z₂)
    · exact k2KarQuad_stDies_of_pair12 hs h₁ h₂ h₃ h₄ hm hp
    by_cases hq : k2KarQuad_PairRankOne (z₂ * z₃)
    · exact k2KarQuad_stDies_of_pair23 hs h₁ h₂ h₃ h₄ hm hq
    exact h M z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hsnd hp hq
  · rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons,
      List.length_cons] at hlen
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuad_boundedAt_four_of_generic

end KarQuadStatement

section KarQuadEndpoint

/-- **The isolated residual (LOUD)**: the generic four-conjugate case over the rings of
`k2Karoubi_PosStatement`.  Equivalent to `k2KarTri_QuadStatement` given the proved reduction;
strictly smaller in proof content only (the rank-one adjacent-pair cases are proved).  Truth
OPEN here; a proof must use relativity (see the module docstring). -/
def k2KarQuad_PosGenericStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → ∀ s₀ : MvPolynomial (Fin k) (ZMod p),
    s₀ ≠ 0 → ¬ IsUnit s₀ →
      k2KarQuad_GenericAt (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuad_PosGenericStatement

/-- **Reduction**: the generic residual gives `k2KarTri_QuadStatement`. -/
theorem k2KarQuad_quad_of_generic (h : k2KarQuad_PosGenericStatement) :
    k2KarTri_QuadStatement :=
  fun p hp k hk s₀ h0 hu ↦ by
    haveI := Fact.mk hp
    exact k2KarQuad_boundedAt_four_of_generic (Polynomial.C_ne_zero.2 h0) (h p hp k hk s₀ h0 hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuad_quad_of_generic

/-- The residual is a special case of `k2KarTri_QuadStatement`. -/
theorem k2KarQuad_generic_of_quad (h : k2KarTri_QuadStatement) :
    k2KarQuad_PosGenericStatement :=
  fun p hp k hk s₀ h0 hu ↦ k2KarQuad_genericAt_of_boundedAt (h p hp k hk s₀ h0 hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuad_generic_of_quad

/-- `R1` implies the residual. -/
theorem k2KarQuad_generic_of_pos (h : k2Karoubi_PosStatement) :
    k2KarQuad_PosGenericStatement :=
  k2KarQuad_generic_of_quad (k2KarTri_quad_of_pos h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuad_generic_of_pos

end KarQuadEndpoint

end GroupApproximation.BooneHigman.Metabelian.ElemFP
