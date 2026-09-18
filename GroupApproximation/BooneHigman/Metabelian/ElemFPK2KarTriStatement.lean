import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarTriStep
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarIndStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# `R1` for three relative conjugates, and the rank-one reduction

Lane `bh-met-93k`, statement module.  `P = k2DilateSt_pullback s`; `A` is a domain, `s ≠ 0`, so
`P` has no zero divisors (`k2KarInd_mul_eq_zero`).

* `k2KarTri_RankOneAt s m`: every product `y` of at most `m` relative conjugates whose matrix is
  `1 + V Wᵀ` with `W ⬝ᵥ V = 0` carries a rank-one datum
  `stab y = ⁅padCol V', padRow W'⁆`, `padMat y = 1 + V' W'ᵀ`.
* **`k2KarTri_boundedAt_succ_of_rankOne`**: `RankOneAt s m → k2KarRel_BoundedAt s (m + 1)`.
  Rotate `z · rest` to `rest · z`; then `padMat rest = 1 + V Wᵀ` with `W ⬝ᵥ V = 0`
  (`k2KarTri_padMat_left`) and `k2KarTri_stab_rankOne_mul_conj` kills `stab (rest · z)`.
* **`k2KarTri_rankOneAt_two`**: `RankOneAt s 2` is **proved** (`k2KarTri_rankOne_rootMul`).
* **`k2KarTri_boundedAt_three`**: `k2KarRel_BoundedAt s 3` is **proved**, for every domain `A`
  and `s ≠ 0`; **`k2KarTri_posBounded_three : k2KarRel_PosBoundedStatement 3`**.
* `k2KarTri_QuadStatement := k2KarRel_PosBoundedStatement 4`, with
  `k2KarTri_quad_of_pos : k2Karoubi_PosStatement → k2KarTri_QuadStatement` and
  `k2KarTri_quad_of_rankOne : (Pos-version of RankOneAt 3) → k2KarTri_QuadStatement`.

## LOUD: status

* **Truth check.**  `BoundedAt s 3` is TRUE and PROVED here.  Neither relativity (`fst b = 0`)
  nor `1 ≠ 0` is used: over a ring with no zero divisors, three root conjugates whose product has
  trivial matrix die after ONE stabilization.
* **The m-reduction is NOT a weakening of `R1`.**  `RankOneAt s m` implies `BoundedAt s m` (take
  `V = W = 0`) and `BoundedAt s (m + 1)`, and in fact demands death after one stabilization.
  So the family `∀ m, RankOneAt s m` IMPLIES `R1` and is plausibly STRONGER than `R1`.  The
  converse is NOT proved.  The truth of `RankOneAt s m` for `m ≥ 3` is OPEN here; it is not
  claimed false.
* **Residual.**  `k2KarTri_QuadStatement` (four relative conjugates) is implied by `R1`
  (`k2KarTri_quad_of_pos`), so it is weaker than or equal to `R1`.  Its STRICT weakness is NOT
  proved.  The family over all `m` of the bounded statements is EQUIVALENT to `R1`
  (`k2KarRel_pos_of_posBounded`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarTriStatementDef

/-- Products of at most `m` relative conjugates with rank-one matrix carry a rank-one datum. -/
def k2KarTri_RankOneAt {A : Type*} [CommRing A] (s : A) (m : ℕ) : Prop :=
  ∀ (M : ℕ) (l : List (SteinbergGroup (Fin M) (k2DilateSt_pullback s))), l.length ≤ m →
    (∀ z ∈ l, z ∈ k2KarRel_gens s M) → ∀ V W : Fin M → k2DilateSt_pullback s,
      padMat l.prod = 1 + Matrix.vecMulVec V W → W ⬝ᵥ V = 0 →
        ∃ V' W' : Fin M → k2DilateSt_pullback s,
          stab M (k2DilateSt_pullback s) l.prod = ⁅padCol V', padRow W'⁆ ∧
            padMat l.prod = 1 + Matrix.vecMulVec V' W'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_RankOneAt

end KarTriStatementDef

section KarTriStatement

variable {A : Type*} [CommRing A] [IsDomain A] {s : A}

/-- **The m-reduction**: `RankOneAt s m → BoundedAt s (m + 1)`. -/
theorem k2KarTri_boundedAt_succ_of_rankOne (hs : s ≠ 0) {m : ℕ} (h : k2KarTri_RankOneAt s m) :
    k2KarRel_BoundedAt s (m + 1) := by
  intro M l hlen hl hsnd
  rcases l with _ | ⟨z, l'⟩
  · exact k2KarRel_boundedAt_one s M [] (by simp) hl hsnd
  obtain ⟨g, k₀, l₀, hkl, c, _, rfl⟩ := hl z (by simp)
  have hl' : ∀ w ∈ l', w ∈ k2KarRel_gens s M := fun w hw ↦ hl w (List.mem_cons_of_mem _ hw)
  have hlen' : l'.length ≤ m := by
    rw [List.length_cons] at hlen
    omega
  rw [List.prod_cons] at hsnd ⊢
  have h1 := k2KarInd_padMat_eq_one hs hsnd
  have e : g * x k₀ l₀ hkl c * g⁻¹ * l'.prod =
      g * x k₀ l₀ hkl c * g⁻¹ * (l'.prod * (g * x k₀ l₀ hkl c * g⁻¹)) *
        (g * x k₀ l₀ hkl c * g⁻¹)⁻¹ := by group
  rw [e] at h1 ⊢
  have h2 := k2KarTri_padMat_conj_eq_one h1
  obtain ⟨V, W, hsV, hmV⟩ := h M l' hlen' hl' _ _ (k2KarTri_padMat_left h2)
    (k2KarTri_dot_eq_zero g hkl (-c))
  exact cubeDiagDilate_stDies_conj _ (k2KarInd_stDies_of_stab
    (k2KarTri_stab_rankOne_mul_conj (k2KarInd_mul_eq_zero hs) hsV hmV g k₀ l₀ hkl c h2))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_boundedAt_succ_of_rankOne

/-- **`RankOneAt s 2` holds** over a domain with `s ≠ 0`. -/
theorem k2KarTri_rankOneAt_two (hs : s ≠ 0) : k2KarTri_RankOneAt s 2 := by
  intro M l hlen hl V W hm _
  rcases l with _ | ⟨z, _ | ⟨w, _ | ⟨u, l⟩⟩⟩
  · refine ⟨0, 0, ?_, ?_⟩
    · rw [List.prod_nil, map_one, padCol_zero, commutatorElement_one_left]
    · rw [List.prod_nil, map_one, Matrix.vecMulVec_zero, add_zero]
  · obtain ⟨g, i, j, hij, b, _, rfl⟩ := hl z (by simp)
    rw [List.prod_cons, List.prod_nil, mul_one]
    exact ⟨_, _, k2KarInd_stab_conj_x g i j hij b, k2KarTri_padMat_conj g i j hij b⟩
  · obtain ⟨g, i, j, hij, b, _, rfl⟩ := hl z (by simp)
    obtain ⟨g₂, i₂, j₂, hij₂, c, _, rfl⟩ := hl w (by simp)
    rw [List.prod_cons, List.prod_cons, List.prod_nil, mul_one] at hm ⊢
    have e : g * x i j hij b * g⁻¹ * (g₂ * x i₂ j₂ hij₂ c * g₂⁻¹) =
        g * (x i j hij b * (g⁻¹ * g₂ * x i₂ j₂ hij₂ c * (g⁻¹ * g₂)⁻¹)) * g⁻¹ := by
      group
    rw [e] at hm ⊢
    obtain ⟨V₁, W₁, hs₁, hm₁⟩ := k2KarTri_rankOne_rootMul (k2KarInd_mul_eq_zero hs)
      (k2KarInd_stab_conj_x (g⁻¹ * g₂) i₂ j₂ hij₂ c) (k2KarTri_padMat_conj (g⁻¹ * g₂) i₂ j₂ hij₂ c)
      (k2KarTri_dot_eq_zero (g⁻¹ * g₂) hij₂ c) i j hij b (k2KarTri_padMat_of_conj hm)
    exact ⟨_, _, k2KarTri_rankOne_conj g hs₁ hm₁⟩
  · rw [List.length_cons, List.length_cons, List.length_cons] at hlen
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_rankOneAt_two

/-- **`R1` for products of three relative conjugates**, over any domain, `s ≠ 0`. -/
theorem k2KarTri_boundedAt_three (hs : s ≠ 0) : k2KarRel_BoundedAt s 3 :=
  k2KarTri_boundedAt_succ_of_rankOne hs (k2KarTri_rankOneAt_two hs)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_boundedAt_three

end KarTriStatement

section KarTriEndpoint

/-- **`k2KarRel_PosBoundedStatement 3` holds.** -/
theorem k2KarTri_posBounded_three : k2KarRel_PosBoundedStatement 3 :=
  fun _ hp _ _ _ h0 _ ↦ by
    haveI := Fact.mk hp
    exact k2KarTri_boundedAt_three (Polynomial.C_ne_zero.2 h0)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_posBounded_three

/-- `RankOneAt` over the rings of `k2Karoubi_PosStatement`. -/
def k2KarTri_PosRankOneStatement (m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → ∀ s₀ : MvPolynomial (Fin k) (ZMod p),
    s₀ ≠ 0 → ¬ IsUnit s₀ →
      k2KarTri_RankOneAt (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p))) m

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_PosRankOneStatement

/-- **Residual**: `R1` for products of four relative conjugates. -/
def k2KarTri_QuadStatement : Prop :=
  k2KarRel_PosBoundedStatement 4

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_QuadStatement

/-- `R1` implies the residual (LOUD: strict weakness is NOT proved). -/
theorem k2KarTri_quad_of_pos (h : k2Karoubi_PosStatement) : k2KarTri_QuadStatement :=
  k2KarRel_posBounded_of_pos h 4

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_quad_of_pos

/-- The rank-one statement at `m = 3` implies the residual. -/
theorem k2KarTri_quad_of_rankOne (h : k2KarTri_PosRankOneStatement 3) :
    k2KarTri_QuadStatement :=
  fun p hp k hk s₀ h0 hu ↦ by
    haveI := Fact.mk hp
    exact k2KarTri_boundedAt_succ_of_rankOne (Polynomial.C_ne_zero.2 h0) (h p hp k hk s₀ h0 hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_quad_of_rankOne

end KarTriEndpoint

end GroupApproximation.BooneHigman.Metabelian.ElemFP
