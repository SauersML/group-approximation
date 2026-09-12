import GroupApproximation.PropertyT.ThreeVertexClosure

/-!
# EJZ Proposition 3.2, in Hilbert-space form

Ershov--Jaikin-Zapirain (*Property (T) for noncommutative universal lattices*, Invent. Math. 179
(2010)), Proposition 3.2: if `G = ⟨H₁, H₂, H₃⟩`, `H₁, H₂` are `ε₃`-orthogonal, `H₁, H₃` are
`ε₂`-orthogonal and `H₂, H₃` are `ε₁`-orthogonal, then the vertex groups `⟨H₁, H₃⟩` and `⟨H₁, H₂⟩`
are `ε₀`-orthogonal with `ε₀ = √2 max{ε₁, ε₂} / √(1 - ε₃)`.

In a representation `V` put `V₁ = V^{⟨H₂,H₃⟩}`, `V₂ = V^{⟨H₁,H₃⟩}`, `V₃ = V^{⟨H₁,H₂⟩}`.  The group
hypotheses enter only through the projections to the three complements: `P_{V₃ᗮ} V₂` and
`P_{V₃ᗮ} V₁` consist of `H₁`- and `H₂`-fixed vectors moved by `⟨H₁, H₂⟩`, so they are
`ε₃`-orthogonal (`ProjectedAngle V₂ V₁ V₃ ε₃`), and likewise for the other two indices.  This file
proves the conclusion `V₃ ⊥_{ε₀} V₂` from those three projected angles and `V₂ ∩ V₃ = 0` alone.

EJZ run the argument inside `V₀ = V₁ + V₂ + V₃` and use `X + Y = U` where only density holds in
infinite dimensions; here `V₀` is the closure of the sum and every step that needs a sum to be the
whole space is proved as a density statement (`dense_three`, `dense_two`), with
`ThreeVertexDuality.abs_inner_le_of_mem_closure_sup` in place of EJZ Lemma 2.4.
-/

namespace GroupApproximation

universe v

namespace ThreeVertexProposition

open HilbertEpsilonOrthogonality ThreeVertexClosure

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The projections to `Cᗮ` of `A` and of `B` are `ε`-orthogonal. -/
def ProjectedAngle (A B C : Submodule ℝ E) [C.HasOrthogonalProjection] (epsilon : ℝ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B,
    |inner ℝ (Cᗮ.starProjection a) (Cᗮ.starProjection b)| ≤
      epsilon * ‖Cᗮ.starProjection a‖ * ‖Cᗮ.starProjection b‖

/-- A subspace with an orthogonal projection is closed. -/
theorem isClosed_of_hasOrthogonalProjection (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    IsClosed (K : Set E) := by
  rw [← K.orthogonal_orthogonal]
  exact Kᗮ.isClosed_orthogonal

/-- The projection to `Cᗮ` of `A ⊔ C` lies in the projection of `A`. -/
theorem map_sup_le_map (A C : Submodule ℝ E) [C.HasOrthogonalProjection] :
    (A ⊔ C).map (Cᗮ.starProjection : E →ₗ[ℝ] E) ≤ A.map (Cᗮ.starProjection : E →ₗ[ℝ] E) := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hz
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
  change Cᗮ.starProjection (a + c) ∈ _
  rw [map_add, Submodule.starProjection_orthogonal_apply_eq_zero hc, add_zero]
  exact Submodule.mem_map_of_mem ha

/-- Under a projected angle `ε < 1`, a vector orthogonal to `C` in the closures of both `A + C`
and `B + C` vanishes. -/
theorem eq_zero_of_projectedAngle (A B C : Submodule ℝ E) [C.HasOrthogonalProjection]
    {epsilon : ℝ} (heps1 : epsilon < 1) (hang : ProjectedAngle A B C epsilon) {w : E}
    (hwC : w ∈ Cᗮ) (hwA : w ∈ (A ⊔ C).topologicalClosure)
    (hwB : w ∈ (B ⊔ C).topologicalClosure) : w = 0 := by
  have hQw : Cᗮ.starProjection w = w := Submodule.starProjection_eq_self_iff.mpr hwC
  have hXY : EpsilonOrthogonal (A.map (Cᗮ.starProjection : E →ₗ[ℝ] E))
      (B.map (Cᗮ.starProjection : E →ₗ[ℝ] E)) epsilon := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
    exact hang a ha b hb
  have h1 := map_mem_topologicalClosure_map (Cᗮ.starProjection) hwA
  have h2 := map_mem_topologicalClosure_map (Cᗮ.starProjection) hwB
  rw [hQw] at h1 h2
  exact eq_zero_of_mem_topologicalClosure heps1 hXY
    (Submodule.topologicalClosure_mono (map_sup_le_map A C) h1)
    (Submodule.topologicalClosure_mono (map_sup_le_map B C) h2)

/-- **EJZ Proposition 3.2, Hilbert-space form.**  Three closed subspaces with `V₂ ∩ V₃ = 0` and
projected angles `ProjectedAngle V₂ V₁ V₃ e₃`, `ProjectedAngle V₃ V₁ V₂ e₂`,
`ProjectedAngle V₂ V₃ V₁ e₁`, all `eᵢ < 1`: then `V₃ ⊥_{ε₀} V₂` for every `ε₀ < 1` with
`2 max(e₁, e₂)² ≤ ε₀² (1 - e₃)`. -/
theorem epsilonOrthogonal_of_projectedAngles (V₁ V₂ V₃ : Submodule ℝ E)
    [V₁.HasOrthogonalProjection] [V₂.HasOrthogonalProjection] [V₃.HasOrthogonalProjection]
    {e₁ e₂ e₃ epsilon₀ : ℝ} (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (he₃ : 0 ≤ e₃)
    (he₁1 : e₁ < 1) (he₂1 : e₂ < 1) (he₃1 : e₃ < 1) (heps₀ : 0 ≤ epsilon₀)
    (heps₀1 : epsilon₀ < 1) (hconst : 2 * max e₁ e₂ ^ 2 ≤ epsilon₀ ^ 2 * (1 - e₃))
    (h₂₃ : V₂ ⊓ V₃ = ⊥)
    (hA₃ : ProjectedAngle V₂ V₁ V₃ e₃) (hA₂ : ProjectedAngle V₃ V₁ V₂ e₂)
    (hA₁ : ProjectedAngle V₂ V₃ V₁ e₁) :
    EpsilonOrthogonal V₃ V₂ epsilon₀ := by
  let V₀ : Submodule ℝ E := (V₁ ⊔ V₂ ⊔ V₃).topologicalClosure
  have hV₀cl : IsClosed (V₀ : Set E) := Submodule.isClosed_topologicalClosure _
  have hV₁₀ : V₁ ≤ V₀ :=
    (le_sup_left.trans le_sup_left).trans (Submodule.le_topologicalClosure _)
  have hV₂₀ : V₂ ≤ V₀ :=
    (le_sup_right.trans le_sup_left).trans (Submodule.le_topologicalClosure _)
  have hV₃₀ : V₃ ≤ V₀ := le_sup_right.trans (Submodule.le_topologicalClosure _)
  have hle₂₁₃ : V₁ ⊔ V₂ ⊔ V₃ ≤ V₂ ⊔ V₁ ⊔ V₃ :=
    sup_le (sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left)) le_sup_right
  have hle₃₁₂ : V₁ ⊔ V₂ ⊔ V₃ ≤ V₃ ⊔ V₁ ⊔ V₂ :=
    sup_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right) (le_sup_left.trans le_sup_left)
  have hle₂₃₁ : V₁ ⊔ V₂ ⊔ V₃ ≤ V₂ ⊔ V₃ ⊔ V₁ :=
    sup_le (sup_le le_sup_right (le_sup_left.trans le_sup_left)) (le_sup_right.trans le_sup_left)
  let X' : Submodule ℝ E := V₀ ⊓ V₂ᗮ ⊓ V₃ᗮ
  let Y' : Submodule ℝ E := V₀ ⊓ V₁ᗮ ⊓ V₃ᗮ
  let Z' : Submodule ℝ E := V₀ ⊓ V₁ᗮ ⊓ V₂ᗮ
  -- EJZ (3.3) and its two companions
  have hX'Y' : EpsilonOrthogonal X' Y' e₃ := by
    intro x hx y hy
    obtain ⟨⟨_, hx2⟩, hx3⟩ := hx
    obtain ⟨⟨hy0, hy1⟩, hy3⟩ := hy
    exact abs_inner_le_of_projected_angle V₂ V₁ V₃ he₃ he₃1 hA₃ hx2 hx3 hy1 hy3
      (Submodule.topologicalClosure_mono hle₂₁₃ hy0)
  have hX'Z' : EpsilonOrthogonal X' Z' e₂ := by
    intro x hx z hz
    obtain ⟨⟨_, hx2⟩, hx3⟩ := hx
    obtain ⟨⟨hz0, hz1⟩, hz2⟩ := hz
    exact abs_inner_le_of_projected_angle V₃ V₁ V₂ he₂ he₂1 hA₂ hx3 hx2 hz1 hz2
      (Submodule.topologicalClosure_mono hle₃₁₂ hz0)
  have hY'Z' : EpsilonOrthogonal Y' Z' e₁ := by
    intro y hy z hz
    obtain ⟨⟨hy0, hy1⟩, hy3⟩ := hy
    obtain ⟨⟨_, hz1⟩, hz2⟩ := hz
    have h := abs_inner_le_of_projected_angle V₂ V₃ V₁ he₁ he₁1 hA₁ hz2 hz1 hy3 hy1
      (Submodule.topologicalClosure_mono hle₂₃₁ hy0)
    rw [real_inner_comm] at h
    linarith [h, show e₁ * ‖z‖ * ‖y‖ = e₁ * ‖y‖ * ‖z‖ by ring]
  -- EJZ (3.4), extended to the closure
  have hsup : EpsilonOrthogonal (X' ⊔ Y') Z' epsilon₀ :=
    ThreeVertexDuality.epsilonOrthogonal_sup_of_pairwise he₁ he₃ heps₀ hconst hX'Y' hX'Z' hY'Z'
  have hsupcl : EpsilonOrthogonal (X' ⊔ Y').topologicalClosure Z' epsilon₀ :=
    HilbertEpsilonOrthogonality.mono (epsilonOrthogonal_topologicalClosure hsup) le_rfl
      (Submodule.le_topologicalClosure Z')
  -- density of `X' + Y'` in `V₀ ∩ V₃ᗮ`
  have dense_three : V₀ ⊓ V₃ᗮ ≤ (X' ⊔ Y').topologicalClosure := by
    intro u hu
    obtain ⟨hu0, hu3⟩ := hu
    let C : Submodule ℝ E := (X' ⊔ Y').topologicalClosure
    haveI : CompleteSpace C := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    have hCV₀ : C ≤ V₀ := Submodule.topologicalClosure_minimal _
      (sup_le (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_left)) hV₀cl
    have hCV₃ : C ≤ V₃ᗮ := Submodule.topologicalClosure_minimal _
      (sup_le inf_le_right inf_le_right) V₃.isClosed_orthogonal
    have hpC : C.starProjection u ∈ C := C.starProjection_apply_mem u
    have hwC : u - C.starProjection u ∈ Cᗮ := C.sub_starProjection_mem_orthogonal u
    have hw0 : u - C.starProjection u ∈ V₀ := V₀.sub_mem hu0 (hCV₀ hpC)
    have hw3 : u - C.starProjection u ∈ V₃ᗮ := V₃ᗮ.sub_mem hu3 (hCV₃ hpC)
    have hwX : ∀ r ∈ X', inner ℝ r (u - C.starProjection u) = 0 := fun r hr ↦
      Submodule.inner_right_of_mem_orthogonal
        (Submodule.le_topologicalClosure _ (Submodule.mem_sup_left hr)) hwC
    have hwY : ∀ r ∈ Y', inner ℝ r (u - C.starProjection u) = 0 := fun r hr ↦
      Submodule.inner_right_of_mem_orthogonal
        (Submodule.le_topologicalClosure _ (Submodule.mem_sup_right hr)) hwC
    have hw23 : u - C.starProjection u ∈ (V₂ ⊔ V₃).topologicalClosure :=
      mem_topologicalClosure_of_orthogonal_inf hV₀cl (sup_le hV₂₀ hV₃₀) hw0 fun r hr ↦ by
        obtain ⟨hr0, hr23⟩ := hr
        rw [← Submodule.inf_orthogonal] at hr23
        exact hwX r ⟨⟨hr0, hr23.1⟩, hr23.2⟩
    have hw13 : u - C.starProjection u ∈ (V₁ ⊔ V₃).topologicalClosure :=
      mem_topologicalClosure_of_orthogonal_inf hV₀cl (sup_le hV₁₀ hV₃₀) hw0 fun r hr ↦ by
        obtain ⟨hr0, hr13⟩ := hr
        rw [← Submodule.inf_orthogonal] at hr13
        exact hwY r ⟨⟨hr0, hr13.1⟩, hr13.2⟩
    have hzero : u - C.starProjection u = 0 :=
      eq_zero_of_projectedAngle V₂ V₁ V₃ he₃1 hA₃ hw3 hw23 hw13
    have hueq : u = C.starProjection u := sub_eq_zero.mp hzero
    show u ∈ C
    rw [hueq]
    exact hpC
  have hdiag : EpsilonOrthogonal (V₀ ⊓ V₃ᗮ) Z' epsilon₀ :=
    HilbertEpsilonOrthogonality.mono hsupcl dense_three le_rfl
  -- density of `(V₀ ∩ V₃ᗮ) + Z'` on `V₂`
  have dense_two : V₂ ≤ ((V₀ ⊓ V₃ᗮ) ⊔ Z').topologicalClosure := by
    intro v hv
    let C : Submodule ℝ E := ((V₀ ⊓ V₃ᗮ) ⊔ Z').topologicalClosure
    haveI : CompleteSpace C := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    have hCV₀ : C ≤ V₀ := Submodule.topologicalClosure_minimal _
      (sup_le inf_le_left (inf_le_left.trans inf_le_left)) hV₀cl
    have hpC : C.starProjection v ∈ C := C.starProjection_apply_mem v
    have hwC : v - C.starProjection v ∈ Cᗮ := C.sub_starProjection_mem_orthogonal v
    have hw0 : v - C.starProjection v ∈ V₀ := V₀.sub_mem (hV₂₀ hv) (hCV₀ hpC)
    have hw3 : v - C.starProjection v ∈ V₃ := by
      have hcl : v - C.starProjection v ∈ V₃.topologicalClosure :=
        mem_topologicalClosure_of_orthogonal_inf hV₀cl hV₃₀ hw0 fun r hr ↦
          Submodule.inner_right_of_mem_orthogonal
            (Submodule.le_topologicalClosure _ (Submodule.mem_sup_left hr)) hwC
      rwa [(isClosed_of_hasOrthogonalProjection V₃).submodule_topologicalClosure_eq] at hcl
    have hw12 : v - C.starProjection v ∈ (V₁ ⊔ V₂).topologicalClosure :=
      mem_topologicalClosure_of_orthogonal_inf hV₀cl (sup_le hV₁₀ hV₂₀) hw0 fun r hr ↦ by
        obtain ⟨hr0, hr12⟩ := hr
        rw [← Submodule.inf_orthogonal] at hr12
        exact Submodule.inner_right_of_mem_orthogonal
          (Submodule.le_topologicalClosure _ (Submodule.mem_sup_right ⟨⟨hr0, hr12.1⟩, hr12.2⟩))
          hwC
    let w : E := v - C.starProjection v
    have hq2 : V₂ᗮ.starProjection w ∈ V₂ᗮ := V₂ᗮ.starProjection_apply_mem w
    have hqeq : V₂ᗮ.starProjection w = w - V₂.starProjection w :=
      Submodule.starProjection_orthogonal_val w
    have hp2 : V₂.starProjection w ∈ V₂ := V₂.starProjection_apply_mem w
    have hq32 : V₂ᗮ.starProjection w ∈ (V₃ ⊔ V₂).topologicalClosure := by
      apply Submodule.le_topologicalClosure
      rw [hqeq]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hw3) (Submodule.mem_sup_right hp2)
    have hq12 : V₂ᗮ.starProjection w ∈ (V₁ ⊔ V₂).topologicalClosure := by
      rw [hqeq]
      exact Submodule.sub_mem _ hw12
        (Submodule.le_topologicalClosure _ (Submodule.mem_sup_right hp2))
    have hq0 : V₂ᗮ.starProjection w = 0 :=
      eq_zero_of_projectedAngle V₃ V₁ V₂ he₂1 hA₂ hq2 hq32 hq12
    have hw2 : w ∈ V₂ := by
      have h := Submodule.starProjection_apply_eq_zero_iff.mp hq0
      rwa [Submodule.orthogonal_orthogonal] at h
    have hwbot : w ∈ V₂ ⊓ V₃ := ⟨hw2, hw3⟩
    rw [h₂₃] at hwbot
    have hwz : w = 0 := by simpa using hwbot
    have hveq : v = C.starProjection v := sub_eq_zero.mp hwz
    show v ∈ C
    rw [hveq]
    exact hpC
  -- EJZ (3.5), density form
  intro v₃ hv₃ v₂ hv₂
  have hs : v₃ ∈ (V₀ ⊓ V₃ᗮ)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro r hr
    exact Submodule.inner_left_of_mem_orthogonal hv₃ hr.2
  have ht : v₂ ∈ Z'ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro r hr
    exact Submodule.inner_left_of_mem_orthogonal hv₂ hr.2
  exact ThreeVertexDuality.abs_inner_le_of_mem_closure_sup heps₀ heps₀1 hdiag hs ht
    (dense_two hv₂)

end ThreeVertexProposition
end GroupApproximation

#audit_axioms GroupApproximation.ThreeVertexProposition.isClosed_of_hasOrthogonalProjection
#audit_axioms GroupApproximation.ThreeVertexProposition.map_sup_le_map
#audit_axioms GroupApproximation.ThreeVertexProposition.eq_zero_of_projectedAngle
#audit_axioms GroupApproximation.ThreeVertexProposition.epsilonOrthogonal_of_projectedAngles
