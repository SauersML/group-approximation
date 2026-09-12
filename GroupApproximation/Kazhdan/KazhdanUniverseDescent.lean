import GroupApproximation.Kazhdan.Kazhdan

/-!
# Universe descent for Kazhdan pairs

A Kazhdan pair quantifying over representation spaces in a large
universe restricts to any smaller universe: a representation on a small
Hilbert space lifts along `ULift` to the large universe, where the pair
produces an invariant vector, which descends back.

The definition `IsKazhdanPair.{u, v}` is deliberately
universe-relative; this module records the one direction that is free —
a pair at `max w v` yields a pair at `w` — so certificates proved once
at a large representation universe serve every smaller one.  The
converse direction (ascent) is a genuine theorem only under countability
hypotheses and is not attempted here.
-/

namespace GroupApproximation

open scoped RealInnerProductSpace

noncomputable section

universe u v w

section ULiftInner

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable instance : InnerProductSpace ℝ (ULift.{v} E) where
  __ := (inferInstance : NormedSpace ℝ (ULift.{v} E))
  inner x y := ⟪x.down, y.down⟫
  norm_sq_eq_re_inner x := by
    show ‖x.down‖ ^ 2 = _
    exact InnerProductSpace.norm_sq_eq_re_inner x.down
  conj_inner_symm x y := by
    show (starRingEnd ℝ) ⟪y.down, x.down⟫ = ⟪x.down, y.down⟫
    rw [starRingEnd_apply, star_trivial]
    exact real_inner_comm x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y r := by
    show ⟪r • x.down, y.down⟫ = (starRingEnd ℝ) r * ⟪x.down, y.down⟫
    rw [starRingEnd_apply, star_trivial]
    exact real_inner_smul_left x.down y.down r

end ULiftInner

section Descent

variable {G : Type u} [Group G]

/-- **Universe descent for Kazhdan pairs**: a pair at representation
universe `max w v` restricts to representation universe `w`. -/
theorem IsKazhdanPair.of_max {Q : Finset G} {ε : ℝ}
    (h : IsKazhdanPair.{u, max w v} G Q ε) :
    IsKazhdanPair.{u, w} G Q ε := by
  refine ⟨h.1, ?_⟩
  intro E _ _ _ ρ x hx hnear
  let e : ULift.{v} E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.ulift ℝ E
  let ρ' : G →* (ULift.{v} E ≃ₗᵢ[ℝ] ULift.{v} E) :=
    { toFun := fun g => (e.trans (ρ g)).trans e.symm
      map_one' := by
        apply LinearIsometryEquiv.ext
        intro z
        show e.symm (ρ 1 (e z)) = z
        rw [map_one]
        show e.symm (e z) = z
        exact e.symm_apply_apply z
      map_mul' := fun a b => by
        apply LinearIsometryEquiv.ext
        intro z
        show e.symm (ρ (a * b) (e z))
            = e.symm (ρ a (e (e.symm (ρ b (e z)))))
        rw [e.apply_symm_apply, map_mul]
        rfl }
  have hx' : ‖e.symm x‖ = 1 := by
    rw [e.symm.norm_map]
    exact hx
  have hnear' : ∀ q ∈ Q, ‖ρ' q (e.symm x) - e.symm x‖ < ε := by
    intro q hq
    have h1 : ρ' q (e.symm x) = e.symm (ρ q x) := by
      show e.symm (ρ q (e (e.symm x))) = e.symm (ρ q x)
      rw [e.apply_symm_apply]
    rw [h1, ← map_sub, e.symm.norm_map]
    exact hnear q hq
  obtain ⟨y, hy0, hyfix⟩ := h.2 (ULift.{v} E) ρ' (e.symm x) hx' hnear'
  refine ⟨e y, ?_, ?_⟩
  · intro h0
    apply hy0
    have := congrArg e.symm h0
    rw [e.symm_apply_apply, map_zero] at this
    exact this
  · intro g
    have h2 := hyfix g
    have h3 : e.symm (ρ g (e y)) = y := h2
    have := congrArg e h3
    rw [e.apply_symm_apply] at this
    exact this

/-- **Universe descent for property `(T)`.** -/
theorem HasKazhdanPropertyT.of_max
    (h : HasKazhdanPropertyT.{u, max w v} G) :
    HasKazhdanPropertyT.{u, w} G := by
  obtain ⟨Q, ε, hpair⟩ := h
  exact ⟨Q, ε, hpair.of_max⟩

end Descent

end

end GroupApproximation
