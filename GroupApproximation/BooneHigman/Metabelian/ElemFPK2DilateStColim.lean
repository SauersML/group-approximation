import GroupApproximation.BooneHigman.Metabelian.ElemFPK2DilateStFamily
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg groups of the pullback: the dilation colimit

Lane `bh-met-90s`, colimit module.  Notation as in `ElemFPK2DilateStRing`.

`P = A ×_L L[X]` is the colimit of `A[X] → A[X] → ⋯` (dilations by `s`), and every Steinberg
relator involves at most two coefficients.  So the generators `x_{ij}(q)` of `St_I(P)` can be
sent to the sequences `(x_{ij}(F_r(q)))_r` in `∏_r St_I(A[X])`, modulo the normal subgroup of
eventually trivial sequences (`k2DilateSt_toQ`).  The relators hold for all large `r`,
because `F` is eventually additive and multiplicative (`k2DilateSt_family_add`,
`k2DilateSt_family_mul`).  On `St_I(A[X])`, through `ι_0`, this map is the diagonal of the
dilations `μ_{s^r}` (`k2DilateSt_family_base`).  The template is
`GroupApproximation.Full.LVCohnColimit` (finite witnesses in directed unions).

* `k2DilateSt_exists_scale_eq_one`: if `g ∈ St_I(A[X])` dies in `St_I(P)` under `ι_0`, then
  `μ_{s^r} g = 1` in `St_I(A[X])` for all large `r`.

No excision is used.  The element `g` need not lie in `K₂`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped commutatorElement

section DilateStEventually

variable (I : Type*) [Fintype I] [DecidableEq I] (A : Type*) [CommRing A]

/-- Sequences in `St_I(A[X])` that are eventually trivial. -/
def k2DilateSt_eventuallyOne : Subgroup (ℕ → SteinbergGroup I (Polynomial A)) where
  carrier := {F | ∃ m : ℕ, ∀ r : ℕ, m ≤ r → F r = 1}
  one_mem' := ⟨0, fun _ _ ↦ rfl⟩
  mul_mem' := by
    rintro F G ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, fun r hr ↦ ?_⟩
    change F r * G r = 1
    rw [hm r (by omega), hn r (by omega), mul_one]
  inv_mem' := by
    rintro F ⟨m, hm⟩
    refine ⟨m, fun r hr ↦ ?_⟩
    change (F r)⁻¹ = 1
    rw [hm r hr, inv_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_eventuallyOne

theorem k2DilateSt_mem_eventuallyOne (F : ℕ → SteinbergGroup I (Polynomial A)) :
    F ∈ k2DilateSt_eventuallyOne I A ↔ ∃ m : ℕ, ∀ r : ℕ, m ≤ r → F r = 1 :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_mem_eventuallyOne

instance k2DilateSt_eventuallyOne_normal : (k2DilateSt_eventuallyOne I A).Normal where
  conj_mem F hF G := by
    obtain ⟨m, hm⟩ := (k2DilateSt_mem_eventuallyOne I A F).mp hF
    refine (k2DilateSt_mem_eventuallyOne I A (G * F * G⁻¹)).mpr ⟨m, fun r hr ↦ ?_⟩
    change G r * F r * (G r)⁻¹ = 1
    rw [hm r hr, mul_one, mul_inv_eq_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_eventuallyOne_normal

end DilateStEventually

section DilateStColim

variable (I : Type*) [Fintype I] [DecidableEq I] {A : Type*} [CommRing A] (s : A)

/-- The sequence `(x_{ij}(F_r(q)))_r` attached to a generator `x_{ij}(q)` of `St_I(P)`. -/
noncomputable def k2DilateSt_genFamily (g : SteinbergGenerator I (k2DilateSt_pullback s)) :
    ℕ → SteinbergGroup I (Polynomial A) :=
  fun r ↦ SteinbergGroup.x g.row g.column g.row_ne_column (k2DilateSt_family s r g.coefficient)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_genFamily

/-- The sequences `k2DilateSt_genFamily` satisfy the Steinberg relations eventually. -/
theorem k2DilateSt_genFamily_relation
    (w : FreeGroup (SteinbergGenerator I (k2DilateSt_pullback s)))
    (hw : w ∈ SteinbergGroup.relations (I := I) (R := ↥(k2DilateSt_pullback s))) :
    FreeGroup.lift (k2DilateSt_genFamily I s) w ∈ k2DilateSt_eventuallyOne I A := by
  change SteinbergGroup.IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      obtain ⟨m, hm⟩ := k2DilateSt_family_add s a b
      refine (k2DilateSt_mem_eventuallyOne I A _).mpr ⟨m, fun r hr ↦ ?_⟩
      change SteinbergGroup.x i j hij (k2DilateSt_family s r a) *
        SteinbergGroup.x i j hij (k2DilateSt_family s r b) *
        (SteinbergGroup.x i j hij (k2DilateSt_family s r (a + b)))⁻¹ = 1
      rw [SteinbergGroup.x_mul, hm r hr]
      exact mul_inv_eq_one.mpr rfl
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      refine (k2DilateSt_mem_eventuallyOne I A _).mpr ⟨0, fun r _ ↦ ?_⟩
      change ⁅SteinbergGroup.x i j hij (k2DilateSt_family s r a),
        SteinbergGroup.x k l hkl (k2DilateSt_family s r b)⁆ = 1
      exact (SteinbergGroup.x_commute_of_ne i j k l hij hkl hjk hli _ _).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      obtain ⟨m, hm⟩ := k2DilateSt_family_mul s a b
      refine (k2DilateSt_mem_eventuallyOne I A _).mpr ⟨m, fun r hr ↦ ?_⟩
      change ⁅SteinbergGroup.x i j hij (k2DilateSt_family s r a),
          SteinbergGroup.x j k hjk (k2DilateSt_family s r b)⁆ *
        (SteinbergGroup.x i k hik (k2DilateSt_family s r (a * b)))⁻¹ = 1
      rw [SteinbergGroup.x_commutator i j k hij hjk hik, hm r hr]
      exact mul_inv_eq_one.mpr rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_genFamily_relation

/-- The relators die in the quotient by the eventually trivial sequences. -/
theorem k2DilateSt_genFamily_relation_quotient
    (w : FreeGroup (SteinbergGenerator I (k2DilateSt_pullback s)))
    (hw : w ∈ SteinbergGroup.relations (I := I) (R := ↥(k2DilateSt_pullback s))) :
    FreeGroup.lift (fun g ↦ QuotientGroup.mk' (k2DilateSt_eventuallyOne I A)
      (k2DilateSt_genFamily I s g)) w = 1 := by
  have hcomp : (QuotientGroup.mk' (k2DilateSt_eventuallyOne I A)).comp
      (FreeGroup.lift (k2DilateSt_genFamily I s)) =
      FreeGroup.lift (fun g ↦ QuotientGroup.mk' (k2DilateSt_eventuallyOne I A)
        (k2DilateSt_genFamily I s g)) :=
    FreeGroup.ext_hom _ _ fun g ↦ by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
  rw [← hcomp, MonoidHom.comp_apply]
  exact (QuotientGroup.eq_one_iff (N := k2DilateSt_eventuallyOne I A)
    (FreeGroup.lift (k2DilateSt_genFamily I s) w)).mpr (k2DilateSt_genFamily_relation I s w hw)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_genFamily_relation_quotient

/-- `St_I(P) → (∏_r St_I(A[X])) / (eventually trivial)`, `x_{ij}(q) ↦ [(x_{ij}(F_r(q)))_r]`. -/
noncomputable def k2DilateSt_toQ :
    SteinbergGroup I (k2DilateSt_pullback s) →*
      (ℕ → SteinbergGroup I (Polynomial A)) ⧸ k2DilateSt_eventuallyOne I A :=
  PresentedGroup.toGroup (f := fun g ↦ QuotientGroup.mk' (k2DilateSt_eventuallyOne I A)
    (k2DilateSt_genFamily I s g)) (k2DilateSt_genFamily_relation_quotient I s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_toQ

theorem k2DilateSt_toQ_x (i j : I) (hij : i ≠ j) (c : k2DilateSt_pullback s) :
    k2DilateSt_toQ I s (SteinbergGroup.x i j hij c) =
      QuotientGroup.mk' (k2DilateSt_eventuallyOne I A)
        (k2DilateSt_genFamily I s ⟨i, j, hij, c⟩) :=
  PresentedGroup.toGroup.of _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_toQ_x

/-- The diagonal of the dilations, `g ↦ (μ_{s^r} g)_r`. -/
noncomputable def k2DilateSt_diag :
    SteinbergGroup I (Polynomial A) →* (ℕ → SteinbergGroup I (Polynomial A)) :=
  MonoidHom.pi fun r ↦ SteinbergGroup.ringMap (I := I) (k2CubeDilate_scale A (s ^ r))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_diag

/-- **Through `ι_0`, `k2DilateSt_toQ` is the diagonal of the dilations.** -/
theorem k2DilateSt_toQ_comp_ringMap :
    (k2DilateSt_toQ I s).comp (SteinbergGroup.ringMap (I := I) (k2DilateSt_toPullback s 0)) =
      (QuotientGroup.mk' (k2DilateSt_eventuallyOne I A)).comp (k2DilateSt_diag I s) := by
  refine PresentedGroup.ext ?_
  rintro ⟨i, j, hij, a⟩
  change k2DilateSt_toQ I s (SteinbergGroup.ringMap (k2DilateSt_toPullback s 0)
      (SteinbergGroup.x i j hij a)) =
    QuotientGroup.mk' (k2DilateSt_eventuallyOne I A)
      (k2DilateSt_diag I s (SteinbergGroup.x i j hij a))
  rw [SteinbergGroup.ringMap_x, k2DilateSt_toQ_x, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply]
  refine QuotientGroup.eq.mpr ?_
  obtain ⟨m, hm⟩ := k2DilateSt_family_base s a
  refine (k2DilateSt_mem_eventuallyOne I A _).mpr ⟨m, fun r hr ↦ ?_⟩
  change (SteinbergGroup.x i j hij
      (k2DilateSt_family s r (k2DilateSt_toPullback s 0 a)))⁻¹ *
    SteinbergGroup.ringMap (k2CubeDilate_scale A (s ^ r)) (SteinbergGroup.x i j hij a) = 1
  rw [SteinbergGroup.ringMap_x, hm r hr]
  exact inv_mul_eq_one.mpr rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_toQ_comp_ringMap

/-- **Steinberg dilation from the pullback.**  If `g ∈ St_I(A[X])` dies in `St_I(P)` under
`ι_0 : A[X] → P`, then `g(s^r X) = 1` in `St_I(A[X])` for all large `r`. -/
theorem k2DilateSt_exists_scale_eq_one (g : SteinbergGroup I (Polynomial A))
    (hg : SteinbergGroup.ringMap (I := I) (k2DilateSt_toPullback s 0) g = 1) :
    ∃ m : ℕ, ∀ r : ℕ, m ≤ r →
      SteinbergGroup.ringMap (I := I) (k2CubeDilate_scale A (s ^ r)) g = 1 := by
  have h1 : QuotientGroup.mk' (k2DilateSt_eventuallyOne I A) (k2DilateSt_diag I s g) = 1 := by
    have h2 := DFunLike.congr_fun (k2DilateSt_toQ_comp_ringMap I s) g
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hg, map_one] at h2
    exact h2.symm
  obtain ⟨m, hm⟩ := (k2DilateSt_mem_eventuallyOne I A (k2DilateSt_diag I s g)).mp
    ((QuotientGroup.eq_one_iff (N := k2DilateSt_eventuallyOne I A) (k2DilateSt_diag I s g)).mp h1)
  exact ⟨m, hm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_exists_scale_eq_one

end DilateStColim

end GroupApproximation.BooneHigman.Metabelian.ElemFP
