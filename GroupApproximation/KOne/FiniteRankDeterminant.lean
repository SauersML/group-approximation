import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Determinants of finite-rank perturbations of the identity

`non_mf_groups_exist.tex`, `cor:leavitt-mf-quotient`, asserts
`K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}`.  The injectivity half of that identification
(`LeavittKOneFormula.ScalarKernel`) is proved in this repository by a
*regularized determinant* on the Toeplitz representation of the Leavitt
relations, and every step of that proof takes the determinant of an operator
of the form `1 + (finite rank)` on an infinite-dimensional vector space.  This
module is that determinant, for an arbitrary vector space over a field.

* `FiniteRank f` --- the range of `f` is finite-dimensional; closed under sums,
  negatives, and composition on either side.
* `fdet f` --- the determinant of `f` restricted to the range of `f - 1`, which
  `f` maps into itself.  No choice is involved.
* `det_restrict_eq_fdet` --- **the value does not depend on the subspace**: for
  every finite-dimensional submodule `U` containing the range of `f - 1`, the
  determinant of `f` on `U` is `fdet f`.  On `U` modulo the range of `f - 1` the
  map `f` is the identity, so the block-triangular determinant formula of
  `LinearMap.det_eq_det_mul_det` gives the independence.
* `fdet_mul` --- multiplicative on finite-rank perturbations of the identity.
* `fdet_eq_det_of_comp_eq` --- transport along an injective intertwiner, from
  which `fdet_eq_det` (on a finite-dimensional space `fdet` is `det`),
  `fdet_units_conj` (conjugation by a unit), `fdet_conj` (conjugation by a linear
  equivalence), `fdet_prodMap` and `fdet_pi` (block formulas) all follow.
* `fdet_eq_one_of_sub_one_mul_self_eq_zero` --- a square-zero perturbation has
  determinant one.

Nothing here is specific to the manuscript; the consumer is
`KOne/RegularizedDeterminant.lean`.
-/

namespace GroupApproximation
namespace FiniteRankDet

variable {k : Type*} [Field k]

section Basic

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- An endomorphism whose range is finite-dimensional. -/
def FiniteRank (f : Module.End k V) : Prop :=
  FiniteDimensional k (LinearMap.range f)

theorem FiniteRank.of_range_le {f : Module.End k V} {S : Submodule k V}
    [FiniteDimensional k S] (h : LinearMap.range f ≤ S) : FiniteRank f :=
  Submodule.finiteDimensional_of_le h

theorem finiteRank_zero : FiniteRank (0 : Module.End k V) :=
  FiniteRank.of_range_le (S := ⊥) (le_of_eq LinearMap.range_zero)

theorem FiniteRank.add {f g : Module.End k V} (hf : FiniteRank f) (hg : FiniteRank g) :
    FiniteRank (f + g) := by
  haveI : FiniteDimensional k (LinearMap.range f) := hf
  haveI : FiniteDimensional k (LinearMap.range g) := hg
  exact FiniteRank.of_range_le (S := LinearMap.range f ⊔ LinearMap.range g)
    (LinearMap.range_add_le f g)

theorem FiniteRank.neg {f : Module.End k V} (hf : FiniteRank f) : FiniteRank (-f) := by
  haveI : FiniteDimensional k (LinearMap.range f) := hf
  exact FiniteRank.of_range_le (S := LinearMap.range f) (le_of_eq (LinearMap.range_neg f))

theorem FiniteRank.sub {f g : Module.End k V} (hf : FiniteRank f) (hg : FiniteRank g) :
    FiniteRank (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- A finite-rank map composed on the left stays finite rank. -/
theorem FiniteRank.mul_left (g : Module.End k V) {f : Module.End k V} (hf : FiniteRank f) :
    FiniteRank (g * f) := by
  haveI : FiniteDimensional k (LinearMap.range f) := hf
  exact FiniteRank.of_range_le (S := (LinearMap.range f).map g)
    (le_of_eq (LinearMap.range_comp f g))

/-- A finite-rank map composed on the right stays finite rank. -/
theorem FiniteRank.mul_right {f : Module.End k V} (hf : FiniteRank f) (g : Module.End k V) :
    FiniteRank (f * g) := by
  haveI : FiniteDimensional k (LinearMap.range f) := hf
  exact FiniteRank.of_range_le (S := LinearMap.range f) (LinearMap.range_comp_le_range g f)

theorem FiniteRank.smul (c : k) {f : Module.End k V} (hf : FiniteRank f) :
    FiniteRank (c • f) := by
  have h : c • f = (c • (1 : Module.End k V)) * f := by rw [smul_mul_assoc, one_mul]
  rw [h]
  exact hf.mul_left _

/-- If `f - 1` and `g - 1` have finite rank, so does `f * g - 1`. -/
theorem FiniteRank.mul_sub_one {f g : Module.End k V} (hf : FiniteRank (f - 1))
    (hg : FiniteRank (g - 1)) : FiniteRank (f * g - 1) := by
  have h : f * g - 1 = (f - 1) * g + (g - 1) := by noncomm_ring
  rw [h]
  exact (hf.mul_right g).add hg

/-- If `u - 1` has finite rank for a unit `u`, so does `u⁻¹ - 1`. -/
theorem FiniteRank.inv_sub_one (u : (Module.End k V)ˣ) (hu : FiniteRank ((u : Module.End k V) - 1)) :
    FiniteRank (((u⁻¹ : (Module.End k V)ˣ) : Module.End k V) - 1) := by
  have h : ((u⁻¹ : (Module.End k V)ˣ) : Module.End k V) - 1
      = -(((u⁻¹ : (Module.End k V)ˣ) : Module.End k V) * ((u : Module.End k V) - 1)) := by
    rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
  rw [h]
  exact (hu.mul_left _).neg

/-! ### The determinant -/

/-- `f` maps the range of `f - 1` into itself. -/
theorem mapsTo_range_sub_one (f : Module.End k V) :
    ∀ x ∈ LinearMap.range (f - 1), f x ∈ LinearMap.range (f - 1) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨f v, ?_⟩
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]

/-- `f` maps every submodule containing the range of `f - 1` into itself. -/
theorem mapsTo_of_range_sub_one_le {f : Module.End k V} {U : Submodule k V}
    (h : LinearMap.range (f - 1) ≤ U) : ∀ x ∈ U, f x ∈ U := by
  intro x hx
  have h1 : (f - 1) x ∈ U := h ⟨x, rfl⟩
  have h2 : f x = (f - 1) x + x := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, sub_add_cancel]
  rw [h2]
  exact U.add_mem h1 hx

/-- **The determinant of a finite-rank perturbation of the identity**: the
determinant of `f` on the range of `f - 1`.  (When that range is
infinite-dimensional, `LinearMap.det` returns `1`; every lemma below assumes the
range is finite-dimensional.) -/
noncomputable def fdet (f : Module.End k V) : k :=
  LinearMap.det (f.restrict (mapsTo_range_sub_one f))

/-- **Independence of the subspace.**  For every finite-dimensional submodule `U`
containing the range of `f - 1`, the determinant of `f` on `U` is `fdet f`. -/
theorem det_restrict_eq_fdet {f : Module.End k V} {U : Submodule k V} [FiniteDimensional k U]
    (h : LinearMap.range (f - 1) ≤ U) (hU : ∀ x ∈ U, f x ∈ U) :
    LinearMap.det (f.restrict hU) = fdet f := by
  let W : Submodule k U := (LinearMap.range (f - 1)).comap U.subtype
  have hW : W ≤ W.comap (f.restrict hU) := by
    intro x hx
    exact mapsTo_range_sub_one f (x : V) hx
  rw [LinearMap.det_eq_det_mul_det W (f.restrict hU) hW]
  have hQ : W.mapQ W (f.restrict hU) hW = LinearMap.id := by
    apply Submodule.linearMap_qext
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_apply, Submodule.Quotient.eq]
    refine ⟨(x : V), ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_subtype,
      Submodule.coe_sub, LinearMap.restrict_coe_apply]
  rw [hQ, LinearMap.det_id, mul_one]
  have hconj : ((Submodule.comapSubtypeEquivOfLe h : W ≃ₗ[k] LinearMap.range (f - 1)) :
        W →ₗ[k] LinearMap.range (f - 1)) ∘ₗ (f.restrict hU).restrict hW ∘ₗ
      ((Submodule.comapSubtypeEquivOfLe h).symm : LinearMap.range (f - 1) →ₗ[k] W)
      = f.restrict (mapsTo_range_sub_one f) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rfl
  rw [fdet, ← hconj, LinearMap.det_conj]

theorem fdet_one : fdet (1 : Module.End k V) = 1 := by
  have h : (1 : Module.End k V).restrict (mapsTo_range_sub_one 1) = LinearMap.id :=
    LinearMap.ext fun x => Subtype.ext rfl
  rw [fdet, h, LinearMap.det_id]

/-- Multiplicativity against any common finite-dimensional invariant subspace. -/
theorem fdet_mul_of_le {f g : Module.End k V} {U : Submodule k V} [FiniteDimensional k U]
    (hfU : LinearMap.range (f - 1) ≤ U) (hgU : LinearMap.range (g - 1) ≤ U) :
    fdet (f * g) = fdet f * fdet g := by
  have hfgU : LinearMap.range (f * g - 1) ≤ U := by
    rintro _ ⟨v, rfl⟩
    have hdec : (f * g - 1) v = (f - 1) (g v) + (g - 1) v := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply]
      abel
    rw [hdec]
    exact U.add_mem (hfU ⟨g v, rfl⟩) (hgU ⟨v, rfl⟩)
  rw [← det_restrict_eq_fdet hfgU (mapsTo_of_range_sub_one_le hfgU),
    ← det_restrict_eq_fdet hfU (mapsTo_of_range_sub_one_le hfU),
    ← det_restrict_eq_fdet hgU (mapsTo_of_range_sub_one_le hgU)]
  have hsplit : (f * g).restrict (mapsTo_of_range_sub_one_le hfgU)
      = f.restrict (mapsTo_of_range_sub_one_le hfU) * g.restrict (mapsTo_of_range_sub_one_le hgU) :=
    LinearMap.ext fun x => Subtype.ext rfl
  rw [hsplit, map_mul]

/-- **`fdet` is multiplicative** on finite-rank perturbations of the identity. -/
theorem fdet_mul {f g : Module.End k V} (hf : FiniteRank (f - 1)) (hg : FiniteRank (g - 1)) :
    fdet (f * g) = fdet f * fdet g := by
  haveI : FiniteDimensional k (LinearMap.range (f - 1)) := hf
  haveI : FiniteDimensional k (LinearMap.range (g - 1)) := hg
  exact fdet_mul_of_le (U := LinearMap.range (f - 1) ⊔ LinearMap.range (g - 1))
    le_sup_left le_sup_right

/-- The determinant of a unit perturbation is a unit. -/
theorem fdet_units_mul_inv (u : (Module.End k V)ˣ) (hu : FiniteRank ((u : Module.End k V) - 1)) :
    fdet (u : Module.End k V) * fdet ((u⁻¹ : (Module.End k V)ˣ) : Module.End k V) = 1 := by
  rw [← fdet_mul hu (FiniteRank.inv_sub_one u hu), Units.mul_inv, fdet_one]

/-- A square-zero perturbation of the identity has determinant one. -/
theorem fdet_eq_one_of_sub_one_mul_self_eq_zero {f : Module.End k V}
    (h : (f - 1) * (f - 1) = 0) : fdet f = 1 := by
  have hid : f.restrict (mapsTo_range_sub_one f) = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨v, hv⟩ := x.2
    have h2 : (f - 1) (x : V) = 0 := by
      rw [← hv]
      exact LinearMap.congr_fun h v
    have h3 : f (x : V) = (x : V) := by
      have := h2
      simp only [LinearMap.sub_apply, Module.End.one_apply] at this
      exact sub_eq_zero.mp this
    exact h3
  rw [fdet, hid, LinearMap.det_id]

end Basic

/-! ### Transport -/

section Transport

variable {V : Type*} [AddCommGroup V] [Module k V]
variable {V' : Type*} [AddCommGroup V'] [Module k V']

/-- **Transport along an injective intertwiner from a finite-dimensional space.**
If `j : M → V'` is injective, `f' ∘ j = j ∘ f`, and the range of `f' - 1` lies in
the range of `j`, then `fdet f' = det f`. -/
theorem fdet_eq_det_of_comp_eq {M : Type*} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (j : M →ₗ[k] V') (hj : Function.Injective j) {f : Module.End k M} {f' : Module.End k V'}
    (hcomm : f' ∘ₗ j = j ∘ₗ f) (hrange : LinearMap.range (f' - 1) ≤ LinearMap.range j) :
    fdet f' = LinearMap.det f := by
  have hinv : ∀ x ∈ LinearMap.range j, f' x ∈ LinearMap.range j := by
    rintro _ ⟨y, rfl⟩
    exact ⟨f y, (LinearMap.congr_fun hcomm y).symm⟩
  rw [← det_restrict_eq_fdet hrange hinv]
  have hconj : ((LinearEquiv.ofInjective (f := j) hj : M ≃ₗ[k] LinearMap.range j) :
        M →ₗ[k] LinearMap.range j) ∘ₗ f ∘ₗ
      ((LinearEquiv.ofInjective (f := j) hj).symm : LinearMap.range j →ₗ[k] M)
      = f'.restrict hinv := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    obtain ⟨x, rfl⟩ := (LinearEquiv.ofInjective (f := j) hj).surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.restrict_coe_apply, LinearEquiv.ofInjective_apply]
    exact (LinearMap.congr_fun hcomm x).symm
  rw [← hconj, LinearMap.det_conj]

/-- On a finite-dimensional space `fdet` is the determinant. -/
theorem fdet_eq_det [FiniteDimensional k V] (f : Module.End k V) : fdet f = LinearMap.det f :=
  fdet_eq_det_of_comp_eq LinearMap.id Function.injective_id (LinearMap.ext fun _ => rfl)
    (by rw [LinearMap.range_id]; exact le_top)

/-- **Transport between two arbitrary spaces.**  If `j : V → V'` is injective,
`f' ∘ j = j ∘ f`, `f - 1` has finite rank, and the range of `f' - 1` is the image
of a part of the range of `f - 1`, then `fdet f' = fdet f`. -/
theorem fdet_of_comp_eq (j : V →ₗ[k] V') (hj : Function.Injective j)
    {f : Module.End k V} {f' : Module.End k V'} (hf : FiniteRank (f - 1))
    (hcomm : f' ∘ₗ j = j ∘ₗ f)
    (hrange : LinearMap.range (f' - 1) ≤ (LinearMap.range (f - 1)).map j) :
    fdet f' = fdet f := by
  haveI : FiniteDimensional k (LinearMap.range (f - 1)) := hf
  have hj' : Function.Injective (j ∘ₗ (LinearMap.range (f - 1)).subtype) :=
    hj.comp Subtype.val_injective
  refine fdet_eq_det_of_comp_eq (j ∘ₗ (LinearMap.range (f - 1)).subtype) hj'
    (f := f.restrict (mapsTo_range_sub_one f)) ?_ ?_
  · refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.restrict_coe_apply]
    exact LinearMap.congr_fun hcomm (x : V)
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hrange hy
    exact ⟨⟨z, hz⟩, rfl⟩

/-- **Conjugation by a linear equivalence.** -/
theorem fdet_conj (e : V ≃ₗ[k] V') {f : Module.End k V} (hf : FiniteRank (f - 1)) :
    fdet (e.conj f) = fdet f := by
  refine fdet_of_comp_eq (e : V →ₗ[k] V') e.injective hf ?_ ?_
  · refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.conj_apply_apply,
      LinearEquiv.symm_apply_apply]
  · rintro _ ⟨v, rfl⟩
    refine ⟨(f - 1) (e.symm v), ⟨e.symm v, rfl⟩, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe,
      LinearEquiv.conj_apply_apply, map_sub, LinearEquiv.apply_symm_apply]

/-- **Conjugation by a unit.** -/
theorem fdet_units_conj (u : (Module.End k V)ˣ) {f : Module.End k V} (hf : FiniteRank (f - 1)) :
    fdet ((u : Module.End k V) * f * ((u⁻¹ : (Module.End k V)ˣ) : Module.End k V)) = fdet f := by
  have hleft : ∀ x, ((u⁻¹ : (Module.End k V)ˣ) : Module.End k V) ((u : Module.End k V) x) = x :=
    fun x => by rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  have hright : ∀ x, (u : Module.End k V) (((u⁻¹ : (Module.End k V)ˣ) : Module.End k V) x) = x :=
    fun x => by rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  refine fdet_of_comp_eq (u : Module.End k V) (Function.LeftInverse.injective hleft) hf ?_ ?_
  · show (u : Module.End k V) * f * ((u⁻¹ : (Module.End k V)ˣ) : Module.End k V) *
        (u : Module.End k V) = (u : Module.End k V) * f
    rw [mul_assoc ((u : Module.End k V) * f), Units.inv_mul, mul_one]
  · rintro _ ⟨v, rfl⟩
    refine ⟨(f - 1) (((u⁻¹ : (Module.End k V)ˣ) : Module.End k V) v),
      ⟨((u⁻¹ : (Module.End k V)ˣ) : Module.End k V) v, rfl⟩, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply, map_sub, hright]

end Transport

/-! ### Block formulas -/

section Blocks

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- **Product block formula.**  On `U × V` with `U` finite-dimensional,
`fdet (A × B) = det A * fdet B`. -/
theorem fdet_prodMap {U : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (A : Module.End k U) {B : Module.End k V} (hB : FiniteRank (B - 1)) :
    fdet (A.prodMap B) = LinearMap.det A * fdet B := by
  haveI : FiniteDimensional k (LinearMap.range (B - 1)) := hB
  have hj : Function.Injective
      ((LinearMap.id : U →ₗ[k] U).prodMap (LinearMap.range (B - 1)).subtype) := by
    rintro ⟨u, w⟩ ⟨u', w'⟩ h
    simp only [LinearMap.prodMap_apply, LinearMap.id_apply, Submodule.coe_subtype,
      Prod.mk.injEq] at h
    exact Prod.ext h.1 (Subtype.ext h.2)
  rw [fdet_eq_det_of_comp_eq _ hj (f := A.prodMap (B.restrict (mapsTo_range_sub_one B))),
    LinearMap.det_prodMap, fdet]
  · refine LinearMap.ext fun p => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      Submodule.coe_subtype, LinearMap.restrict_coe_apply]
  · rintro _ ⟨p, rfl⟩
    refine ⟨((A - 1) p.1, ⟨(B - 1) p.2, ⟨p.2, rfl⟩⟩), ?_⟩
    refine Prod.ext ?_ ?_ <;>
      simp [LinearMap.prodMap_apply, LinearMap.id_apply, Submodule.coe_subtype,
        LinearMap.sub_apply, Module.End.one_apply]

/-- **Diagonal block formula.**  `fdet (g ⊕ ⋯ ⊕ g) = (fdet g) ^ |ι|`. -/
theorem fdet_pi {ι : Type*} [Fintype ι] {g : Module.End k V} (hg : FiniteRank (g - 1)) :
    fdet (LinearMap.pi fun i : ι => g ∘ₗ LinearMap.proj i) = fdet g ^ Fintype.card ι := by
  haveI : FiniteDimensional k (LinearMap.range (g - 1)) := hg
  let j : (ι → LinearMap.range (g - 1)) →ₗ[k] (ι → V) :=
    LinearMap.pi fun i => (LinearMap.range (g - 1)).subtype ∘ₗ LinearMap.proj i
  have hj : Function.Injective j := by
    intro x y h
    funext i
    exact Subtype.ext (congrFun h i)
  rw [fdet_eq_det_of_comp_eq j hj
      (f := LinearMap.pi fun i : ι => (g.restrict (mapsTo_range_sub_one g)) ∘ₗ LinearMap.proj i),
    LinearMap.det_pi, Finset.prod_const, Finset.card_univ, fdet]
  · refine LinearMap.ext fun x => funext fun i => ?_
    rfl
  · rintro _ ⟨x, rfl⟩
    refine ⟨fun i => ⟨(g - 1) (x i), ⟨x i, rfl⟩⟩, ?_⟩
    funext i
    rfl

/-- The identity block contributes nothing: `fdet (A × 1) = det A`. -/
theorem fdet_prodMap_one {U : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (A : Module.End k U) : fdet (A.prodMap (1 : Module.End k V)) = LinearMap.det A := by
  have h1 : FiniteRank ((1 : Module.End k V) - 1) := by
    rw [sub_self]; exact finiteRank_zero
  rw [fdet_prodMap A h1, fdet_one, mul_one]

end Blocks

end FiniteRankDet
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.FiniteRankDet.det_restrict_eq_fdet
#audit_axioms GroupApproximation.FiniteRankDet.fdet_mul
#audit_axioms GroupApproximation.FiniteRankDet.fdet_units_mul_inv
#audit_axioms GroupApproximation.FiniteRankDet.fdet_eq_one_of_sub_one_mul_self_eq_zero
#audit_axioms GroupApproximation.FiniteRankDet.fdet_eq_det_of_comp_eq
#audit_axioms GroupApproximation.FiniteRankDet.fdet_eq_det
#audit_axioms GroupApproximation.FiniteRankDet.fdet_of_comp_eq
#audit_axioms GroupApproximation.FiniteRankDet.fdet_conj
#audit_axioms GroupApproximation.FiniteRankDet.fdet_units_conj
#audit_axioms GroupApproximation.FiniteRankDet.fdet_prodMap
#audit_axioms GroupApproximation.FiniteRankDet.fdet_pi
#audit_axioms GroupApproximation.FiniteRankDet.fdet_prodMap_one
