import GroupApproximation.Analysis.ExactnessPermanence
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.WellFounded
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Property A pulls back along coarse embeddings

`non_mf_group_notes.tex`, paragraph `\paragraph{Exactness.}` after
`prop:blocknormalform`: *"The group `Σ ≤ GL₄(ℚ)` is exact by
Guentner--Higson--Weinberger"*.  The Guentner--Higson--Weinberger argument
coarsely embeds the linear group into an amenable (solvable) group and pulls
property A back.  This file proves the pull-back step in the repository's
finite-scale, metric-free form of property A
(`ExactnessPermanence.HasPropertyA`).

A map `f : Γ → D` of groups is

* *bornologous at finite scale* when every finite set of increments `R` of `Γ`
  is sent to a finite set of increments `(f g)⁻¹ f (g r)` of `D`;
* *effectively proper at finite scale* when every finite set of increments `C`
  of `D` pulls back to a finite set of increments of `Γ`.

`hasPropertyA_of_coarse`: if `D` is countable and has property A, and `f` has
both properties, then `Γ` has property A.  The measures on `Γ` are the
push-forwards of the measures on `D` under a nearest-point projection
`D → Γ`, defined by minimising a fixed injection `D → ℕ`.
-/

namespace GroupApproximation.Full.NN09b

open GroupApproximation.ExactnessPermanence

universe u v

section Projection

variable (D : Type v)

/-- A fixed injection of a countable type into `ℕ`, used as a length. -/
noncomputable def lengthNat [Countable D] : D → ℕ :=
  Classical.choose (Countable.exists_injective_nat D)

theorem lengthNat_injective [Countable D] : Function.Injective (lengthNat D) :=
  Classical.choose_spec (Countable.exists_injective_nat D)

/-- Only finitely many elements have length at most `M`. -/
theorem finite_lengthNat_le [Countable D] (M : ℕ) : {e : D | lengthNat D e ≤ M}.Finite := by
  have h := (Set.finite_le_nat M).preimage (Set.injOn_of_injective (lengthNat_injective D))
  exact h

end Projection

section Nearest

variable {Γ : Type u} {D : Type v}

/-- A nearest point of the image of `f` to `d`: an element `γ` minimising the
length of the increment `(f γ)⁻¹ d`. -/
noncomputable def nearest [Group D] [Countable D] [Nonempty Γ] (f : Γ → D) (d : D) : Γ :=
  Function.argmin (fun γ : Γ ↦ lengthNat D ((f γ)⁻¹ * d))

theorem nearest_le [Group D] [Countable D] [Nonempty Γ] (f : Γ → D) (d : D) (γ : Γ) :
    lengthNat D ((f (nearest f d))⁻¹ * d) ≤ lengthNat D ((f γ)⁻¹ * d) :=
  Function.argmin_le (fun γ : Γ ↦ lengthNat D ((f γ)⁻¹ * d)) γ

end Nearest

section PushForward

variable {Γ : Type u} {D : Type v}

/-- The push-forward to `Γ`, along `π`, of the measure attached to `f g`. -/
noncomputable def pushWeight [Group D] [DecidableEq Γ] [DecidableEq D]
    {C : Finset D} {ε : ℝ} (W : PropertyAWitness D C ε) (f : Γ → D) (π : D → Γ)
    (g x : Γ) : ℝ :=
  ∑ d ∈ (W.template.image fun s ↦ f g * s).filter (fun d ↦ π d = x), W.weight (f g) d

theorem weight_eq_zero_of_not_mem_image [Group D] [DecidableEq D]
    {C : Finset D} {ε : ℝ} (W : PropertyAWitness D C ε) (f : Γ → D)
    (g : Γ) (d : D) (hd : d ∉ W.template.image fun s ↦ f g * s) :
    W.weight (f g) d = 0 := by
  refine W.weight_eq_zero (f g) d fun hs ↦ hd ?_
  exact Finset.mem_image.mpr ⟨(f g)⁻¹ * d, hs, mul_inv_cancel_left (f g) d⟩

theorem pushWeight_nonneg [Group D] [DecidableEq Γ] [DecidableEq D]
    {C : Finset D} {ε : ℝ} (W : PropertyAWitness D C ε) (f : Γ → D) (π : D → Γ)
    (g x : Γ) : 0 ≤ pushWeight W f π g x :=
  Finset.sum_nonneg fun d _ ↦ W.weight_nonneg (f g) d

/-- The push-forward may be computed over any finite superset of the support. -/
theorem pushWeight_eq_sum_superset [Group D] [DecidableEq Γ] [DecidableEq D]
    {C : Finset D} {ε : ℝ} (W : PropertyAWitness D C ε) (f : Γ → D)
    (π : D → Γ) (g x : Γ) (U : Finset D)
    (hU : (W.template.image fun s ↦ f g * s) ⊆ U) :
    pushWeight W f π g x = ∑ d ∈ U.filter (fun d ↦ π d = x), W.weight (f g) d := by
  unfold pushWeight
  refine Finset.sum_subset (Finset.filter_subset_filter hU) ?_
  intro d hdU hdS
  refine weight_eq_zero_of_not_mem_image W f g d fun hd ↦ hdS ?_
  exact Finset.mem_filter.mpr ⟨hd, (Finset.mem_filter.mp hdU).2⟩

/-- Push-forward does not increase `ℓ¹` distances. -/
theorem sum_abs_sub_pushWeight_le [Group D] [DecidableEq Γ] [DecidableEq D]
    {C : Finset D} {ε : ℝ} (W : PropertyAWitness D C ε) (f : Γ → D)
    (π : D → Γ) (g h : Γ) (U : Finset D)
    (hg : (W.template.image fun s ↦ f g * s) ⊆ U)
    (hh : (W.template.image fun s ↦ f h * s) ⊆ U) (T : Finset Γ) :
    ∑ x ∈ T, |pushWeight W f π g x - pushWeight W f π h x| ≤
      ∑ d ∈ U, |W.weight (f g) d - W.weight (f h) d| := by
  calc ∑ x ∈ T, |pushWeight W f π g x - pushWeight W f π h x|
      = ∑ x ∈ T, |∑ d ∈ U.filter (fun d ↦ π d = x),
          (W.weight (f g) d - W.weight (f h) d)| := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [pushWeight_eq_sum_superset W f π g x U hg,
          pushWeight_eq_sum_superset W f π h x U hh, Finset.sum_sub_distrib]
    _ ≤ ∑ x ∈ T, ∑ d ∈ U.filter (fun d ↦ π d = x),
          |W.weight (f g) d - W.weight (f h) d| :=
        Finset.sum_le_sum fun x _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ U.filter (fun d ↦ π d ∈ T), |W.weight (f g) d - W.weight (f h) d| :=
        Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ d ∈ U, |W.weight (f g) d - W.weight (f h) d| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ ↦ abs_nonneg _

/-- The push-forward has total mass one, once `π` maps the support of the
measure at `f g` into `g · T`. -/
theorem sum_pushWeight_eq_one [Group Γ] [Group D] [DecidableEq Γ] [DecidableEq D]
    {C : Finset D} {ε : ℝ} (W : PropertyAWitness D C ε) (f : Γ → D)
    (π : D → Γ) (T : Finset Γ) (g : Γ)
    (hπ : ∀ s ∈ W.template, g⁻¹ * π (f g * s) ∈ T) :
    ∑ s ∈ T, pushWeight W f π g (g * s) = 1 := by
  have hinjT : Set.InjOn (fun s : Γ ↦ g * s) (T : Set Γ) :=
    fun a _ b _ hab ↦ mul_left_cancel hab
  have hinjD : Set.InjOn (fun s : D ↦ f g * s) (W.template : Set D) :=
    fun a _ b _ hab ↦ mul_left_cancel hab
  have hmaps : ∀ d ∈ W.template.image (fun s ↦ f g * s),
      π d ∈ T.image (fun s ↦ g * s) := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_image.mpr ⟨g⁻¹ * π (f g * s), hπ s hs, mul_inv_cancel_left g _⟩
  calc ∑ s ∈ T, pushWeight W f π g (g * s)
      = ∑ x ∈ T.image (fun s ↦ g * s), pushWeight W f π g x :=
        (Finset.sum_image (f := pushWeight W f π g) hinjT).symm
    _ = ∑ d ∈ W.template.image (fun s ↦ f g * s), W.weight (f g) d :=
        Finset.sum_fiberwise_of_maps_to hmaps (W.weight (f g))
    _ = ∑ s ∈ W.template, W.weight (f g) (f g * s) :=
        Finset.sum_image (f := W.weight (f g)) hinjD
    _ = 1 := W.weight_sum (f g)

/-- The push-forward is supported in `g · T`, under the same hypothesis. -/
theorem pushWeight_eq_zero [Group Γ] [Group D] [DecidableEq Γ] [DecidableEq D]
    {C : Finset D} {ε : ℝ} (W : PropertyAWitness D C ε) (f : Γ → D)
    (π : D → Γ) (T : Finset Γ) (g x : Γ)
    (hπ : ∀ s ∈ W.template, g⁻¹ * π (f g * s) ∈ T) (hx : g⁻¹ * x ∉ T) :
    pushWeight W f π g x = 0 := by
  unfold pushWeight
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  obtain ⟨hdS, hdx⟩ := Finset.mem_filter.mp hd
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hdS
  have hmem := hπ s hs
  rw [hdx] at hmem
  exact absurd hmem hx

end PushForward

section Transfer

variable {Γ : Type u} {D : Type v} [Group Γ] [Group D]

/-- **Property A pulls back along a coarse embedding into a countable group.**

This is the transfer step of Guentner--Higson--Weinberger used for
`\paragraph{Exactness.}` in `non_mf_group_notes.tex`. -/
theorem hasPropertyA_of_coarse [Countable D] (f : Γ → D)
    (hbor : ∀ R : Finset Γ, ∃ C : Finset D, ∀ g r, r ∈ R → (f g)⁻¹ * f (g * r) ∈ C)
    (hprop : ∀ C : Finset D, ∃ T : Finset Γ, ∀ g h, (f g)⁻¹ * f h ∈ C → g⁻¹ * h ∈ T)
    (hD : HasPropertyA D) : HasPropertyA Γ := by
  classical
  intro R ε hε
  obtain ⟨C, hC⟩ := hbor R
  obtain ⟨W⟩ := hD C ε hε
  let M : ℕ := W.template.sup (lengthNat D)
  let B : Finset D := (finite_lengthNat_le D M).toFinset
  obtain ⟨T, hT⟩ := hprop ((W.template ×ˢ B).image fun p ↦ p.1 * p.2⁻¹)
  have hπ : ∀ g : Γ, ∀ s ∈ W.template, g⁻¹ * nearest f (f g * s) ∈ T := by
    intro g s hs
    refine hT g (nearest f (f g * s)) ?_
    let e : D := (f (nearest f (f g * s)))⁻¹ * (f g * s)
    have hle : lengthNat D e ≤ M := by
      calc lengthNat D e ≤ lengthNat D ((f g)⁻¹ * (f g * s)) := nearest_le f (f g * s) g
        _ = lengthNat D s := by rw [inv_mul_cancel_left]
        _ ≤ M := Finset.le_sup hs
    have hB : e ∈ B := (Set.Finite.mem_toFinset (finite_lengthNat_le D M)).mpr hle
    refine Finset.mem_image.mpr ⟨(s, e), Finset.mem_product.mpr ⟨hs, hB⟩, ?_⟩
    show s * ((f (nearest f (f g * s)))⁻¹ * (f g * s))⁻¹ = (f g)⁻¹ * f (nearest f (f g * s))
    rw [mul_inv_rev, inv_inv, mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel,
      one_mul]
  refine ⟨{
    template := T
    weight := pushWeight W f (nearest f)
    weight_nonneg := pushWeight_nonneg W f (nearest f)
    weight_eq_zero := fun g x hx ↦ pushWeight_eq_zero W f (nearest f) T g x (hπ g) hx
    weight_sum := fun g ↦ sum_pushWeight_eq_one W f (nearest f) T g (hπ g)
    weight_close := ?_ }⟩
  intro g h hgh T' _ _
  have hCgh : (f g)⁻¹ * f h ∈ C := by
    have hmem := hC g (g⁻¹ * h) hgh
    rwa [mul_inv_cancel_left] at hmem
  refine (sum_abs_sub_pushWeight_le W f (nearest f) g h
    ((W.template.image fun s ↦ f g * s) ∪ (W.template.image fun s ↦ f h * s))
    Finset.subset_union_left Finset.subset_union_right T').trans ?_
  refine W.weight_close (f g) (f h) hCgh _ ?_ ?_
  · intro d hd
    by_contra hdU
    exact hd (weight_eq_zero_of_not_mem_image W f g d fun hmem ↦
      hdU (Finset.mem_union_left _ hmem))
  · intro d hd
    by_contra hdU
    exact hd (weight_eq_zero_of_not_mem_image W f h d fun hmem ↦
      hdU (Finset.mem_union_right _ hmem))

end Transfer

end GroupApproximation.Full.NN09b
