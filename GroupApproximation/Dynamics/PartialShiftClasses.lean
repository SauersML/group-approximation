import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order

/-!
# Exponent classes of a finite family of partial shifts

`non_mf_groups_exist.tex`, `\label{lem:transient-matrices}`, proof, tex 1494–1497 and 1505–1511:

> Include inverse partial shifts, and let $C$ be the union of their
> sources and ranges.  The equivalence relation they generate on $C$
> has classes of size at most $m$.  Erasing loops shortens any path
> between related points to at most $m-1$ steps.

> Order its atoms
> and select the point in the first occupied atom as the class
> representative.  The representative set is clopen, because presence
> of a related point in an earlier atom is a finite clopen test.
> Refine it according to the occupied atoms, the shift exponents to
> each level, and all original coefficient values.  On each cell the
> classes have a fixed size $h$ and continuously enumerated clopen
> levels.

Here `T : X ≃ₜ X`, `C ⊆ X`, and `E : Finset ℤ` holds the exponents of the partial shifts.

* `stepExponents E = E ∪ -E`: the partial shifts together with their inverses;
* `reachableExponents T C E r x`: the exponents `d` with `T^d x ∈ C` reached from `x` in at most `r`
  steps from `stepExponents E` through points of `C`;
* `ExponentBound T C m`: a finite set of exponents returning `x` to `C` has at most `m` elements
  (aperiodicity on `C` together with the orbit bound); `card_reachableExponents_le`;
* `isLocallyConstant_reachableExponents`, `isClopen_setOf_reachableExponents_eq` for clopen `C`;
* `baseSet`, `baseCell`, `level`, their clopenness, and `mem_level_iff`;
* model tests: `modelShift` (the shift of `ℤ`, `C = [0, 1]`, `E = {1}`, `m = 2`) has base cell
  `{0}` over the class `{0, 1}` with levels `{0}` and `{1}`; `modelSwap` has a periodic point in
  `C = {true}` and fails `ExponentBound` for every `m`.
-/

namespace GroupApproximation.ChainCore

open Topology

/-- The step exponents: the partial shifts `E` together with their inverses (tex 1494). -/
def stepExponents (E : Finset ℤ) : Finset ℤ :=
  E ∪ E.image Neg.neg

theorem mem_stepExponents {E : Finset ℤ} {e : ℤ} : e ∈ stepExponents E ↔ e ∈ E ∨ -e ∈ E := by
  simp only [stepExponents, Finset.mem_union, Finset.mem_image]
  refine or_congr_right ⟨?_, fun h => ⟨-e, h, neg_neg e⟩⟩
  rintro ⟨a, ha, rfl⟩
  rwa [neg_neg]

theorem neg_mem_stepExponents {E : Finset ℤ} {e : ℤ} (he : e ∈ stepExponents E) :
    -e ∈ stepExponents E := by
  rw [mem_stepExponents, neg_neg]
  exact (mem_stepExponents.mp he).symm

variable {X : Type*} [TopologicalSpace X]

open Classical in
/-- `reachableExponents T C E r x`: the exponents `d` with `T^d x ∈ C` reached from `x` in at most
`r` steps from `stepExponents E`, every intermediate point lying in `C`. -/
noncomputable def reachableExponents (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) : ℕ → X → Finset ℤ
  | 0, x => ({0} : Finset ℤ).filter fun d => (T ^ d) x ∈ C
  | r + 1, x =>
    (reachableExponents T C E r x ∪
      ((reachableExponents T C E r x).biUnion fun a => (stepExponents E).image (a + ·))).filter
        fun d => (T ^ d) x ∈ C

/-- **The orbit bound** (tex 1489–1491): a finite set of exponents returning `x` to `C` has at
most `m` elements.  This is aperiodicity on `C` together with the bound on orbit intersections. -/
def ExponentBound (T : X ≃ₜ X) (C : Set X) (m : ℕ) : Prop :=
  ∀ (x : X) (S : Finset ℤ), (∀ n ∈ S, (T ^ n) x ∈ C) → S.card ≤ m

/-- The representative set (tex 1505–1507): points of `C` all of whose class exponents are
nonnegative, so the point itself occupies the first level. -/
def baseSet (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) (m : ℕ) : Set X :=
  C ∩ {x | ∀ d ∈ reachableExponents T C E (m - 1) x, 0 ≤ d}

/-- A base cell (tex 1508–1509): the representatives with prescribed exponent set `S`. -/
def baseCell (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) (m : ℕ) (S : Finset ℤ) : Set X :=
  baseSet T C E m ∩ {x | reachableExponents T C E (m - 1) x = S}

/-- The level of exponent `d` over the base cell of `S` (tex 1510–1511). -/
def level (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) (m : ℕ) (S : Finset ℤ) (d : ℤ) : Set X :=
  (T ^ (-d)) ⁻¹' baseCell T C E m S

variable {T : X ≃ₜ X} {C : Set X} {E : Finset ℤ} {m : ℕ}

theorem mem_reachableExponents_zero {x : X} {d : ℤ} :
    d ∈ reachableExponents T C E 0 x ↔ d = 0 ∧ x ∈ C := by
  simp only [reachableExponents, Finset.mem_filter, Finset.mem_singleton]
  refine and_congr_right fun hd => ?_
  rw [hd, zpow_zero, Homeomorph.one_apply]

theorem mem_reachableExponents_succ {r : ℕ} {x : X} {d : ℤ} :
    d ∈ reachableExponents T C E (r + 1) x ↔
      (d ∈ reachableExponents T C E r x ∨
        ∃ a ∈ reachableExponents T C E r x, ∃ e ∈ stepExponents E, a + e = d) ∧
        (T ^ d) x ∈ C := by
  simp only [reachableExponents, Finset.mem_filter, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_image]

theorem zpow_mem_of_mem_reachableExponents {r : ℕ} {x : X} {d : ℤ}
    (hd : d ∈ reachableExponents T C E r x) : (T ^ d) x ∈ C := by
  cases r with
  | zero =>
    obtain ⟨rfl, hx⟩ := mem_reachableExponents_zero.mp hd
    rwa [zpow_zero, Homeomorph.one_apply]
  | succ r => exact (mem_reachableExponents_succ.mp hd).2

theorem zero_mem_reachableExponents {r : ℕ} {x : X} (hx : x ∈ C) :
    (0 : ℤ) ∈ reachableExponents T C E r x := by
  induction r with
  | zero => exact mem_reachableExponents_zero.mpr ⟨rfl, hx⟩
  | succ r ih =>
    refine mem_reachableExponents_succ.mpr ⟨Or.inl ih, ?_⟩
    rwa [zpow_zero, Homeomorph.one_apply]

theorem reachableExponents_subset_succ (r : ℕ) (x : X) :
    reachableExponents T C E r x ⊆ reachableExponents T C E (r + 1) x := fun _ hd =>
  mem_reachableExponents_succ.mpr ⟨Or.inl hd, zpow_mem_of_mem_reachableExponents hd⟩

theorem reachableExponents_mono {r s : ℕ} (hrs : r ≤ s) (x : X) :
    reachableExponents T C E r x ⊆ reachableExponents T C E s x := by
  induction s, hrs using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ s _ ih => exact Finset.Subset.trans ih (reachableExponents_subset_succ s x)

/-- **Classes have at most `m` exponents** (tex 1495–1496). -/
theorem card_reachableExponents_le (hm : ExponentBound T C m) (r : ℕ) (x : X) :
    (reachableExponents T C E r x).card ≤ m :=
  hm x _ fun _ hd => zpow_mem_of_mem_reachableExponents hd

theorem eventually_zpow_mem_iff (hC : IsClopen C) (d : ℤ) (x : X) :
    ∀ᶠ y in 𝓝 x, ((T ^ d) y ∈ C ↔ (T ^ d) x ∈ C) := by
  have hpre : IsClopen ((T ^ d) ⁻¹' C) := hC.preimage (T ^ d).continuous
  by_cases hx : (T ^ d) x ∈ C
  · have hx' : x ∈ (T ^ d) ⁻¹' C := hx
    filter_upwards [hpre.2.mem_nhds hx'] with y hy
    exact ⟨fun _ => hx, fun _ => hy⟩
  · have hx' : x ∈ ((T ^ d) ⁻¹' C)ᶜ := hx
    filter_upwards [hpre.1.isOpen_compl.mem_nhds hx'] with y hy
    exact ⟨fun h => (hy h).elim, fun h => (hx h).elim⟩

/-- **The generated relation is given by clopen data** (tex 1499–1500): for clopen `C` every
`reachableExponents T C E r` is locally constant. -/
theorem isLocallyConstant_reachableExponents (hC : IsClopen C) (r : ℕ) :
    IsLocallyConstant (reachableExponents T C E r) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  induction r with
  | zero =>
    filter_upwards [eventually_zpow_mem_iff (T := T) hC 0 x] with y hy
    simp only [zpow_zero, Homeomorph.one_apply] at hy
    ext d
    rw [mem_reachableExponents_zero, mem_reachableExponents_zero]
    exact and_congr_right fun _ => hy
  | succ r ih =>
    have hB : ∀ᶠ y in 𝓝 x, ∀ d ∈ reachableExponents T C E r x ∪
        ((reachableExponents T C E r x).biUnion fun a => (stepExponents E).image (a + ·)),
        ((T ^ d) y ∈ C ↔ (T ^ d) x ∈ C) :=
      (Filter.eventually_all_finset _).2 fun d _ => eventually_zpow_mem_iff (T := T) hC d x
    filter_upwards [ih, hB] with y hy hyB
    ext d
    rw [mem_reachableExponents_succ, mem_reachableExponents_succ, hy]
    refine and_congr_right fun h => hyB d ?_
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
    exact h

theorem isClopen_setOf_reachableExponents_eq (hC : IsClopen C) (r : ℕ) (S : Finset ℤ) :
    IsClopen {x | reachableExponents T C E r x = S} :=
  (isLocallyConstant_reachableExponents hC r).isClopen_fiber S

/-- **The representative set is clopen** (tex 1506–1507). -/
theorem isClopen_baseSet (hC : IsClopen C) : IsClopen (baseSet T C E m) := by
  have h := ((isLocallyConstant_reachableExponents (T := T) (E := E) hC (m - 1)).comp
    fun S : Finset ℤ => ∀ d ∈ S, 0 ≤ d).isClopen_fiber True
  have hset : {x | ∀ d ∈ reachableExponents T C E (m - 1) x, 0 ≤ d} =
      {x | ((fun S : Finset ℤ => ∀ d ∈ S, 0 ≤ d) ∘ reachableExponents T C E (m - 1)) x = True} :=
    Set.ext fun _ => ⟨eq_true, of_eq_true⟩
  show IsClopen (C ∩ {x | ∀ d ∈ reachableExponents T C E (m - 1) x, 0 ≤ d})
  rw [hset]
  exact hC.inter h

theorem isClopen_baseCell (hC : IsClopen C) (S : Finset ℤ) : IsClopen (baseCell T C E m S) :=
  (isClopen_baseSet hC).inter (isClopen_setOf_reachableExponents_eq hC (m - 1) S)

/-- **The levels are clopen** (tex 1510–1511). -/
theorem isClopen_level (hC : IsClopen C) (S : Finset ℤ) (d : ℤ) :
    IsClopen (level T C E m S d) :=
  (isClopen_baseCell hC S).preimage (T ^ (-d)).continuous

theorem mem_level_iff {S : Finset ℤ} {d : ℤ} {z : X} :
    z ∈ level T C E m S d ↔ ∃ x ∈ baseCell T C E m S, (T ^ d) x = z := by
  constructor
  · intro hz
    refine ⟨(T ^ (-d)) z, hz, ?_⟩
    rw [← Homeomorph.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Homeomorph.one_apply]
  · rintro ⟨x, hx, rfl⟩
    show (T ^ (-d)) ((T ^ d) x) ∈ baseCell T C E m S
    rw [← Homeomorph.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, Homeomorph.one_apply]
    exact hx

section Models

/-- The model partial shift: `x ↦ x + 1` on `ℤ`. -/
def modelShift : ℤ ≃ₜ ℤ where
  toFun x := x + 1
  invFun x := x - 1
  left_inv x := by show x + 1 - 1 = x; omega
  right_inv x := by show x - 1 + 1 = x; omega
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

theorem modelShift_zpow_apply (n x : ℤ) : (modelShift ^ n) x = x + n := by
  induction n using Int.induction_on generalizing x with
  | zero => simp only [zpow_zero, Homeomorph.one_apply, add_zero]
  | succ i ih =>
    rw [zpow_add_one, Homeomorph.mul_apply, ih]
    show x + 1 + (i : ℤ) = x + ((i : ℤ) + 1)
    omega
  | pred i ih =>
    rw [zpow_sub_one, Homeomorph.mul_apply, ih]
    show x - 1 + -(i : ℤ) = x + (-(i : ℤ) - 1)
    omega

/-- **Positive model test of `ExponentBound`**: the orbit of `x` meets `[0, 1]` at the exponents
`-x` and `1 - x` only. -/
theorem exponentBound_modelShift : ExponentBound modelShift (Set.Icc 0 1) 2 := by
  intro x S hS
  have hsub : S ⊆ {-x, 1 - x} := by
    intro n hn
    have h := hS n hn
    rw [modelShift_zpow_apply, Set.mem_Icc] at h
    rw [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem modelShift_mem_reachableExponents_one {x d : ℤ} :
    d ∈ reachableExponents modelShift (Set.Icc 0 1) {1} 1 x ↔
      (0 ≤ x ∧ x ≤ 1) ∧ (d = -1 ∨ d = 0 ∨ d = 1) ∧ 0 ≤ x + d ∧ x + d ≤ 1 := by
  refine (mem_reachableExponents_succ (r := 0)).trans ?_
  rw [modelShift_zpow_apply]
  constructor
  · rintro ⟨h | ⟨a, ha, e, he, rfl⟩, hxd⟩
    · obtain ⟨rfl, hx⟩ := mem_reachableExponents_zero.mp h
      exact ⟨hx, by omega, hxd⟩
    · obtain ⟨rfl, hx⟩ := mem_reachableExponents_zero.mp ha
      rw [mem_stepExponents, Finset.mem_singleton, Finset.mem_singleton] at he
      exact ⟨hx, by omega, hxd⟩
  · rintro ⟨hx, hd, hxd⟩
    refine ⟨?_, hxd⟩
    have h0 : (0 : ℤ) ∈ reachableExponents modelShift (Set.Icc 0 1) {1} 0 x :=
      mem_reachableExponents_zero.mpr ⟨rfl, hx⟩
    rcases hd with rfl | rfl | rfl
    · have he : (-1 : ℤ) ∈ stepExponents {1} :=
        mem_stepExponents.mpr (Or.inr (Finset.mem_singleton.mpr (by omega)))
      exact Or.inr ⟨0, h0, -1, he, by omega⟩
    · exact Or.inl h0
    · have he : (1 : ℤ) ∈ stepExponents {1} :=
        mem_stepExponents.mpr (Or.inl (Finset.mem_singleton_self 1))
      exact Or.inr ⟨0, h0, 1, he, by omega⟩

theorem modelShift_reachableExponents_one_zero :
    reachableExponents modelShift (Set.Icc 0 1) {1} 1 0 = {0, 1} := by
  ext d
  rw [modelShift_mem_reachableExponents_one, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    omega
  · intro h
    omega

theorem modelShift_reachableExponents_one_one :
    reachableExponents modelShift (Set.Icc 0 1) {1} 1 1 = {-1, 0} := by
  ext d
  rw [modelShift_mem_reachableExponents_one, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    omega
  · intro h
    omega

/-- **Model test of the base cell**: the class `{0, 1}` is represented by `0` alone. -/
theorem modelShift_baseCell : baseCell modelShift (Set.Icc 0 1) {1} 2 {0, 1} = {0} := by
  ext x
  constructor
  · rintro ⟨-, hD⟩
    have hD' : reachableExponents modelShift (Set.Icc 0 1) {1} (2 - 1) x = {0, 1} := hD
    have h1 : (1 : ℤ) ∈ reachableExponents modelShift (Set.Icc 0 1) {1} (2 - 1) x := by
      rw [hD']
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 1)
    have h := modelShift_mem_reachableExponents_one.mp h1
    exact Set.mem_singleton_iff.mpr (by omega)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨⟨Set.mem_Icc.mpr ⟨by omega, by omega⟩, fun d hd => ?_⟩,
      modelShift_reachableExponents_one_zero⟩
    have h := modelShift_mem_reachableExponents_one.mp hd
    omega

/-- **Model test of the levels**: the class `{0, 1}` has the levels `{0}` and `{1}`. -/
theorem modelShift_level_zero : level modelShift (Set.Icc 0 1) {1} 2 {0, 1} 0 = {0} := by
  ext z
  show (modelShift ^ (-0 : ℤ)) z ∈ baseCell modelShift (Set.Icc 0 1) {1} 2 {0, 1} ↔
    z ∈ ({0} : Set ℤ)
  rw [modelShift_baseCell, Set.mem_singleton_iff, Set.mem_singleton_iff, modelShift_zpow_apply]
  constructor
  · intro h
    omega
  · intro h
    omega

theorem modelShift_level_one : level modelShift (Set.Icc 0 1) {1} 2 {0, 1} 1 = {1} := by
  ext z
  show (modelShift ^ (-1 : ℤ)) z ∈ baseCell modelShift (Set.Icc 0 1) {1} 2 {0, 1} ↔
    z ∈ ({1} : Set ℤ)
  rw [modelShift_baseCell, Set.mem_singleton_iff, Set.mem_singleton_iff, modelShift_zpow_apply]
  constructor
  · intro h
    omega
  · intro h
    omega

/-- The swap of `Bool`, whose points are periodic. -/
def modelSwap : Bool ≃ₜ Bool where
  toFun := not
  invFun := not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

theorem modelSwap_sq : modelSwap ^ (2 : ℤ) = 1 := by
  rw [zpow_two]
  ext b
  cases b <;> rfl

/-- **Negative model test of `ExponentBound`**: a periodic point in `C` violates it for every `m`. -/
theorem not_exponentBound_modelSwap (m : ℕ) : ¬ ExponentBound modelSwap {true} m := by
  intro h
  have hinj : Function.Injective fun n : ℕ => 2 * (n : ℤ) := fun a b hab => by
    have h2 : 2 * (a : ℤ) = 2 * (b : ℤ) := hab
    omega
  have hS := h true ((Finset.range (m + 1)).image fun n : ℕ => 2 * (n : ℤ)) (by
    intro d hd
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hd
    rw [zpow_mul, modelSwap_sq, one_zpow, Homeomorph.one_apply]
    exact Set.mem_singleton true)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at hS
  omega

end Models

#audit_axioms GroupApproximation.ChainCore.mem_stepExponents
#audit_axioms GroupApproximation.ChainCore.mem_reachableExponents_succ
#audit_axioms GroupApproximation.ChainCore.reachableExponents_mono
#audit_axioms GroupApproximation.ChainCore.card_reachableExponents_le
#audit_axioms GroupApproximation.ChainCore.isLocallyConstant_reachableExponents
#audit_axioms GroupApproximation.ChainCore.isClopen_setOf_reachableExponents_eq
#audit_axioms GroupApproximation.ChainCore.isClopen_baseSet
#audit_axioms GroupApproximation.ChainCore.isClopen_baseCell
#audit_axioms GroupApproximation.ChainCore.isClopen_level
#audit_axioms GroupApproximation.ChainCore.mem_level_iff
#audit_axioms GroupApproximation.ChainCore.exponentBound_modelShift
#audit_axioms GroupApproximation.ChainCore.modelShift_baseCell
#audit_axioms GroupApproximation.ChainCore.modelShift_level_zero
#audit_axioms GroupApproximation.ChainCore.modelShift_level_one
#audit_axioms GroupApproximation.ChainCore.not_exponentBound_modelSwap

end GroupApproximation.ChainCore
