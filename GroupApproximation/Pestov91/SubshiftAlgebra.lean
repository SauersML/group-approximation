import GroupApproximation.Pestov91.SubshiftMinimal
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Locally constant functions on the Toeplitz subshift

A locally constant function on `X` depends only on finitely many coordinates. The shift acts on
`LocallyConstant X K` by algebra automorphisms, translating coordinate functions, and the
coordinate functions generate `LocallyConstant X K` as a `K`-algebra.
-/

namespace GroupApproximation.Pestov91

theorem isLocallyConstant_of_depends {Y : Type*} {g : X → Y} (s : Finset ℤ)
    (hg : ∀ y z : X, (∀ i ∈ s, y.1 i = z.1 i) → g y = g z) : IsLocallyConstant g := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y
  exact ⟨cyl s y, isOpen_cyl s y, mem_cyl_self s y, fun z hz => hg z y hz⟩

/-- A locally constant function on `X` depends on finitely many coordinates. -/
theorem exists_finset_depends {Y : Type*} (f : LocallyConstant X Y) :
    ∃ s : Finset ℤ, ∀ y z : X, (∀ i ∈ s, y.1 i = z.1 i) → f y = f z := by
  have h : ∀ y : X, ∃ s : Finset ℤ, cyl s y ⊆ {z | f z = f y} := fun y =>
    exists_cyl_subset (f.isLocallyConstant.isOpen_fiber (f y)) rfl
  choose I hI using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => cyl (I y) y)
    (fun y => isOpen_cyl (I y) y) (fun y _ => Set.mem_iUnion.mpr ⟨y, mem_cyl_self _ y⟩)
  refine ⟨t.biUnion I, fun y z hyz => ?_⟩
  obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  have hzw : z ∈ cyl (I w) w := fun i hi =>
    (hyz i (Finset.mem_biUnion.mpr ⟨w, hw, hi⟩)).symm.trans (hyw i hi)
  have h1 : f y = f w := hI w hyw
  have h2 : f z = f w := hI w hzw
  exact h1.trans h2.symm

/-- The radius form of `exists_finset_depends`. -/
theorem exists_radius {Y : Type*} (f : LocallyConstant X Y) :
    ∃ r : ℕ, ∀ y z : X, (∀ k : ℤ, |k| ≤ r → y.1 k = z.1 k) → f y = f z := by
  obtain ⟨s, hs⟩ := exists_finset_depends f
  refine ⟨s.sup Int.natAbs, fun y z hyz => hs y z fun i hi => hyz i ?_⟩
  have h := Finset.le_sup (f := Int.natAbs) hi
  rw [abs_le]
  constructor <;> omega

variable (K : Type*) [CommRing K]

/-- Translation by `n`: `translate K n f y = f (shiftBy (-n) y)`. -/
def translate (n : ℤ) : LocallyConstant X K ≃ₐ[K] LocallyConstant X K :=
  LocallyConstant.congrLeftₐ K (shiftBy n)

theorem translate_apply (n : ℤ) (f : LocallyConstant X K) (y : X) :
    translate K n f y = f (shiftBy (-n) y) := rfl

theorem translate_add (m n : ℤ) (f : LocallyConstant X K) :
    translate K (m + n) f = translate K m (translate K n f) := by
  ext y
  simp only [translate_apply, ← shiftBy_add]
  rw [show -(m + n) = -n + -m by ring]

theorem translate_zero (f : LocallyConstant X K) : translate K 0 f = f := by
  ext y
  simp only [translate_apply, neg_zero, shiftBy_zero]

/-- The coordinate function `y ↦ [y i = true]`. -/
def coord (i : ℤ) : LocallyConstant X K where
  toFun y := if y.1 i then 1 else 0
  isLocallyConstant := isLocallyConstant_of_depends {i} fun y z h => by
    simp only [h i (Finset.mem_singleton_self i)]

theorem coord_apply (i : ℤ) (y : X) : coord K i y = if y.1 i then 1 else 0 := rfl

theorem translate_coord (n i : ℤ) : translate K n (coord K i) = coord K (i - n) := by
  ext y
  exact congrArg (fun k : ℤ => if y.1 k then (1 : K) else 0) (by ring : -n + i = i - n)

theorem mem_adjoin_of_depends (s : Finset ℤ) :
    ∀ f : LocallyConstant X K, (∀ y z : X, (∀ i ∈ s, y.1 i = z.1 i) → f y = f z) →
      f ∈ Algebra.adjoin K (Set.range (coord K)) := by
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have e : f = f toeplitzPoint • 1 := by
      ext y
      show f y = f toeplitzPoint * 1
      rw [mul_one]
      exact hf y toeplitzPoint (by simp)
    rw [e]
    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) _
  | insert a s ha ih =>
    intro f hf
    classical
    let g : Bool → X → K := fun b y =>
      if h : ∃ z : X, (∀ i ∈ s, z.1 i = y.1 i) ∧ z.1 a = b then f h.choose else 0
    have hg : ∀ b, ∀ y z : X, (∀ i ∈ s, y.1 i = z.1 i) → g b y = g b z := by
      intro b y z hyz
      have hiff : (∃ w : X, (∀ i ∈ s, w.1 i = y.1 i) ∧ w.1 a = b) ↔
          ∃ w : X, (∀ i ∈ s, w.1 i = z.1 i) ∧ w.1 a = b := by
        constructor
        · rintro ⟨w, hw, hwa⟩
          exact ⟨w, fun i hi => (hw i hi).trans (hyz i hi), hwa⟩
        · rintro ⟨w, hw, hwa⟩
          exact ⟨w, fun i hi => (hw i hi).trans (hyz i hi).symm, hwa⟩
      simp only [g]
      by_cases hy : ∃ w : X, (∀ i ∈ s, w.1 i = y.1 i) ∧ w.1 a = b
      · have hz := hiff.mp hy
        rw [dif_pos hy, dif_pos hz]
        apply hf
        intro i hi
        rcases Finset.mem_insert.mp hi with h | hi
        · rw [h]
          exact hy.choose_spec.2.trans hz.choose_spec.2.symm
        · exact (hy.choose_spec.1 i hi).trans ((hyz i hi).trans (hz.choose_spec.1 i hi).symm)
      · have hz : ¬ ∃ w : X, (∀ i ∈ s, w.1 i = z.1 i) ∧ w.1 a = b := fun h => hy (hiff.mpr h)
        rw [dif_neg hy, dif_neg hz]
    let G : Bool → LocallyConstant X K := fun b => ⟨g b, isLocallyConstant_of_depends s (hg b)⟩
    have hG : ∀ b, G b ∈ Algebra.adjoin K (Set.range (coord K)) := fun b => ih (G b) (hg b)
    have hc : coord K a ∈ Algebra.adjoin K (Set.range (coord K)) :=
      Algebra.subset_adjoin ⟨a, rfl⟩
    have e : f = coord K a * G true + (1 - coord K a) * G false := by
      ext y
      have hy : ∃ w : X, (∀ i ∈ s, w.1 i = y.1 i) ∧ w.1 a = y.1 a := ⟨y, fun _ _ => rfl, rfl⟩
      have hval : G (y.1 a) y = f y := by
        show g (y.1 a) y = f y
        simp only [g]
        rw [dif_pos hy]
        apply hf
        intro i hi
        rcases Finset.mem_insert.mp hi with h | hi
        · rw [h]
          exact hy.choose_spec.2
        · exact hy.choose_spec.1 i hi
      rw [← hval]
      show _ = coord K a y * G true y + (1 - coord K a y) * G false y
      rw [coord_apply]
      cases y.1 a <;> simp
    rw [e]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hc (hG true))
      (Subalgebra.mul_mem _ (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hc) (hG false))

/-- The coordinate functions generate `LocallyConstant X K`. -/
theorem adjoin_range_coord : Algebra.adjoin K (Set.range (coord K)) = ⊤ := by
  rw [Algebra.eq_top_iff]
  intro f
  obtain ⟨s, hs⟩ := exists_finset_depends f
  exact mem_adjoin_of_depends K s f hs

end GroupApproximation.Pestov91
