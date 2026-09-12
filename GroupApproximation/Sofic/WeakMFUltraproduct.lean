import GroupApproximation.Sofic.NormTraceGap
import GroupApproximation.Sofic.SoficUltraproduct
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Weak-MF approximations and their operator-norm ultraproduct

This file supplies the first analytic layer of the Kazhdan-corner argument.
The local operator-norm models of `IsNormApproximable` are assembled, for a
countable group, into one sequential approximation.  Its pointwise unitary
maps then induce an injective homomorphism into the quotient of the product of
matrix unitary groups by operator-norm-null sequences.

Unlike the Hilbert--Schmidt ultraproduct, no amplification theorem is needed:
the fixed separation constant in the definition of weak-MF directly prevents
distinct elements from becoming equal in the quotient.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-! ## The local weak-MF predicate -/

/-- Weak-MF in the operator-norm sense: finite unitary models have a fixed
positive operator-norm separation and arbitrarily small multiplicative
defect. -/
def IsWeakMF (G : Type u) [Group G] : Prop :=
  ∃ delta : ℝ, 0 < delta ∧ IsNormApproximable G delta

/-- Positive control: every finite group is weak-MF, using its regular
representation. -/
theorem isWeakMF_of_finite (G : Type) [Group G] [Finite G] : IsWeakMF G :=
  ⟨1, by norm_num, isNormApproximable_of_finite G⟩

/-! ## Sequential weak-MF models -/

/-- A sequence of operator-norm unitary models with a single positive
separation constant. -/
structure WeakMFApproximation (G : Type u) [Group G] where
  separation : ℝ
  separation_pos : 0 < separation
  model : ℕ → FiniteModel
  modelNonempty : ∀ n, 0 < Fintype.card (model n)
  map : ∀ n, G → Matrix.unitaryGroup (model n) ℂ
  asymptoticallyMultiplicative : ∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    ‖(map n (g * h) : Matrix (model n) (model n) ℂ) -
        (map n g : Matrix (model n) (model n) ℂ) * map n h‖ ≤ ε
  separatedEventually : ∀ g h : G, g ≠ h → ∃ N, ∀ n ≥ N,
    separation ≤ ‖(map n g : Matrix (model n) (model n) ℂ) - map n h‖

namespace WeakMFApproximation

/-- Pull a sequential weak-MF approximation back along an injective
homomorphism.  The finite matrix models are unchanged; only the group
elements fed to the maps are restricted. -/
abbrev comap {H : Type*} [Group H] (A : WeakMFApproximation G)
    (ι : H →* G) (hι : Function.Injective ι) : WeakMFApproximation H where
  separation := A.separation
  separation_pos := A.separation_pos
  model := A.model
  modelNonempty := A.modelNonempty
  map n h := A.map n (ι h)
  asymptoticallyMultiplicative g h ε hε := by
    simpa only [map_mul] using A.asymptoticallyMultiplicative (ι g) (ι h) ε hε
  separatedEventually g h hne :=
    A.separatedEventually (ι g) (ι h) (hι.ne hne)

@[simp] theorem comap_model {H : Type*} [Group H]
    (A : WeakMFApproximation G) (ι : H →* G) (hι : Function.Injective ι)
    (n : ℕ) : (A.comap ι hι).model n = A.model n := rfl

@[simp] theorem comap_map {H : Type*} [Group H]
    (A : WeakMFApproximation G) (ι : H →* G) (hι : Function.Injective ι)
    (n : ℕ) (h : H) : (A.comap ι hι).map n h = A.map n (ι h) := rfl

/-- Reindex a weak-MF approximation along a pointwise cofinal map.  The
inequality `n ≤ φ n` is exactly what is needed to preserve all eventual
operator-norm estimates. -/
def reindex (A : WeakMFApproximation G) (φ : ℕ → ℕ)
    (hφ : ∀ n, n ≤ φ n) : WeakMFApproximation G where
  separation := A.separation
  separation_pos := A.separation_pos
  model n := A.model (φ n)
  modelNonempty n := A.modelNonempty (φ n)
  map n := A.map (φ n)
  asymptoticallyMultiplicative g h ε hε := by
    obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h ε hε
    exact ⟨N, fun n hn ↦ hN (φ n) (hn.trans (hφ n))⟩
  separatedEventually g h hgh := by
    obtain ⟨N, hN⟩ := A.separatedEventually g h hgh
    exact ⟨N, fun n hn ↦ hN (φ n) (hn.trans (hφ n))⟩

@[simp] theorem reindex_model (A : WeakMFApproximation G) (φ : ℕ → ℕ)
    (hφ : ∀ n, n ≤ φ n) (n : ℕ) :
    (A.reindex φ hφ).model n = A.model (φ n) := rfl

@[simp] theorem reindex_map (A : WeakMFApproximation G) (φ : ℕ → ℕ)
    (hφ : ∀ n, n ≤ φ n) (n : ℕ) :
    (A.reindex φ hφ).map n = A.map (φ n) := rfl

end WeakMFApproximation

/-- The one-point exact models form a closed sequential weak-MF
approximation of the trivial group. -/
noncomputable def trivialWeakMFApproximation : WeakMFApproximation PUnit where
  separation := 1
  separation_pos := by norm_num
  model := fun _ ↦ ⟨PUnit, inferInstance, inferInstance⟩
  modelNonempty := fun _ ↦ by simp
  map := fun _ _ ↦ 1
  asymptoticallyMultiplicative := by
    intro g h ε hε
    refine ⟨0, fun n _ ↦ ?_⟩
    show ‖(1 : Matrix _ _ ℂ) - 1 * 1‖ ≤ ε
    simp [hε.le]
  separatedEventually := by
    intro g h hne
    exact absurd (Subsingleton.elim g h) hne

/-- Local weak-MF models assemble into one sequential approximation for a
countable group. -/
theorem exists_weakMFApproximation [Countable G]
    {delta : ℝ} (hdelta : 0 < delta) (hMF : IsNormApproximable G delta) :
    Nonempty (WeakMFApproximation G) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let F : ℕ → Finset G := fun n ↦ insert 1 ((Finset.range (n + 1)).image e)
  have hFmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := by
    intro m n hmn
    refine Finset.insert_subset_insert _ (Finset.image_subset_image ?_)
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hFmem : ∀ g : G, ∃ N, ∀ n ≥ N, g ∈ F n := by
    intro g
    obtain ⟨i, hi⟩ := he g
    refine ⟨i, fun n hn ↦ hFmono hn ?_⟩
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i, Finset.self_mem_range_succ i, hi⟩)
  have heps : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n ↦ by positivity
  let M : ∀ n : ℕ, NormModel G (F n) delta (1 / (n + 1)) :=
    fun n ↦ (hMF (F n) (1 / (n + 1)) (heps n)).some
  refine ⟨{
    separation := delta
    separation_pos := hdelta
    model := fun n ↦ (M n).carrier
    modelNonempty := fun n ↦ (M n).nonempty
    map := fun n g ↦ ⟨(M n).map g, (M n).isUnitary g⟩
    asymptoticallyMultiplicative := ?_
    separatedEventually := ?_ }⟩
  · intro g h ε hε
    obtain ⟨Ng, hNg⟩ := hFmem g
    obtain ⟨Nh, hNh⟩ := hFmem h
    obtain ⟨Ne, hNe⟩ := exists_nat_gt (1 / ε)
    refine ⟨max (max Ng Nh) Ne, fun n hn ↦ ?_⟩
    have hg : g ∈ F n := hNg n
      (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn)
    have hh : h ∈ F n := hNh n
      (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
    have hsmall : 1 / ((n : ℝ) + 1) ≤ ε := by
      have hNen : (Ne : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast le_trans (le_max_right _ _) hn
      have : (1 : ℝ) / ε < (n : ℝ) + 1 := by linarith
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at this
      linarith
    exact (M n).multiplicative g hg h hh |>.trans hsmall
  · intro g h hne
    obtain ⟨Ng, hNg⟩ := hFmem g
    obtain ⟨Nh, hNh⟩ := hFmem h
    refine ⟨max Ng Nh, fun n hn ↦ ?_⟩
    exact (M n).separated g (hNg n ((le_max_left _ _).trans hn))
      h (hNh n ((le_max_right _ _).trans hn)) hne

/-! ## Operator-norm length -/

/-- Operator-norm displacement of a unitary from the identity. -/
noncomputable def opLength (Y : FiniteModel)
    (u : Matrix.unitaryGroup Y ℂ) : ℝ :=
  ‖(u : Matrix Y Y ℂ) - 1‖

@[simp] theorem opLength_one (Y : FiniteModel) :
    opLength Y 1 = 0 := by
  simp [opLength]

theorem opLength_nonneg (Y : FiniteModel) (u : Matrix.unitaryGroup Y ℂ) :
    0 ≤ opLength Y u := norm_nonneg _

/-- The length of a product is at most the sum of the lengths. -/
theorem opLength_mul_le (Y : FiniteModel)
    (u v : Matrix.unitaryGroup Y ℂ) :
    opLength Y (u * v) ≤ opLength Y u + opLength Y v := by
  have hsplit :
      ((u * v : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) - 1 =
        (u : Matrix Y Y ℂ) * ((v : Matrix Y Y ℂ) - 1) +
          ((u : Matrix Y Y ℂ) - 1) := by
    change (u : Matrix Y Y ℂ) * (v : Matrix Y Y ℂ) - 1 = _
    rw [Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [opLength, hsplit, opLength, opLength]
  calc
    ‖(u : Matrix Y Y ℂ) * ((v : Matrix Y Y ℂ) - 1) +
        ((u : Matrix Y Y ℂ) - 1)‖ ≤
        ‖(u : Matrix Y Y ℂ) * ((v : Matrix Y Y ℂ) - 1)‖ +
          ‖(u : Matrix Y Y ℂ) - 1‖ := norm_add_le _ _
    _ = ‖(v : Matrix Y Y ℂ) - 1‖ + ‖(u : Matrix Y Y ℂ) - 1‖ := by
      rw [CStarRing.norm_mem_unitary_mul _ u.2]
    _ = ‖(u : Matrix Y Y ℂ) - 1‖ + ‖(v : Matrix Y Y ℂ) - 1‖ :=
      add_comm _ _

/-- Inversion does not change operator-norm length. -/
theorem opLength_inv (Y : FiniteModel) (u : Matrix.unitaryGroup Y ℂ) :
    opLength Y u⁻¹ = opLength Y u := by
  have hcoe : ((u⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) =
      (u : Matrix Y Y ℂ)ᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    rfl
  rw [opLength, opLength, hcoe]
  have hstar : (u : Matrix Y Y ℂ)ᴴ - 1 =
      ((u : Matrix Y Y ℂ) - 1)ᴴ := by simp
  rw [hstar, ← Matrix.star_eq_conjTranspose, norm_star]

/-- Conjugation does not change operator-norm length. -/
theorem opLength_conj (Y : FiniteModel)
    (t u : Matrix.unitaryGroup Y ℂ) :
    opLength Y (t * u * t⁻¹) = opLength Y u := by
  have htinv : (((t⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ))
      ∈ Matrix.unitaryGroup Y ℂ := (t⁻¹).2
  have hsplit :
      ((t * u * t⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) - 1 =
        (t : Matrix Y Y ℂ) * ((u : Matrix Y Y ℂ) - 1) *
          ((t⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) := by
    have hcancel : (t : Matrix Y Y ℂ) *
        ((t⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) = 1 := by
      exact congrArg Subtype.val (mul_inv_cancel t)
    change (t : Matrix Y Y ℂ) * (u : Matrix Y Y ℂ) *
      ((t⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) - 1 = _
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hcancel]
  rw [opLength, opLength, hsplit, CStarRing.norm_mul_mem_unitary _ htinv,
    CStarRing.norm_mem_unitary_mul _ t.2]

/-- The identity converting quotient length to operator-norm distance. -/
theorem opLength_inv_mul (Y : FiniteModel)
    (a b : Matrix.unitaryGroup Y ℂ) :
    opLength Y (a⁻¹ * b) =
      ‖(b : Matrix Y Y ℂ) - (a : Matrix Y Y ℂ)‖ := by
  have hainv : (((a⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ))
      ∈ Matrix.unitaryGroup Y ℂ := (a⁻¹).2
  have hsplit :
      ((a⁻¹ * b : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) - 1 =
        ((a⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) *
          ((b : Matrix Y Y ℂ) - (a : Matrix Y Y ℂ)) := by
    have hcancel : (((a⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)) *
        (a : Matrix Y Y ℂ) = 1 := by
      exact congrArg Subtype.val (inv_mul_cancel a)
    change ((a⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) *
      (b : Matrix Y Y ℂ) - 1 = _
    rw [Matrix.mul_sub, hcancel]
  rw [opLength, hsplit, CStarRing.norm_mem_unitary_mul _ hainv]

/-! ## The norm ultraproduct -/

variable {ι : Type*} (𝒰 : Ultrafilter ι) (X : ι → FiniteModel)

/-- Sequences of unitaries converging to the identity in operator norm. -/
def IsNullOpSeq (u : ∀ i, Matrix.unitaryGroup (X i) ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (𝒰 : Filter ι), opLength (X i) (u i) < ε

theorem isNullOpSeq_one : IsNullOpSeq 𝒰 X 1 := by
  intro ε hε
  filter_upwards with i
  simpa using hε

/-- Operator-norm-null sequences form a subgroup of the product. -/
def nullOpSubgroup : Subgroup (∀ i, Matrix.unitaryGroup (X i) ℂ) where
  carrier := {u | IsNullOpSeq 𝒰 X u}
  one_mem' := isNullOpSeq_one 𝒰 X
  mul_mem' := by
    intro u v hu hv ε hε
    filter_upwards [hu (ε / 2) (by linarith), hv (ε / 2) (by linarith)]
      with i hi hv
    exact (opLength_mul_le (X i) (u i) (v i)).trans_lt (by linarith)
  inv_mem' := by
    intro u hu ε hε
    filter_upwards [hu ε hε] with i hi
    change opLength (X i) (u i)⁻¹ < ε
    rwa [opLength_inv]

instance nullOpSubgroup_normal : (nullOpSubgroup 𝒰 X).Normal where
  conj_mem := by
    intro u hu t ε hε
    filter_upwards [hu ε hε] with i hi
    change opLength (X i) (t i * u i * (t i)⁻¹) < ε
    rwa [opLength_conj]

/-- The operator-norm matrix ultraproduct unitary group. -/
abbrev UniversalWeakMF : Type _ :=
  (∀ i, Matrix.unitaryGroup (X i) ℂ) ⧸ nullOpSubgroup 𝒰 X

/-! ## A sequential weak-MF approximation is a faithful representation -/

/-- The maps of a sequential weak-MF approximation induce an injective
homomorphism into its operator-norm ultraproduct. -/
theorem WeakMFApproximation.exists_normUltraproductEmbedding
    (A : WeakMFApproximation G) {𝒰 : Ultrafilter ℕ}
    (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    ∃ ρ : G →* UniversalWeakMF 𝒰 A.model, Function.Injective ρ := by
  have hnull : ∀ g h : G,
      (fun n ↦ A.map n g * A.map n h)⁻¹ * (fun n ↦ A.map n (g * h))
        ∈ nullOpSubgroup 𝒰 A.model := by
    intro g h ε hε
    obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h (ε / 2) (by linarith)
    refine eventually_of_atTop hcof N (fun n hn ↦ ?_)
    change opLength (A.model n)
      ((A.map n g * A.map n h)⁻¹ * A.map n (g * h)) < ε
    rw [opLength_inv_mul]
    exact (hN n hn).trans_lt (by linarith)
  refine ⟨MonoidHom.mk' (fun g ↦ QuotientGroup.mk (fun n ↦ A.map n g)) ?_, ?_⟩
  · intro g h
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq.mpr (hnull g h)).symm
  · intro g h hgh
    by_contra hne
    obtain ⟨N, hN⟩ := A.separatedEventually g h hne
    have hfar : ∀ᶠ n in (𝒰 : Filter ℕ),
        A.separation ≤ ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) - A.map n h‖ :=
      eventually_of_atTop hcof N hN
    have hmem : (fun n ↦ A.map n h)⁻¹ * (fun n ↦ A.map n g)
        ∈ nullOpSubgroup 𝒰 A.model := QuotientGroup.eq.mp hgh.symm
    have hclose : ∀ᶠ n in (𝒰 : Filter ℕ),
        ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) - A.map n h‖ <
          A.separation := by
      filter_upwards [hmem A.separation A.separation_pos] with n hn
      change opLength (A.model n) ((A.map n h)⁻¹ * A.map n g) <
        A.separation at hn
      rwa [opLength_inv_mul] at hn
    obtain ⟨n, hn₁, hn₂⟩ := (hfar.and hclose).exists
    exact (not_lt_of_ge hn₁) hn₂

/-- Weak-MF gives a faithful representation in an operator-norm matrix
ultraproduct. -/
theorem exists_normUltraproductEmbedding_of_isWeakMF [Countable G]
    (hMF : IsWeakMF G) :
    ∃ (A : WeakMFApproximation G)
      (ρ : G →* UniversalWeakMF (Ultrafilter.of Filter.cofinite) A.model),
      Function.Injective ρ := by
  obtain ⟨delta, hdelta, hMF⟩ := hMF
  obtain ⟨A⟩ := exists_weakMFApproximation hdelta hMF
  have hcof : (((Ultrafilter.of Filter.cofinite : Ultrafilter ℕ) : Filter ℕ)
      ≤ Filter.cofinite) := Ultrafilter.of_le _
  obtain ⟨ρ, hρ⟩ := A.exists_normUltraproductEmbedding hcof
  exact ⟨A, ρ, hρ⟩

end GroupApproximation
