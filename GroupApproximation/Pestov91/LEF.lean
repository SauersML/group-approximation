import GroupApproximation.Sofic.LEF
import GroupApproximation.Pestov91.Centre
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Fintype.Powerset

/-!
# LEF for `EL_ι(R)` modulo its centre

`IsLEF` does not pass to quotients in general
(`GroupApproximation.exists_isLEF_group_with_non_isLEF_quotient`). It does pass
to quotients by a **finite** normal subgroup, and the centre of `EL_ι(R)` is
finite whenever `R` has only finitely many central units, because central
elements of `EL_ι(R)` are scalars (`exists_central_unit_scalar_of_mem_center`).

* `isLEF_quotient_of_finite`: `IsLEF G → IsLEF (G ⧸ N)` for finite normal `N`.
  Lift a finite set of `G ⧸ N` to `G` and approximate the lift together with
  `N`. The image `K` of `N` is then a subgroup, the lifted elements normalize
  it, and the model is `N(K) ⧸ K`.
* `IsLEFRing`: every finite set maps into a finite ring, injectively, with
  sums and products of pairs preserved.
* `IsLEFRing.matrix` and `IsLEFRing.isLEF_units`, so `isLEF_elementaryGroup`.
* `isLEF_elementaryModCentre_of_finite` and
  `isLEF_elementaryModCentre_of_finite_centralUnits`.
-/

namespace GroupApproximation
namespace Pestov91

open scoped BigOperators

/-- LEF from multiplicative partial models into arbitrary finite groups. -/
theorem isLEF_of_forall_finite_model {G : Type*} [Group G]
    (h : ∀ s : Finset G, ∃ (H : Type) (_ : Group H) (_ : Finite H) (f : G → H),
      Set.InjOn f (s : Set G) ∧ ∀ x ∈ s, ∀ y ∈ s, f (x * y) = f x * f y) :
    IsLEF G := by
  classical
  refine (isLEF_iff_textbook G).2 fun s ↦ ?_
  obtain ⟨H, _, _, f, hinj, hmul⟩ := h s
  exact ⟨⟨H, inferInstance, Fintype.ofFinite H, Classical.decEq H⟩, f, hinj,
    fun x hx y hy _ ↦ hmul x hx y hy⟩

/-- **LEF passes to quotients by finite normal subgroups.** -/
theorem isLEF_quotient_of_finite {G : Type*} [Group G] (hG : IsLEF G)
    (N : Subgroup G) [N.Normal] [Finite N] : IsLEF (G ⧸ N) := by
  classical
  refine isLEF_of_forall_finite_model fun s ↦ ?_
  obtain ⟨o, ho⟩ : ∃ o : G ⧸ N → G, ∀ x, (o x : G ⧸ N) = x :=
    ⟨Quotient.out, QuotientGroup.out_eq'⟩
  obtain ⟨T, hZ, hs, hss, hsZ⟩ : ∃ T : Finset G, (∀ z ∈ N, z ∈ T) ∧ (∀ x ∈ s, o x ∈ T) ∧
      (∀ x ∈ s, ∀ y ∈ s, o x * o y ∈ T) ∧ (∀ x ∈ s, ∀ z ∈ N, o x * z ∈ T) := by
    haveI : Fintype N := Fintype.ofFinite N
    refine ⟨Finset.univ.image (Subtype.val : N → G) ∪ s.image o ∪
      (s.image o ×ˢ s.image o).image (fun p ↦ p.1 * p.2) ∪
      (s.image o ×ˢ Finset.univ.image (Subtype.val : N → G)).image (fun p ↦ p.1 * p.2),
      ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.2 ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩)))
    · intro x hx
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem o hx)))
    · intro x hx y hy
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨(o x, o y), Finset.mem_product.2
          ⟨Finset.mem_image_of_mem o hx, Finset.mem_image_of_mem o hy⟩, rfl⟩))
    · intro x hx z hz
      exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨(o x, z), Finset.mem_product.2
        ⟨Finset.mem_image_of_mem o hx, Finset.mem_image.2 ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩⟩,
        rfl⟩)
  obtain ⟨n, f, hinj, hmul⟩ := hG T
  obtain ⟨K, hKmem⟩ : ∃ K : Subgroup (Equiv.Perm (Fin n)),
      ∀ σ, σ ∈ K ↔ ∃ z : G, z ∈ N ∧ f z = σ := by
    let φ : N →* Equiv.Perm (Fin n) :=
      { toFun := fun z ↦ f z
        map_one' := hmul.map_one
        map_mul' := fun z w ↦ hmul.map_mul _ (hZ _ z.2) _ (hZ _ w.2) }
    refine ⟨φ.range, fun σ ↦ ?_⟩
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨NK, hNKmem, hKNK, _⟩ : ∃ NK : Subgroup (Equiv.Perm (Fin n)),
      (∀ g, g ∈ NK ↔ ∀ h, h ∈ K ↔ g * h * g⁻¹ ∈ K) ∧ K ≤ NK ∧ (K.subgroupOf NK).Normal :=
    ⟨Subgroup.normalizer (K : Set (Equiv.Perm (Fin n))), fun _ ↦ Subgroup.mem_normalizer_iff,
      Subgroup.le_normalizer, inferInstance⟩
  have hnorm : ∀ x ∈ s, f (o x) ∈ NK := by
    intro x hx
    rw [hNKmem]
    intro σ
    rw [hKmem, hKmem]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hc : o x * z * (o x)⁻¹ ∈ N := ‹N.Normal›.conj_mem z hz (o x)
      refine ⟨_, hc, ?_⟩
      have h1 : f (o x * z) = f (o x) * f z := hmul.map_mul _ (hs x hx) _ (hZ z hz)
      have h2 : f (o x * z * (o x)⁻¹ * o x) = f (o x * z * (o x)⁻¹) * f (o x) :=
        hmul.map_mul _ (hZ _ hc) _ (hs x hx)
      rw [inv_mul_cancel_right] at h2
      exact eq_mul_inv_of_mul_eq (h2.symm.trans h1)
    · rintro ⟨z', hz', hσ⟩
      have hz : (o x)⁻¹ * z' * o x ∈ N := by
        have := ‹N.Normal›.conj_mem z' hz' (o x)⁻¹
        rwa [inv_inv] at this
      refine ⟨_, hz, ?_⟩
      have h1 : f (o x * ((o x)⁻¹ * z' * o x)) = f (o x) * f ((o x)⁻¹ * z' * o x) :=
        hmul.map_mul _ (hs x hx) _ (hZ _ hz)
      have h2 : f (z' * o x) = f z' * f (o x) := hmul.map_mul _ (hZ _ hz') _ (hs x hx)
      have h3 : o x * ((o x)⁻¹ * z' * o x) = z' * o x := by simp [mul_assoc]
      rw [h3, h2, hσ, inv_mul_cancel_right] at h1
      exact (mul_left_cancel h1).symm
  obtain ⟨F, hF⟩ : ∃ F : G ⧸ N → ↥NK ⧸ K.subgroupOf NK,
      ∀ x, ∀ h : f (o x) ∈ NK, F x = (⟨f (o x), h⟩ : ↥NK) :=
    ⟨fun x ↦ if h : f (o x) ∈ NK then
      ((⟨f (o x), h⟩ : ↥NK) : ↥NK ⧸ K.subgroupOf NK) else 1,
      fun x h ↦ dif_pos h⟩
  refine ⟨↥NK ⧸ K.subgroupOf NK, inferInstance, inferInstance, F, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [hF x (hnorm x hx), hF y (hnorm y hy), QuotientGroup.eq, Subgroup.mem_subgroupOf,
      hKmem] at hxy
    obtain ⟨z, hz, hfz⟩ := hxy
    have h1 : f (o x * z) = f (o x) * f z := hmul.map_mul _ (hs x hx) _ (hZ z hz)
    have h2 : f (o y) = f (o x * z) := by
      rw [h1, hfz]
      simp
    have h3 : o y = o x * z := hinj (hs y hy) (hsZ x hx z hz) h2
    calc x = (o x : G ⧸ N) := (ho x).symm
      _ = (o y : G ⧸ N) := QuotientGroup.eq.2 (by rw [h3, inv_mul_cancel_left]; exact hz)
      _ = y := ho y
  · intro x hx y hy
    have hz : (o x * o y)⁻¹ * o (x * y) ∈ N := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_mul, ho, ho, ho]
    have h1 : f (o x * o y) = f (o x) * f (o y) := hmul.map_mul _ (hs x hx) _ (hs y hy)
    have h2 : f (o (x * y)) = f (o x * o y) * f ((o x * o y)⁻¹ * o (x * y)) := by
      rw [← hmul.map_mul _ (hss x hx y hy) _ (hZ _ hz), mul_inv_cancel_left]
    have hN' : f (o (x * y)) ∈ NK := by
      rw [h2, h1]
      exact NK.mul_mem (NK.mul_mem (hnorm x hx) (hnorm y hy))
        (hKNK ((hKmem _).2 ⟨_, hz, rfl⟩))
    rw [hF (x * y) hN', hF x (hnorm x hx), hF y (hnorm y hy), ← QuotientGroup.mk_mul]
    refine (QuotientGroup.eq.2 ?_).symm
    rw [Subgroup.mem_subgroupOf, hKmem]
    refine ⟨_, hz, ?_⟩
    show f _ = (f (o x) * f (o y))⁻¹ * f (o (x * y))
    rw [h2, h1, inv_mul_cancel_left]

/-- A ring is **LEF** if every finite subset maps into a finite ring injectively,
with `0`, `1`, and the sums and products of pairs from the subset preserved. -/
def IsLEFRing (A : Type*) [Ring A] : Prop :=
  ∀ t : Finset A, ∃ (F : Type) (_ : Ring F) (_ : Finite F) (φ : A → F),
    Set.InjOn φ (t : Set A) ∧ φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ a ∈ t, ∀ b ∈ t, φ (a + b) = φ a + φ b ∧ φ (a * b) = φ a * φ b

/-- Finite rings are LEF rings. -/
theorem isLEFRing_of_finite (A : Type) [Ring A] [Finite A] : IsLEFRing A :=
  fun _ ↦ ⟨A, inferInstance, inferInstance, id, fun _ _ _ _ h ↦ h, rfl, rfl,
    fun _ _ _ _ ↦ ⟨rfl, rfl⟩⟩

/-- The unit group of an LEF ring is LEF. -/
theorem IsLEFRing.isLEF_units {A : Type*} [Ring A] (hA : IsLEFRing A) : IsLEF Aˣ := by
  classical
  refine isLEF_of_forall_finite_model fun s ↦ ?_
  obtain ⟨t, hv, hi⟩ : ∃ t : Finset A, (∀ u ∈ s, (u : A) ∈ t) ∧
      ∀ u ∈ s, ((u⁻¹ : Aˣ) : A) ∈ t :=
    ⟨s.image (fun u : Aˣ ↦ (u : A)) ∪ s.image (fun u : Aˣ ↦ ((u⁻¹ : Aˣ) : A)),
      fun u hu ↦ Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu),
      fun u hu ↦ Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu)⟩
  obtain ⟨F, _, _, φ, hinj, -, h1, hφ⟩ := hA t
  have hunit : ∀ u ∈ s, φ u * φ ((u⁻¹ : Aˣ) : A) = 1 ∧ φ ((u⁻¹ : Aˣ) : A) * φ u = 1 :=
    fun u hu ↦ ⟨by rw [← (hφ _ (hv u hu) _ (hi u hu)).2, Units.mul_inv, h1],
      by rw [← (hφ _ (hi u hu) _ (hv u hu)).2, Units.inv_mul, h1]⟩
  obtain ⟨g, hg⟩ : ∃ g : Aˣ → Fˣ, ∀ (u : Aˣ) (_ : φ u * φ ((u⁻¹ : Aˣ) : A) = 1 ∧
      φ ((u⁻¹ : Aˣ) : A) * φ u = 1), (g u : F) = φ u :=
    ⟨fun u ↦ if h : φ u * φ ((u⁻¹ : Aˣ) : A) = 1 ∧ φ ((u⁻¹ : Aˣ) : A) * φ u = 1 then
      ⟨φ u, φ ((u⁻¹ : Aˣ) : A), h.1, h.2⟩ else 1,
      fun u h ↦ by simp only [dif_pos h]⟩
  refine ⟨Fˣ, inferInstance, inferInstance, g, ?_, ?_⟩
  · intro u hu v hv' huv
    exact Units.ext (hinj (hv u hu) (hv v hv') (by
      rw [← hg u (hunit u hu), ← hg v (hunit v hv'), huv]))
  · intro u hu v hv'
    have hmul : φ ((u * v : Aˣ) : A) = φ u * φ v := by
      rw [Units.val_mul]
      exact (hφ _ (hv u hu) _ (hv v hv')).2
    have hinv : φ (((u * v)⁻¹ : Aˣ) : A) = φ ((v⁻¹ : Aˣ) : A) * φ ((u⁻¹ : Aˣ) : A) := by
      rw [mul_inv_rev, Units.val_mul]
      exact (hφ _ (hi v hv') _ (hi u hu)).2
    have huv : φ ((u * v : Aˣ) : A) * φ (((u * v)⁻¹ : Aˣ) : A) = 1 ∧
        φ (((u * v)⁻¹ : Aˣ) : A) * φ ((u * v : Aˣ) : A) = 1 := by
      rw [hmul, hinv]
      refine ⟨?_, ?_⟩
      · calc φ u * φ v * (φ ((v⁻¹ : Aˣ) : A) * φ ((u⁻¹ : Aˣ) : A))
            = φ u * (φ v * φ ((v⁻¹ : Aˣ) : A)) * φ ((u⁻¹ : Aˣ) : A) := by
              simp only [mul_assoc]
          _ = 1 := by rw [(hunit v hv').1, mul_one, (hunit u hu).1]
      · calc φ ((v⁻¹ : Aˣ) : A) * φ ((u⁻¹ : Aˣ) : A) * (φ u * φ v)
            = φ ((v⁻¹ : Aˣ) : A) * (φ ((u⁻¹ : Aˣ) : A) * φ u) * φ v := by
              simp only [mul_assoc]
          _ = 1 := by rw [(hunit u hu).2, mul_one, (hunit v hv').2]
    exact Units.ext (by
      rw [Units.val_mul, hg _ huv, hg u (hunit u hu), hg v (hunit v hv'), hmul])

/-- Matrix rings over an LEF ring are LEF rings. -/
theorem IsLEFRing.matrix {A : Type*} [Ring A] (hA : IsLEFRing A) (n : Type) [Fintype n]
    [DecidableEq n] : IsLEFRing (Matrix n n A) := by
  classical
  intro t
  obtain ⟨t', hE, hP⟩ : ∃ t' : Finset A, (∀ M ∈ t, ∀ i j, M i j ∈ t') ∧
      ∀ M ∈ t, ∀ N ∈ t, ∀ i j, ∀ S : Finset n, ∑ k ∈ S, M i k * N k j ∈ t' := by
    refine ⟨(t ×ˢ (Finset.univ : Finset (n × n))).image (fun q ↦ q.1 q.2.1 q.2.2) ∪
      (t ×ˢ t ×ˢ (Finset.univ : Finset (n × n)) ×ˢ (Finset.univ : Finset (Finset n))).image
        (fun q ↦ ∑ k ∈ q.2.2.2, q.1 q.2.2.1.1 k * q.2.1 k q.2.2.1.2), ?_, ?_⟩
    · intro M hM i j
      exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨(M, (i, j)), by simp [hM], rfl⟩)
    · intro M hM N hN i j S
      exact Finset.mem_union_right _
        (Finset.mem_image.2 ⟨(M, N, (i, j), S), by simp [hM, hN], rfl⟩)
  obtain ⟨F, _, _, φ, hinj, h0, h1, hφ⟩ := hA t'
  have hsum : ∀ M ∈ t, ∀ N ∈ t, ∀ i j, ∀ S : Finset n,
      φ (∑ k ∈ S, M i k * N k j) = ∑ k ∈ S, φ (M i k) * φ (N k j) := by
    intro M hM N hN i j S
    refine Finset.induction_on S (by simpa using h0) ?_
    intro a S ha ih
    have hprod : M i a * N a j ∈ t' := by simpa using hP M hM N hN i j {a}
    rw [Finset.sum_insert ha, Finset.sum_insert ha, (hφ _ hprod _ (hP M hM N hN i j S)).1, ih,
      (hφ _ (hE M hM i a) _ (hE N hN a j)).2]
  refine ⟨Matrix n n F, inferInstance, inferInstanceAs (Finite (n → n → F)),
    fun M ↦ M.map φ, ?_, Matrix.map_zero φ h0, Matrix.map_one φ h0 h1, ?_⟩
  · intro M hM N hN hMN
    ext i j
    exact hinj (hE M hM i j) (hE N hN i j) (congrFun (congrFun hMN i) j)
  · intro M hM N hN
    refine ⟨?_, ?_⟩
    · ext i j
      exact (hφ _ (hE M hM i j) _ (hE N hN i j)).1
    · ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply]
      exact hsum M hM N hN i j Finset.univ

variable {ι : Type} {R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- **`EL_ι(R)` is LEF over an LEF ring.** -/
theorem isLEF_elementaryGroup (hR : IsLEFRing R) : IsLEF ↥(elementaryGroup ι R) :=
  isLEF_of_injective (elementaryGroup ι R).subtype Subtype.val_injective
    (hR.matrix ι).isLEF_units

/-- **`EL_ι(R)` modulo a finite centre is LEF.** -/
theorem isLEF_elementaryModCentre_of_finite (hR : IsLEFRing R)
    [Finite ↥(Subgroup.center ↥(elementaryGroup ι R))] :
    IsLEF (↥(elementaryGroup ι R) ⧸ Subgroup.center ↥(elementaryGroup ι R)) :=
  isLEF_quotient_of_finite (isLEF_elementaryGroup hR) _

/-- The centre of `EL_ι(R)` is finite when `R` has finitely many central units. -/
theorem finite_center_elementaryGroup [Nontrivial ι]
    (hR : Finite {c : R // (∀ r : R, r * c = c * r) ∧ IsUnit c}) :
    Finite ↥(Subgroup.center ↥(elementaryGroup ι R)) := by
  classical
  haveI := hR
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hmem : ∀ g : ↥(Subgroup.center ↥(elementaryGroup ι R)),
      (∀ r : R, r * (((g : ↥(elementaryGroup ι R)) : (Matrix ι ι R)ˣ) : Matrix ι ι R) i i =
        (((g : ↥(elementaryGroup ι R)) : (Matrix ι ι R)ˣ) : Matrix ι ι R) i i * r) ∧
      IsUnit ((((g : ↥(elementaryGroup ι R)) : (Matrix ι ι R)ˣ) : Matrix ι ι R) i i) := by
    intro g
    obtain ⟨c, hc, hu, hM⟩ := exists_central_unit_scalar_of_mem_center g.2
    rw [hM]
    simpa [Matrix.scalar_apply] using And.intro hc hu
  refine Finite.of_injective (β := {c : R // (∀ r : R, r * c = c * r) ∧ IsUnit c})
    (fun g ↦ ⟨_, hmem g⟩) fun g h hgh ↦ ?_
  obtain ⟨c, -, -, hc⟩ := exists_central_unit_scalar_of_mem_center g.2
  obtain ⟨d, -, -, hd⟩ := exists_central_unit_scalar_of_mem_center h.2
  have hcd : c = d := by
    have := congrArg Subtype.val hgh
    simpa [hc, hd, Matrix.scalar_apply] using this
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [hc, hd, hcd]

/-- **`EL_ι(R)` modulo its centre is LEF** when `R` is an LEF ring with finitely
many central units. -/
theorem isLEF_elementaryModCentre_of_finite_centralUnits [Nontrivial ι] (hR : IsLEFRing R)
    (hZ : Finite {c : R // (∀ r : R, r * c = c * r) ∧ IsUnit c}) :
    IsLEF (↥(elementaryGroup ι R) ⧸ Subgroup.center ↥(elementaryGroup ι R)) :=
  haveI := finite_center_elementaryGroup (ι := ι) hZ
  isLEF_elementaryModCentre_of_finite hR

/-- **`EL_ι(R)` modulo its centre is LEF** when `R` is an LEF ring whose central
elements are `0` and `1`; the centre is then trivial. -/
theorem isLEF_elementaryModCentre_of_central_zero_or_one [Nontrivial ι] (hR : IsLEFRing R)
    (hc : ∀ c : R, (∀ r : R, r * c = c * r) → c = 0 ∨ c = 1) :
    IsLEF (↥(elementaryGroup ι R) ⧸ Subgroup.center ↥(elementaryGroup ι R)) := by
  haveI : Finite ↥(Subgroup.center ↥(elementaryGroup ι R)) := by
    rw [center_elementaryGroup_eq_bot_of_central_zero_or_one hc]
    infer_instance
  exact isLEF_elementaryModCentre_of_finite hR

end Pestov91
end GroupApproximation
