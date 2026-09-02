import GroupApproximation.GGT.HullYiOrientationDetector

/-!
# Hull's orientation-pure radical

Hull's Lemma `K(S)` intersects the elementary closures of the loxodromic
elements of `S` whose elementary closures preserve orientation.  Lemma 5.4
provides two non-commensurable such elements, so this intersection is finite.
It is normalized by `S`, and is trivial when `S` is suitable.

The last theorem applies the finite-intersection argument from Hull's proof:
start with three orientation-pure non-commensurable elements, then exclude the
remaining elements of their finite elementary-closure intersection one at a
time.  This gives a finite orientation-pure family with trivial total
intersection.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G]

/-- A centralizer description of `E(h)` gives the positive-power normalizer
condition used in Hull's definition of the orientation-pure family. -/
theorem hasPositivePowerNormalizer_of_centralizer_pow {h : G} {r : ℕ}
    (hr : 0 < r)
    (hcentral : (elementaryClosure h : Set G) =
      {x : G | Commute x (h ^ (r : ℤ))}) :
    HasPositivePowerNormalizer h := by
  intro t ht
  have htcomm : Commute t (h ^ (r : ℤ)) := by
    exact Set.mem_setOf_eq.mp ((Set.ext_iff.mp hcentral t).mp ht)
  refine ⟨r, hr, ?_⟩
  simpa only [zpow_natCast] using htcomm.mul_inv_cancel

/-- Positive-power normalization is invariant under conjugating the
loxodromic element. -/
theorem hasPositivePowerNormalizer_conj {h : G}
    (hnormal : HasPositivePowerNormalizer h) (a : G) :
    HasPositivePowerNormalizer (a * h * a⁻¹) := by
  intro t ht
  have ht' : a⁻¹ * t * a ∈ elementaryClosure h := by
    apply mem_elementaryClosure_of_conj_mem (a := a)
    have heq : a * (a⁻¹ * t * a) * a⁻¹ = t := by group
    rw [heq]
    exact ht
  obtain ⟨q, hq, hnormalize⟩ := hnormal (a⁻¹ * t * a) ht'
  refine ⟨q, hq, ?_⟩
  have hpow : (a * h * a⁻¹) ^ q = a * h ^ q * a⁻¹ := by
    simpa only [zpow_natCast] using (conj_zpow_eq a h (q : ℤ)).symm
  rw [hpow]
  calc
    t * (a * h ^ q * a⁻¹) * t⁻¹ =
        a * ((a⁻¹ * t * a) * h ^ q * (a⁻¹ * t * a)⁻¹) * a⁻¹ := by
          group
    _ = a * h ^ q * a⁻¹ := by rw [hnormalize]

/-- Hull's `K_G(S)`, with the indexing family represented by the equivalent
positive-power-normalizer condition. -/
def orientationPureRadical (A : Alphabet G) (S : Subgroup G) : Subgroup G :=
  ⨅ h : {h : G // h ∈ S ∧ IsLoxodromic h (Cayley.base A) ∧
    HasPositivePowerNormalizer h}, elementaryClosure (h : G)

theorem mem_orientationPureRadical {A : Alphabet G} {S : Subgroup G} {x : G} :
    x ∈ orientationPureRadical A S ↔
      ∀ h : G, h ∈ S → IsLoxodromic h (Cayley.base A) →
        HasPositivePowerNormalizer h → x ∈ elementaryClosure h := by
  constructor
  · intro hx h hS hlox hnormal
    exact Subgroup.mem_iInf.mp hx ⟨h, hS, hlox, hnormal⟩
  · intro hx
    apply Subgroup.mem_iInf.mpr
    intro h
    exact hx (h : G) h.2.1 h.2.2.1 h.2.2.2

/-- The orientation-pure radical is normalized by the suitable subgroup. -/
theorem conj_mem_orientationPureRadical {A : Alphabet G} {S : Subgroup G}
    {s x : G} (hs : s ∈ S) (hx : x ∈ orientationPureRadical A S) :
    s * x * s⁻¹ ∈ orientationPureRadical A S := by
  apply mem_orientationPureRadical.mpr
  intro h hhS hhlox hhnormal
  let h' := s⁻¹ * h * s
  have hh'S : h' ∈ S := by
    exact S.mul_mem (S.mul_mem (S.inv_mem hs) hhS) hs
  have hh'lox : IsLoxodromic h' (Cayley.base A) := by
    have hc := isLoxodromic_conj (isIsometricAction_cayley A)
      (a := s⁻¹) hhlox
    simpa only [inv_inv] using hc
  have hh'normal : HasPositivePowerNormalizer h' := by
    simpa only [h', inv_inv] using
      hasPositivePowerNormalizer_conj hhnormal s⁻¹
  have hx' : x ∈ elementaryClosure h' :=
    mem_orientationPureRadical.mp hx h' hh'S hh'lox hh'normal
  have hconj := mem_elementaryClosure_conj (a := s) hx'
  have heq : s * h' * s⁻¹ = h := by
    dsimp [h']
    group
  rwa [heq] at hconj

/-- Hull's Lemma `K(S)`, finiteness clause. -/
theorem finite_orientationPureRadical_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : HullGeneratingSet G)
    {S : Subgroup G} (hS : ActsNonElementarily S (Cayley.base A.alphabet)) :
    ((orientationPureRadical A.alphabet S : Subgroup G) : Set G).Finite := by
  obtain ⟨f, r, hfS, hflox, hfnc, -, hr, hcentral⟩ :=
    exists_orientationPure_family_of_dgoLemma421b h421b A hS 2
  have hnormal : ∀ i, HasPositivePowerNormalizer (f i) :=
    fun i ↦ hasPositivePowerNormalizer_of_centralizer_pow (hr i) (hcentral i)
  have hind : Independent (f 0) (f 1) (Cayley.base A.alphabet) := by
    apply ElementaryMorse.independentOfNoCommonZpow_cayley A
      (f 0) (f 1) (hflox 0) (hflox 1)
    intro p q hp hq heq
    exact hfnc 0 1 (by decide) p q hp hq 1 (by simpa using heq)
  by_contra hinf
  exact not_infinite_le_inf_elementaryClosure
    (isIsometricAction_cayley A.alphabet)
    (elementaryClosureVirtuallyCyclic_hullGeneratingSet A)
    (hflox 0) (hflox 1) hind
    (fun _ hx ↦ mem_orientationPureRadical.mp hx
      (f 0) (hfS 0) (hflox 0) (hnormal 0))
    (fun _ hx ↦ mem_orientationPureRadical.mp hx
      (f 1) (hfS 1) (hflox 1) (hnormal 1)) hinf

/-- Suitability makes Hull's orientation-pure radical trivial. -/
theorem orientationPureRadical_eq_bot_of_suitable_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : HullGeneratingSet G)
    {S : Subgroup G} (hS : Suitable A.alphabet S) :
    orientationPureRadical A.alphabet S = ⊥ :=
  hS.normalizesNoNontrivialFinite (orientationPureRadical A.alphabet S)
    (finite_orientationPureRadical_of_dgoLemma421b
      h421b A hS.actsNonElementarily).to_subtype
    (fun _ hs _ hx ↦ conj_mem_orientationPureRadical hs hx)

/-- A finite orientation-pure family detects the trivial radical of a
suitable subgroup.  The first three members are pairwise
non-commensurable; later members exclude the remaining elements of the
finite intersection. -/
theorem exists_fin_orientationPure_family_trivial_intersection_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : HullGeneratingSet G)
    {S : Subgroup G} (hS : Suitable A.alphabet S) :
    ∃ (k : ℕ) (f : Fin k → G) (r : Fin k → ℕ), 3 ≤ k ∧
      (∀ i, f i ∈ S) ∧
      (∀ i, IsLoxodromic (f i) (Cayley.base A.alphabet)) ∧
      (∀ i, 0 < r i) ∧
      (∀ i, (elementaryClosure (f i) : Set G) =
        {x : G | Commute x (f i ^ (r i : ℤ))}) ∧
      ∀ x : G, (∀ i, x ∈ elementaryClosure (f i)) → x = 1 := by
  classical
  obtain ⟨base, baseR, hbaseS, hbaseLox, hbaseNc, -, hbaseRpos,
      hbaseCentral⟩ :=
    exists_orientationPure_family_of_dgoLemma421b
      h421b A hS.actsNonElementarily 3
  let I : Subgroup G := elementaryClosure (base 0) ⊓ elementaryClosure (base 1)
  have hIfin : (I : Set G).Finite := by
    have hind : Independent (base 0) (base 1) (Cayley.base A.alphabet) := by
      apply ElementaryMorse.independentOfNoCommonZpow_cayley A
        (base 0) (base 1) (hbaseLox 0) (hbaseLox 1)
      intro p q hp hq heq
      exact hbaseNc 0 1 (by decide) p q hp hq 1 (by simpa using heq)
    by_contra hinf
    exact not_infinite_le_inf_elementaryClosure
      (isIsometricAction_cayley A.alphabet)
      (elementaryClosureVirtuallyCyclic_hullGeneratingSet A)
      (hbaseLox 0) (hbaseLox 1) hind inf_le_left inf_le_right hinf
  let K := orientationPureRadical A.alphabet S
  let B : Set G := (I : Set G) \ (K : Set G)
  have hBfin : B.Finite := hIfin.subset (fun _ hx ↦ hx.1)
  have hexclude : ∀ x : G, x ∈ B → ∃ h : G,
      h ∈ S ∧ IsLoxodromic h (Cayley.base A.alphabet) ∧
        HasPositivePowerNormalizer h ∧ x ∉ elementaryClosure h := by
    intro x hx
    have hxnot : x ∉ K := hx.2
    rw [mem_orientationPureRadical] at hxnot
    push Not at hxnot
    exact hxnot
  choose witness hwS hwlox hwnormal hwexclude using hexclude
  let pick : G → G := fun x ↦ if hx : x ∈ B then witness x hx else base 0
  have hpickS : ∀ x ∈ B, pick x ∈ S := by
    intro x hx
    simp only [pick, dif_pos hx]
    exact hwS x hx
  have hpickLox : ∀ x ∈ B,
      IsLoxodromic (pick x) (Cayley.base A.alphabet) := by
    intro x hx
    simp only [pick, dif_pos hx]
    exact hwlox x hx
  have hpickNormal : ∀ x ∈ B, HasPositivePowerNormalizer (pick x) := by
    intro x hx
    simp only [pick, dif_pos hx]
    exact hwnormal x hx
  have hpickExclude : ∀ x ∈ B, x ∉ elementaryClosure (pick x) := by
    intro x hx
    simp only [pick, dif_pos hx]
    exact hwexclude x hx
  let baseSet : Finset G := Finset.univ.image base
  let F : Finset G := baseSet ∪ hBfin.toFinset.image pick
  have hbaseInj : Function.Injective base := by
    intro i j hij
    by_contra hne
    exact hbaseNc i j hne 1 1 one_ne_zero one_ne_zero 1 (by simp [hij])
  have hbaseCard : baseSet.card = 3 := by
    rw [Finset.card_image_iff.mpr hbaseInj.injOn]
    simp
  have hFcard : 3 ≤ F.card := by
    rw [← hbaseCard]
    exact Finset.card_le_card (Finset.subset_union_left)
  have hFdata : ∀ h ∈ F, h ∈ S ∧
      IsLoxodromic h (Cayley.base A.alphabet) ∧
      HasPositivePowerNormalizer h := by
    intro h hh
    rw [Finset.mem_union] at hh
    rcases hh with hh | hh
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hh
      exact ⟨hbaseS i, hbaseLox i,
        hasPositivePowerNormalizer_of_centralizer_pow
          (hbaseRpos i) (hbaseCentral i)⟩
    · obtain ⟨x, hxB, rfl⟩ := Finset.mem_image.mp hh
      have hx : x ∈ B := hBfin.mem_toFinset.mp hxB
      exact ⟨hpickS x hx, hpickLox x hx, hpickNormal x hx⟩
  have hFinter : ∀ x : G, (∀ h ∈ F, x ∈ elementaryClosure h) → x = 1 := by
    intro x hx
    have hx0 : x ∈ elementaryClosure (base 0) := by
      apply hx (base 0)
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    have hx1 : x ∈ elementaryClosure (base 1) := by
      apply hx (base 1)
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    have hxI : x ∈ I := ⟨hx0, hx1⟩
    have hxK : x ∈ K := by
      by_contra hxnot
      have hxB : x ∈ B := ⟨hxI, hxnot⟩
      apply hpickExclude x hxB
      apply hx (pick x)
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr
        ⟨x, hBfin.mem_toFinset.mpr hxB, rfl⟩
    change x ∈ orientationPureRadical A.alphabet S at hxK
    rw [orientationPureRadical_eq_bot_of_suitable_of_dgoLemma421b
      h421b A hS, Subgroup.mem_bot] at hxK
    exact hxK
  let f : Fin F.card → G := fun i ↦ (F.equivFin.symm i : F)
  have hfData : ∀ i, f i ∈ S ∧
      IsLoxodromic (f i) (Cayley.base A.alphabet) ∧
      HasPositivePowerNormalizer (f i) := by
    intro i
    exact hFdata (f i) (F.equivFin.symm i).property
  have hpow : ∀ i : Fin F.card, ∃ r : ℕ, 0 < r ∧
      (elementaryClosure (f i) : Set G) =
        {x : G | Commute x (f i ^ (r : ℤ))} := by
    intro i
    exact exists_elementaryClosure_eq_centralizer_pow_of_hasPositivePowerNormalizer
      A (hfData i).2.1 (hfData i).2.2
  choose r hr hcentral using hpow
  refine ⟨F.card, f, r, hFcard, fun i ↦ (hfData i).1,
    fun i ↦ (hfData i).2.1, hr, hcentral, ?_⟩
  intro x hx
  apply hFinter x
  intro h hh
  let i : Fin F.card := F.equivFin ⟨h, hh⟩
  have hfi : f i = h := by
    change ((F.equivFin.symm (F.equivFin ⟨h, hh⟩) : F) : G) = h
    simp
  rw [← hfi]
  exact hx i

end HullSC
end GroupApproximation
