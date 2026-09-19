import GroupApproximation.GGT.BassSerreHNNAction
import GroupApproximation.GGT.CayleyGeodesicRealisation
import GroupApproximation.GGT.HyperbolicWPDTransfer

/-!
# A genuine geodesic realization of the Bass--Serre tree orbit

The vertex metric of a Bass--Serre tree is integer-valued, hence is not a
geodesic space in the real-parameter sense used by Osin and DGO.  This module
replaces it by the metric realization of the Cayley graph whose alphabet is
the set of elements of Bass--Serre syllable length at most one.

The comparison is sharp up to one: the syllable length of `x` is at most its
word length in this alphabet, while a reduced HNN spelling gives a word of
length at most `tLen x + 1` (the extra letter is the initial base-group
element).  Thus the orbit map from the Cayley vertices to the Bass--Serre tree
has additive distortion one.  Hyperbolicity, loxodromy, and WPD consequently
transfer to the genuine geodesic realization already constructed in
`CayleyGeodesicRealisation`.
-/

namespace GroupApproximation
namespace GGT
namespace BassSerreHNN

open GroupApproximation.HNNBritton
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.AxisDichotomyRoute
open scoped Classical

universe u

variable {G : Type u} [Group G] {A B : Subgroup G}

/-- The HNN elements moving the base vertex by at most one edge. -/
def syllableSet (φ : A ≃* B) : Set (HNNExtension G A B φ) :=
  {x | tLen φ x ≤ 1}

theorem syllableSet_inv_mem (φ : A ≃* B) {x : HNNExtension G A B φ}
    (hx : x ∈ syllableSet φ) : x⁻¹ ∈ syllableSet φ := by
  change tLen φ x⁻¹ ≤ 1
  rw [tLen_inv]
  exact hx

theorem syllableSet_closure_eq_top (φ : A ≃* B) :
    Subgroup.closure (syllableSet φ) = ⊤ := by
  refine top_le_iff.mp ?_
  intro x hxTop
  clear hxTop
  induction x using HNNExtension.induction_on with
  | of g =>
      exact Subgroup.subset_closure (by simp [syllableSet, tLen_of])
  | t =>
      exact Subgroup.subset_closure (by simp [syllableSet, tLen_t])
  | mul x y hx hy => exact Subgroup.mul_mem _ hx hy
  | inv x hx => exact Subgroup.inv_mem _ hx

/-- The syllable-one alphabet of the Bass--Serre action. -/
def syllableAlphabet (φ : A ≃* B) : Alphabet (HNNExtension G A B φ) where
  carrier := syllableSet φ
  symmetricGenerating :=
    ⟨fun _ hx => syllableSet_inv_mem φ hx, syllableSet_closure_eq_top φ⟩

/-- A product of syllable-one elements has Bass--Serre syllable length at most
the number of factors. -/
theorem tLen_prod_le_length (φ : A ≃* B) :
    ∀ (l : List (HNNExtension G A B φ)),
      (∀ x ∈ l, x ∈ syllableSet φ) → tLen φ l.prod ≤ l.length := by
  intro l
  induction l with
  | nil =>
      intro _
      simp [tLen_one]
  | cons x l ih =>
      intro hl
      have hx : tLen φ x ≤ 1 := hl x (by simp)
      have htail : ∀ y ∈ l, y ∈ syllableSet φ := by
        intro y hy
        exact hl y (by simp [hy])
      have hmul := tLen_mul_le φ x l.prod
      have hi := ih htail
      simp only [List.prod_cons, List.length_cons]
      omega

/-- Word length in the syllable-one alphabet dominates Bass--Serre syllable
length. -/
theorem tLen_le_wordNorm_syllableAlphabet (φ : A ≃* B)
    (x : HNNExtension G A B φ) :
    tLen φ x ≤ wordNorm (syllableAlphabet φ).carrier x := by
  obtain ⟨l, hl, hlen⟩ :=
    exists_isWord_length_eq (syllableAlphabet φ).symmetricGenerating x
  rw [← hlen]
  rw [← hl.prod_eq]
  exact tLen_prod_le_length φ l hl.letters

/-- The factors of an HNN spelling, with its initial base-group element kept as
one extra syllable-zero letter. -/
def spellingFactors (φ : A ≃* B) (g : G) (l : List (ℤˣ × G)) :
    List (HNNExtension G A B φ) :=
  HNNExtension.of g :: l.map fun p =>
    HNNExtension.t ^ (p.1 : ℤ) * HNNExtension.of p.2

@[simp] theorem spellingFactors_length (φ : A ≃* B) (g : G)
    (l : List (ℤˣ × G)) :
    (spellingFactors φ g l).length = l.length + 1 := by
  simp [spellingFactors]

theorem spellingFactors_prod (φ : A ≃* B) (g : G)
    (l : List (ℤˣ × G)) :
    (spellingFactors φ g l).prod = wordProd φ g l := by
  induction l generalizing g with
  | nil => simp [spellingFactors, wordProd, spell]
  | cons p l ih =>
      obtain ⟨u, h⟩ := p
      have ihh := ih h
      simp only [spellingFactors, List.prod_cons] at ihh ⊢
      calc
        HNNExtension.of g *
              ((HNNExtension.t ^ (u : ℤ) * HNNExtension.of h) *
                (List.map
                  (fun p => HNNExtension.t ^ (p.1 : ℤ) * HNNExtension.of p.2) l).prod)
            = HNNExtension.of g * HNNExtension.t ^ (u : ℤ) *
                (HNNExtension.of h *
                  (List.map
                    (fun p => HNNExtension.t ^ (p.1 : ℤ) * HNNExtension.of p.2)
                    l).prod) := by group
        _ = HNNExtension.of g * HNNExtension.t ^ (u : ℤ) * wordProd φ h l := by
              rw [ihh]
        _ = wordProd φ g ((u, h) :: l) := (wordProd_cons φ g u h l).symm

theorem spellingFactors_letters (φ : A ≃* B) (g : G)
    (l : List (ℤˣ × G)) :
    ∀ x ∈ spellingFactors φ g l, x ∈ syllableSet φ := by
  intro x hx
  simp only [spellingFactors, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨p, hp, rfl⟩
  · simp [syllableSet, tLen_of]
  · obtain ⟨u, h⟩ := p
    simp only
    change tLen φ (HNNExtension.t ^ (u : ℤ) * HNNExtension.of h) ≤ 1
    rw [tLen_mul_of, tLen_t_zpow]

/-- A reduced spelling gives a word in the syllable-one alphabet with only the
initial base-group letter as overhead. -/
theorem wordNorm_syllableAlphabet_le_tLen_add_one (φ : A ≃* B)
    (x : HNNExtension G A B φ) :
    wordNorm (syllableAlphabet φ).carrier x ≤ tLen φ x + 1 := by
  obtain ⟨g, l, hl, hp, hlen⟩ := tLen_mem φ x
  have hw : IsWord (syllableAlphabet φ).carrier (spellingFactors φ g l) x :=
    ⟨spellingFactors_letters φ g l, (spellingFactors_prod φ g l).trans hp⟩
  have hle := wordNorm_le_length hw
  rw [spellingFactors_length, hlen] at hle
  exact hle

/-- The orbit map from syllable Cayley vertices to the Bass--Serre tree. -/
def cayleyToTree (φ : A ≃* B) :
    Cayley (syllableAlphabet φ) → Space φ :=
  fun x => pt φ (Cayley.val x)

theorem cayleyToTree_equivariant (φ : A ≃* B) :
    IsEquivariant (HNNExtension G A B φ) (cayleyToTree φ) := by
  intro a x
  change pt φ (a * Cayley.val x) = a • pt φ (Cayley.val x)
  rw [smul_pt]

theorem cayleyToTree_additiveDistortion (φ : A ≃* B) :
    HasAdditiveDistortion 1 (cayleyToTree φ) := by
  intro x y
  let z := (Cayley.val x)⁻¹ * Cayley.val y
  have hlo : tLen φ z ≤ wordNorm (syllableAlphabet φ).carrier z :=
    tLen_le_wordNorm_syllableAlphabet φ z
  have hup : wordNorm (syllableAlphabet φ).carrier z ≤ tLen φ z + 1 :=
    wordNorm_syllableAlphabet_le_tLen_add_one φ z
  have hloR : (tLen φ z : ℝ) ≤ (wordNorm (syllableAlphabet φ).carrier z : ℝ) := by
    exact_mod_cast hlo
  have hupR : (wordNorm (syllableAlphabet φ).carrier z : ℝ) ≤ tLen φ z + 1 := by
    exact_mod_cast hup
  simp only [cayleyToTree, dist_pt, Cayley.dist_eq]
  change |(tLen φ z : ℝ) - (wordNorm (syllableAlphabet φ).carrier z : ℝ)| ≤ 1
  rw [abs_le]
  constructor <;> linarith

/-- The syllable Cayley graph is hyperbolic because its vertex metric differs
from the Bass--Serre tree orbit metric by at most one. -/
theorem isHyperbolicSpace_syllableCayley (φ : A ≃* B) :
    IsHyperbolicSpace 3 (Cayley (syllableAlphabet φ)) := by
  have h := isHyperbolicSpace_of_additiveDistortion
    (cayleyToTree_additiveDistortion φ) (isHyperbolicSpace_zero_space φ)
  norm_num at h ⊢
  exact h

/-- The genuine geodesic hyperbolic model attached to the Bass--Serre orbit. -/
noncomputable def geodesicModel (φ : A ≃* B) :
    GeodesicModel (HNNExtension G A B φ) (Cayley (syllableAlphabet φ)) :=
  CayleyGeodesicModel.modelQuot (syllableAlphabet φ)
    (isHyperbolicSpace_syllableCayley φ) (by norm_num)
    (CayleyGeodesicModel.isGeodesicRealisationQuot (syllableAlphabet φ))

end BassSerreHNN
end GGT
end GroupApproximation
