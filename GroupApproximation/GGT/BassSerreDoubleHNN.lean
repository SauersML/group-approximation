import GroupApproximation.GGT.BassSerreHNNAction
import GroupApproximation.GGT.WPDAcylindricalHyperbolicity
import GroupApproximation.Manuscript.NonMF.FournierFacioDoubleHNN

/-!
# The Bass--Serre tree of the manuscript's `E`, and its acylindrical
hyperbolicity

`non_mf_groups_exist.tex`, Section *"A torsion-free group with full MF
radical"*:

> Let `E` be the double HNN extension of `P` with stable letters `u₁, u₂` and
> `uᵢPuᵢ⁻¹ = Pᵢ`; it is finitely presented and torsion-free, and its Bass--Serre
> action makes it acylindrically hyperbolic by the tree criterion of
> Minasyan--Osin.

`Manuscript/NonMF/FournierFacioDoubleHNN.lean` builds `E = Skeleton f hf` as two
successive Mathlib `HNNExtension`s, proves it finitely presented and
torsion-free, and leaves the acylindrical hyperbolicity as a citation.  This
module supplies the Bass--Serre half of that citation.

## Which tree

`E` is presented as an HNN extension of `E₁ = ⟨P, u₁⟩` with associated
subgroups `ιP` and `ιP₂`, and it is *that* splitting whose Bass--Serre tree
`GGT/BassSerreHNNTree.lean` builds.  Its edge stabilisers are the conjugates of
`ι(P)`, exactly the edge group of the two-letter picture the manuscript draws,
so the computation the manuscript records --- the printed sentence

> the pointwise stabiliser of the two vertices `u₁Δ` and `u₂Δ` is
> `Δ₁ ∩ Δ₂ = 1`

--- is available here without any multi-letter Britton lemma.

## What is proved

* `factorOne_eq_factorTwo_imp` --- **`P₁ ∩ P₂ = 1`**, from injectivity of the
  printed embedding `f : P × P × S ↪ P` alone.
* `stageOneBase_ne_top`, `stageTwoTarget_ne_top` --- both associated subgroups
  are proper, so the splitting is not ascending.  Britton at the *first* level:
  `u₁ ∉ ιP`.
* `axisWord`, `isLoxodromic_axisElt` --- `u₂u₁⁻¹` is a one-syllable cyclically
  reduced word, hence a **loxodromic isometry of translation length one**.
* `eq_one_of_fixes_axis_segment` --- **the printed sentence**: the pointwise
  stabiliser of the three consecutive axis vertices `Δ`, `u₂u₁⁻¹Δ`,
  `(u₂u₁⁻¹)²Δ` is trivial.  Conjugating the two edge stabilisers into `Δ` turns
  this into `ι(P₁) ∩ ι(P₂) = 1`, which is `factorOne_eq_factorTwo_imp`.
* `not_isVirtuallyCyclic` --- the two stable letters have no common nonzero
  power, by the exponent-sum grading of the outer extension together with
  Britton at the inner one.
* `ah3Data`, `isAcylindricallyHyperbolic_of` --- the assembly.  Given
  `BassSerreHNN.IsTreeWPDCriterion` (the tree-geometry step named in
  `GGT/BassSerreHNNAction.lean`) and `GGT.OsinTheorem12` (the literature input
  named in `GGT/WPDAcylindricalHyperbolicity.lean`), `E` is acylindrically
  hyperbolic.  Those two propositions are the entire remaining debt; every
  group-theoretic ingredient above is proved.
-/

namespace GroupApproximation
namespace GGT
namespace BassSerreDoubleHNN

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TheoremC

variable {P : Type} [Group P] {j₁ j₂ : P →* P}

/-! ## The two associated subgroups are proper -/

theorem stageOneBase_ne_top (hj₁ : Function.Injective j₁) :
    stageOneBase j₁ hj₁ ≠ ⊤ := by
  intro htop
  have hmem : (HNNExtension.t : StageOne j₁ hj₁) ∈ stageOneBase j₁ hj₁ := by
    rw [htop]
    exact Subgroup.mem_top _
  exact BassSerreHNN.t_notMem_range (stageOneEquiv j₁ hj₁) hmem

theorem stageTwoTarget_le_stageOneBase (hj₁ : Function.Injective j₁) :
    stageTwoTarget j₁ j₂ hj₁ ≤ stageOneBase j₁ hj₁ := by
  rintro x ⟨z, -, rfl⟩
  exact ⟨z, rfl⟩

theorem stageTwoTarget_ne_top (hj₁ : Function.Injective j₁) :
    stageTwoTarget j₁ j₂ hj₁ ≠ ⊤ := by
  intro htop
  refine stageOneBase_ne_top hj₁ (le_antisymm le_top ?_)
  rw [← htop]
  exact stageTwoTarget_le_stageOneBase hj₁

/-! ## The stable letters, unfolded -/

@[simp] theorem firstStableLetter_eq (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) :
    firstStableLetter j₁ j₂ hj₁ hj₂
      = (HNNExtension.of : StageOne j₁ hj₁ →* Double j₁ j₂ hj₁ hj₂)
          HNNExtension.t := rfl

@[simp] theorem secondStableLetter_eq (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) :
    secondStableLetter j₁ j₂ hj₁ hj₂
      = (HNNExtension.t : Double j₁ j₂ hj₁ hj₂) := rfl

@[simp] theorem doubleIota_apply (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) (p : P) :
    doubleIota j₁ j₂ hj₁ hj₂ p
      = (HNNExtension.of : StageOne j₁ hj₁ →* Double j₁ j₂ hj₁ hj₂)
          (HNNExtension.of p) := rfl

/-! ## The axis element `u₂u₁⁻¹` -/

/-- The one-syllable cyclically reduced word spelling `u₂u₁⁻¹`.  Its seam
condition is vacuous: a single syllable is its own predecessor and successor,
so the sign agreement it demands is `1 = 1`. -/
def axisWord (hj₁ : Function.Injective j₁) :
    HNNTorsionFree.CyclicWord (StageOne j₁ hj₁) (stageOneBase j₁ hj₁)
      (stageTwoTarget j₁ j₂ hj₁) where
  letters := [((1 : ℤˣ), (HNNExtension.t : StageOne j₁ hj₁)⁻¹)]
  nonempty := by simp
  chain := List.isChain_singleton _
  cyclic := by
    intro x hx y hy _
    rw [List.getLast?_singleton, Option.mem_some_iff] at hx
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hx
    subst hy
    rfl

/-- `u₂u₁⁻¹`, the element whose axis the argument runs along. -/
noncomputable def axisElt (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) : Double j₁ j₂ hj₁ hj₂ :=
  HNNExtension.t *
    ((HNNExtension.of : StageOne j₁ hj₁ →* Double j₁ j₂ hj₁ hj₂)
      HNNExtension.t)⁻¹

@[simp] theorem axisElt_eq (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) :
    axisElt hj₁ hj₂
      = secondStableLetter j₁ j₂ hj₁ hj₂ *
        (firstStableLetter j₁ j₂ hj₁ hj₂)⁻¹ := rfl

theorem axisWord_elem (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) :
    (axisWord (j₂ := j₂) hj₁).elem (stageTwoEquiv j₁ j₂ hj₁ hj₂)
      = axisElt hj₁ hj₂ := by
  have h1 : (axisWord (j₂ := j₂) hj₁).elem (stageTwoEquiv j₁ j₂ hj₁ hj₂)
      = HNNBritton.spell (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        [((1 : ℤˣ), (HNNExtension.t : StageOne j₁ hj₁)⁻¹)] := rfl
  have hv : (((1 : ℤˣ)) : ℤ) = 1 := rfl
  rw [h1, BassSerreHNN.spell_singleton, hv, zpow_one, axisElt, map_inv]

/-- **`u₂u₁⁻¹` is a loxodromic isometry of the Bass--Serre tree**, with
translation length one. -/
theorem isLoxodromic_axisElt (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) :
    IsLoxodromic (axisElt hj₁ hj₂)
      (BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1) := by
  have h := BassSerreHNN.isLoxodromic_cyclicWord
    (stageTwoEquiv j₁ j₂ hj₁ hj₂) (axisWord (j₂ := j₂) hj₁)
  rwa [axisWord_elem] at h

/-! ## The two edges of the axis -/

theorem vmk_axisElt (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) :
    BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) (axisElt hj₁ hj₂)
      = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (1 * HNNExtension.t) := by
  rw [one_mul, axisElt, ← map_inv, BassSerreHNN.vmk_mul_of]

theorem vmk_axisElt_sq (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) :
    BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) (axisElt hj₁ hj₂ ^ 2)
      = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (axisElt hj₁ hj₂ * HNNExtension.t) := by
  have h : axisElt hj₁ hj₂ ^ 2
      = axisElt hj₁ hj₂ * HNNExtension.t *
        (HNNExtension.of : StageOne j₁ hj₁ →* Double j₁ j₂ hj₁ hj₂)
          (HNNExtension.t : StageOne j₁ hj₁)⁻¹ := by
    rw [pow_two, axisElt, map_inv]
    group
  rw [h, BassSerreHNN.vmk_mul_of]

/-! ## `P₁ ∩ P₂ = 1` -/

/-- **The printed intersection.**  Two different factors of the printed
subgroup `P₁ × P₂ × S ≤ P` meet only in the identity, by injectivity of the
printed embedding. -/
theorem factorOne_eq_factorTwo_imp {S : Type} [Group S]
    (f : (P × P × S) →* P) (hf : Function.Injective f) {p q : P}
    (h : factorOne f p = factorTwo f q) : p = 1 := by
  have h1 : f ((p, 1, 1) : P × P × S) = f ((1, q, 1) : P × P × S) := h
  have h2 : ((p, 1, 1) : P × P × S) = ((1, q, 1) : P × P × S) := hf h1
  exact congrArg (fun z : P × P × S => z.1) h2

/-! ## The pointwise stabiliser of the axis segment -/

/-- Conjugation cancels on both sides. -/
theorem eq_of_conj_eq {Γ : Type*} [Group Γ] (a X Y : Γ)
    (h : a * X * a⁻¹ = a * Y * a⁻¹) : X = Y := by
  have h1 := congrArg (fun z => a⁻¹ * z * a) h
  simpa [mul_assoc] using h1

/-- **The printed sentence.**  The pointwise stabiliser of the three
consecutive axis vertices `Δ`, `u₂u₁⁻¹Δ`, `(u₂u₁⁻¹)²Δ` is trivial.

The two edges of the segment give `g = ι(j₂ p)` and `g = h·ι(j₂ q)·h⁻¹` with
`h = u₂u₁⁻¹`; cancelling `u₂` and then conjugating by `u₁` turns the resulting
equation into `ι(j₁ p) = ι(j₂ q)`, i.e. `P₁ ∩ P₂ ≠ 1` unless `p = 1`. -/
theorem eq_one_of_fixes_axis_segment (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂)
    (hinter : ∀ p q : P, j₁ p = j₂ q → p = 1)
    (g : Double j₁ j₂ hj₁ hj₂)
    (h0 : g • BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1
        = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
    (h1 : g • BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂)
        = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂) (axisElt hj₁ hj₂))
    (h2 : g • BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ 2)
        = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
          (axisElt hj₁ hj₂ ^ 2)) :
    g = 1 := by
  have h1a : g • BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (1 * HNNExtension.t)
      = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (1 * HNNExtension.t) := by
    rw [← vmk_axisElt hj₁ hj₂]
    exact h1
  have h2a : g • BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (axisElt hj₁ hj₂ * HNNExtension.t)
      = BassSerreHNN.vmk (stageTwoEquiv j₁ j₂ hj₁ hj₂)
        (axisElt hj₁ hj₂ * HNNExtension.t) := by
    rw [← vmk_axisElt_sq hj₁ hj₂]
    exact h2
  obtain ⟨b, hbmem, hb⟩ :=
    (BassSerreHNN.smul_edge_eq_iff (stageTwoEquiv j₁ j₂ hj₁ hj₂) g 1).1
      ⟨h0, h1a⟩
  obtain ⟨b', hbmem', hb'⟩ :=
    (BassSerreHNN.smul_edge_eq_iff (stageTwoEquiv j₁ j₂ hj₁ hj₂) g
      (axisElt hj₁ hj₂)).1 ⟨h1, h2a⟩
  obtain ⟨z, hz, hzb⟩ := hbmem
  obtain ⟨p, hp⟩ := hz
  obtain ⟨z', hz', hzb'⟩ := hbmem'
  obtain ⟨q, hq⟩ := hz'
  have hbval : b = (HNNExtension.of : P →* StageOne j₁ hj₁) (j₂ p) := by
    rw [← hzb, ← hp]
  have hbval' : b' = (HNNExtension.of : P →* StageOne j₁ hj₁) (j₂ q) := by
    rw [← hzb', ← hq]
  have hg : g = doubleIota j₁ j₂ hj₁ hj₂ (j₂ p) := by
    rw [hb, one_mul, inv_one, mul_one, hbval, doubleIota_apply]
  have hg' : g = axisElt hj₁ hj₂ * doubleIota j₁ j₂ hj₁ hj₂ (j₂ q) *
      (axisElt hj₁ hj₂)⁻¹ := by
    rw [hb', hbval', doubleIota_apply]
  have hE : doubleIota j₁ j₂ hj₁ hj₂ (j₂ p)
      = axisElt hj₁ hj₂ * doubleIota j₁ j₂ hj₁ hj₂ (j₂ q) *
        (axisElt hj₁ hj₂)⁻¹ := hg.symm.trans hg'
  have hstep : secondStableLetter j₁ j₂ hj₁ hj₂ *
        doubleIota j₁ j₂ hj₁ hj₂ p * (secondStableLetter j₁ j₂ hj₁ hj₂)⁻¹
      = secondStableLetter j₁ j₂ hj₁ hj₂ *
        ((firstStableLetter j₁ j₂ hj₁ hj₂)⁻¹ *
          doubleIota j₁ j₂ hj₁ hj₂ (j₂ q) *
          firstStableLetter j₁ j₂ hj₁ hj₂) *
        (secondStableLetter j₁ j₂ hj₁ hj₂)⁻¹ := by
    rw [conj_secondStableLetter, hE, axisElt_eq]
    group
  have hp1 : doubleIota j₁ j₂ hj₁ hj₂ p
      = (firstStableLetter j₁ j₂ hj₁ hj₂)⁻¹ *
        doubleIota j₁ j₂ hj₁ hj₂ (j₂ q) *
        firstStableLetter j₁ j₂ hj₁ hj₂ :=
    eq_of_conj_eq _ _ _ hstep
  have hkey : doubleIota j₁ j₂ hj₁ hj₂ (j₁ p)
      = doubleIota j₁ j₂ hj₁ hj₂ (j₂ q) := by
    rw [← conj_firstStableLetter, hp1]
    group
  have hjeq : j₁ p = j₂ q := doubleIota_injective j₁ j₂ hj₁ hj₂ hkey
  have hp0 : p = 1 := hinter p q hjeq
  rw [hg, hp0, map_one, map_one]

/-! ## `E` is not virtually cyclic -/

theorem no_common_power (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) (m k : ℤ)
    (h : (secondStableLetter j₁ j₂ hj₁ hj₂) ^ m
        = (firstStableLetter j₁ j₂ hj₁ hj₂) ^ k) : m = 0 ∧ k = 0 := by
  have hm : m = 0 := by
    have h1 := congrArg
      (HNNBritton.exponentSum (stageTwoEquiv j₁ j₂ hj₁ hj₂)) h
    rw [map_zpow, map_zpow, secondStableLetter_eq, firstStableLetter_eq,
      HNNBritton.exponentSum_t, HNNBritton.exponentSum_of, one_zpow] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    simp only [toAdd_zpow, toAdd_ofAdd, toAdd_one, zsmul_eq_mul, Int.cast_id,
      mul_one] at h2
    exact h2
  refine ⟨hm, ?_⟩
  subst hm
  rw [zpow_zero, firstStableLetter_eq] at h
  have h3 : (HNNExtension.t : StageOne j₁ hj₁) ^ k = 1 := by
    refine HNNExtension.of_injective (stageTwoEquiv j₁ j₂ hj₁ hj₂) ?_
    rw [map_zpow, map_one, ← h]
  by_contra hk
  exact HNNBritton.t_zpow_ne_one (stageOneEquiv j₁ hj₁) hk h3

theorem not_isVirtuallyCyclic (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂) :
    ¬ IsVirtuallyCyclic (Double j₁ j₂ hj₁ hj₂) :=
  not_isVirtuallyCyclic_of_no_common_power
    (a := secondStableLetter j₁ j₂ hj₁ hj₂)
    (b := firstStableLetter j₁ j₂ hj₁ hj₂)
    (no_common_power hj₁ hj₂)

/-! ## The `(AH₃)` datum -/

/-- **The Bass--Serre `(AH₃)` datum of `E`.**  The tree, the element `u₂u₁⁻¹`,
and the base vertex.  Hyperbolicity is `δ = 0`; loxodromy is the one-syllable
cyclic word; the WPD clause is the named tree criterion applied to the trivial
segment stabiliser. -/
noncomputable def ah3Data (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂)
    (hinter : ∀ p q : P, j₁ p = j₂ q → p = 1)
    (hcrit : BassSerreHNN.IsTreeWPDCriterion (Double j₁ j₂ hj₁ hj₂)
      (BassSerreHNN.tree_isTree (stageTwoEquiv j₁ j₂ hj₁ hj₂))) :
    AH3Data.{0, 0} (Double j₁ j₂ hj₁ hj₂) where
  Space := BassSerreHNN.Space (stageTwoEquiv j₁ j₂ hj₁ hj₂)
  isometric := BassSerreHNN.isIsometricAction (stageTwoEquiv j₁ j₂ hj₁ hj₂)
  delta := 0
  hyperbolic :=
    BassSerreHNN.isHyperbolicSpace_zero_space (stageTwoEquiv j₁ j₂ hj₁ hj₂)
  elt := axisElt hj₁ hj₂
  base := BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1
  loxodromic := isLoxodromic_axisElt hj₁ hj₂
  wpd := by
    refine hcrit (axisElt hj₁ hj₂)
      (BassSerreHNN.pt (stageTwoEquiv j₁ j₂ hj₁ hj₂) 1)
      (BassSerreHNN.isIsometricAction (stageTwoEquiv j₁ j₂ hj₁ hj₂))
      (isLoxodromic_axisElt hj₁ hj₂) ?_
    intro g hg
    have hf0 := hg 0 (by omega)
    have hf1 := hg 1 (by omega)
    have hf2 := hg 2 (by omega)
    rw [pow_zero, one_smul] at hf0
    rw [pow_one] at hf1
    rw [BassSerreHNN.smul_pt, mul_one] at hf1
    rw [BassSerreHNN.smul_pt, mul_one] at hf2
    rw [BassSerreHNN.smul_pt_eq_iff] at hf0
    rw [BassSerreHNN.smul_pt_eq_iff] at hf1
    rw [BassSerreHNN.smul_pt_eq_iff] at hf2
    exact eq_one_of_fixes_axis_segment hj₁ hj₂ hinter g hf0 hf1 hf2

/-- **`E` is acylindrically hyperbolic**, granted the two named literature
inputs. -/
theorem isAcylindricallyHyperbolic_of (hj₁ : Function.Injective j₁)
    (hj₂ : Function.Injective j₂)
    (hinter : ∀ p q : P, j₁ p = j₂ q → p = 1)
    (hcrit : BassSerreHNN.IsTreeWPDCriterion (Double j₁ j₂ hj₁ hj₂)
      (BassSerreHNN.tree_isTree (stageTwoEquiv j₁ j₂ hj₁ hj₂)))
    (hosin : OsinTheorem12.{0, 0}) :
    IsAcylindricallyHyperbolic (Double j₁ j₂ hj₁ hj₂) :=
  hosin (Double j₁ j₂ hj₁ hj₂) (ah3Data hj₁ hj₂ hinter hcrit)
    (not_isVirtuallyCyclic hj₁ hj₂)

/-! ## At the manuscript's data -/

section Skeleton

variable {S : Type} [Group S] (f : (P × P × S) →* P) (hf : Function.Injective f)

/-- `P₁ ∩ P₂ = 1`, in the shape the segment computation consumes. -/
theorem skeleton_inter :
    ∀ p q : P, factorOne f p = factorTwo f q → p = 1 :=
  fun _ _ h => factorOne_eq_factorTwo_imp f hf h

/-- **The printed sentence at the printed data.**  For the manuscript's `E`,
the pointwise stabiliser of the three consecutive vertices along the axis of
`u₂u₁⁻¹` is trivial. -/
theorem skeleton_eq_one_of_fixes_axis_segment
    (g : Skeleton f hf)
    (h0 : g • BassSerreHNN.vmk (stageTwoEquiv (factorOne f) (factorTwo f)
          (factorOne_injective f hf) (factorTwo_injective f hf)) 1
        = BassSerreHNN.vmk (stageTwoEquiv (factorOne f) (factorTwo f)
          (factorOne_injective f hf) (factorTwo_injective f hf)) 1)
    (h1 : g • BassSerreHNN.vmk (stageTwoEquiv (factorOne f) (factorTwo f)
          (factorOne_injective f hf) (factorTwo_injective f hf))
          (axisElt (factorOne_injective f hf) (factorTwo_injective f hf))
        = BassSerreHNN.vmk (stageTwoEquiv (factorOne f) (factorTwo f)
          (factorOne_injective f hf) (factorTwo_injective f hf))
          (axisElt (factorOne_injective f hf) (factorTwo_injective f hf)))
    (h2 : g • BassSerreHNN.vmk (stageTwoEquiv (factorOne f) (factorTwo f)
          (factorOne_injective f hf) (factorTwo_injective f hf))
          (axisElt (factorOne_injective f hf) (factorTwo_injective f hf) ^ 2)
        = BassSerreHNN.vmk (stageTwoEquiv (factorOne f) (factorTwo f)
          (factorOne_injective f hf) (factorTwo_injective f hf))
          (axisElt (factorOne_injective f hf)
            (factorTwo_injective f hf) ^ 2)) :
    g = 1 :=
  eq_one_of_fixes_axis_segment (factorOne_injective f hf)
    (factorTwo_injective f hf) (skeleton_inter f hf) g h0 h1 h2

/-- **`E` is not virtually cyclic.** -/
theorem skeleton_not_isVirtuallyCyclic :
    ¬ IsVirtuallyCyclic (Skeleton f hf) :=
  not_isVirtuallyCyclic (factorOne_injective f hf) (factorTwo_injective f hf)

/-- **`E` is acylindrically hyperbolic.**  Everything group-theoretic is
proved; the two hypotheses are the tree-geometry step named in
`GGT/BassSerreHNNAction.lean` and Osin's Theorem 1.2 named in
`GGT/WPDAcylindricalHyperbolicity.lean`. -/
theorem skeleton_isAcylindricallyHyperbolic
    (hcrit : BassSerreHNN.IsTreeWPDCriterion (Skeleton f hf)
      (BassSerreHNN.tree_isTree (stageTwoEquiv (factorOne f) (factorTwo f)
        (factorOne_injective f hf) (factorTwo_injective f hf))))
    (hosin : OsinTheorem12.{0, 0}) :
    IsAcylindricallyHyperbolic (Skeleton f hf) :=
  isAcylindricallyHyperbolic_of (factorOne_injective f hf)
    (factorTwo_injective f hf) (skeleton_inter f hf) hcrit hosin

end Skeleton

end BassSerreDoubleHNN
end GGT
end GroupApproximation
