import GroupApproximation.Higman.Benign
import GroupApproximation.Higman.MikhailovaFiberProduct

/-!
# The rank-three Mikhailova benign witness

This file packages the fibre-product calculation in the exact finite-rank
shape used after a marked embedding of a three-generator recursively
presented group has been produced.

Given finite presentation data `R` on `X` and marked lifts
`words : F₃ →* FreeGroup X`, put

`K = F₃ × FreeGroup X × FreeGroup X`

and embed `f` as `(f, words f, 1)`.  The cutting subgroup is the whole first
factor times the Mikhailova fibre product for `R`.  We prove directly that its
preimage is the kernel of the marked presentation map.  If the marked map
factors an injective map from another presented quotient, that kernel is the
normal closure of the source relators.  This supplies an actual
`BenignWitness`, not an interface asking for one.
-/

namespace GroupApproximation
namespace Higman
namespace MikhailovaRankThree

open GroupApproximation.ProductFinitePresentation

/-- The compiler's rank-three free source. -/
abbrev Source : Type := FreeGroup (Fin 3)

/-- The product-of-free-groups ambient group. -/
abbrev Ambient (X : Type) : Type :=
  Source × (FreeGroup X × FreeGroup X)

/-- The quotient homomorphism named by a relator set. -/
def quotientHom {X : Type} (R : Set (FreeGroup X)) :
    FreeGroup X →* PresentedGroup R :=
  QuotientGroup.mk' (Subgroup.normalClosure R)

@[simp] theorem quotientHom_apply {X : Type} (R : Set (FreeGroup X))
    (w : FreeGroup X) :
    quotientHom R w = PresentedGroup.mk R w := rfl

/-- Embed a source word together with its marked lift and a trivial second
copy.  The independent source coordinate makes this map injective. -/
def inputHom {X : Type} (words : Source →* FreeGroup X) :
    Source →* Ambient X :=
  (MonoidHom.id Source).prod (words.prod (1 : Source →* FreeGroup X))

@[simp] theorem inputHom_apply {X : Type} (words : Source →* FreeGroup X)
    (f : Source) : inputHom words f = (f, words f, 1) := rfl

theorem inputHom_injective {X : Type} (words : Source →* FreeGroup X) :
    Function.Injective (inputHom words) := by
  intro f g hfg
  exact congrArg Prod.fst hfg

/-- The entire source factor times the Mikhailova subgroup. -/
def cuttingSubgroup {X : Type} (R : Set (FreeGroup X)) :
    Subgroup (Ambient X) :=
  (⊤ : Subgroup Source).prod (Mikhailova.freeSubgroup R)

/-- Elementwise form of the cut: a marked source word is accepted exactly
when its lift is trivial in the finite presentation. -/
theorem input_mem_cutting_iff {X : Type} (R : Set (FreeGroup X))
    (words : Source →* FreeGroup X) (f : Source) :
    inputHom words f ∈ cuttingSubgroup R ↔ quotientHom R (words f) = 1 := by
  rw [inputHom_apply, cuttingSubgroup, Subgroup.mem_prod]
  simp only [Subgroup.mem_top, true_and]
  rw [Mikhailova.mem_freeSubgroup_iff_quotient_eq]
  change quotientHom R (words f) = quotientHom R 1 ↔
    quotientHom R (words f) = 1
  simp only [map_one]

/-- **Exact rank-three cut.**  The cutting subgroup pulls back to the kernel
of the marked quotient map. -/
theorem comap_cutting_eq_kernel {X : Type} (R : Set (FreeGroup X))
    (words : Source →* FreeGroup X) :
    (cuttingSubgroup R).comap (inputHom words) =
      ((quotientHom R).comp words).ker := by
  ext f
  rw [Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact input_mem_cutting_iff R words f

/-- The same exact cut as an intersection inside the product ambient group. -/
theorem range_inf_cutting_eq_kernel_map {X : Type}
    (R : Set (FreeGroup X)) (words : Source →* FreeGroup X) :
    (inputHom words).range ⊓ cuttingSubgroup R =
      ((quotientHom R).comp words).ker.map (inputHom words) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hrange, hcut⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨f, hf⟩ := hrange
    refine Subgroup.mem_map.mpr ⟨f, ?_, hf⟩
    rw [← comap_cutting_eq_kernel R words]
    exact Subgroup.mem_comap.mpr (hf ▸ hcut)
  · intro hx
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_inf.mpr ⟨⟨f, rfl⟩, ?_⟩
    rw [comap_cutting_eq_kernel R words] at hf
    exact Subgroup.mem_comap.mp hf

/-- Finite target alphabet and relator data make the displayed cutting
subgroup finitely generated. -/
theorem cuttingSubgroup_fg {X : Type} [Finite X]
    {R : Set (FreeGroup X)} (hR : R.Finite) :
    (cuttingSubgroup R).FG := by
  letI : Group.FG Source := fg_of_isFinitelyPresented Source
  exact fg_prod fg_top (Mikhailova.freeSubgroup_fg hR)

/-- The concrete Mikhailova benign witness for the kernel of a marked map. -/
def kernelWitness {X : Type} [Finite X]
    {R : Set (FreeGroup X)} (hR : R.Finite)
    (words : Source →* FreeGroup X) :
    BenignWitness (((quotientHom R).comp words).ker) where
  K := Ambient X
  emb := inputHom words
  emb_injective := inputHom_injective words
  L := cuttingSubgroup R
  L_fg := cuttingSubgroup_fg hR
  comap_eq := comap_cutting_eq_kernel R words

/-! ## Consuming an explicit marked embedding -/

/-- An injective marked map between presented quotients identifies the kernel
of its chosen word lifts with the source normal closure. -/
theorem kernel_eq_normalClosure_of_markedEmbedding
    {X : Type} (S : Set Source) (R : Set (FreeGroup X))
    (words : Source →* FreeGroup X) (i : PresentedGroup S →* PresentedGroup R)
    (hi : Function.Injective i)
    (hcomm : (quotientHom R).comp words = i.comp (quotientHom S)) :
    ((quotientHom R).comp words).ker = Subgroup.normalClosure S := by
  ext f
  constructor
  · intro hf
    have hvalue : i (quotientHom S f) = 1 := by
      have hpoint := DFunLike.congr_fun hcomm f
      rw [MonoidHom.mem_ker.mp hf] at hpoint
      exact hpoint.symm
    have hsource : quotientHom S f = 1 := by
      apply hi
      simpa only [map_one] using hvalue
    exact (QuotientGroup.eq_one_iff _).mp hsource
  · intro hf
    apply MonoidHom.mem_ker.mpr
    have hsource : quotientHom S f = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hf
    have hpoint := DFunLike.congr_fun hcomm f
    simp only [MonoidHom.comp_apply, hsource, map_one] at hpoint
    exact hpoint

/-- **Concrete benign compiler checkpoint.**  Finite marked embedding data
produce a genuine benign witness cutting out the source relator kernel. -/
def normalClosureWitnessOfMarkedEmbedding
    {X : Type} [Finite X] (S : Set Source) {R : Set (FreeGroup X)}
    (hR : R.Finite) (words : Source →* FreeGroup X)
    (i : PresentedGroup S →* PresentedGroup R) (hi : Function.Injective i)
    (hcomm : (quotientHom R).comp words = i.comp (quotientHom S)) :
    BenignWitness (Subgroup.normalClosure S) where
  K := Ambient X
  emb := inputHom words
  emb_injective := inputHom_injective words
  L := cuttingSubgroup R
  L_fg := cuttingSubgroup_fg hR
  comap_eq := (comap_cutting_eq_kernel R words).trans
    (kernel_eq_normalClosure_of_markedEmbedding S R words i hi hcomm)

/-- The marked-embedding version of the exact ambient intersection. -/
theorem range_inf_cutting_eq_normalClosure_map
    {X : Type} (S : Set Source) (R : Set (FreeGroup X))
    (words : Source →* FreeGroup X) (i : PresentedGroup S →* PresentedGroup R)
    (hi : Function.Injective i)
    (hcomm : (quotientHom R).comp words = i.comp (quotientHom S)) :
    (inputHom words).range ⊓ cuttingSubgroup R =
      (Subgroup.normalClosure S).map (inputHom words) := by
  rw [range_inf_cutting_eq_kernel_map,
    kernel_eq_normalClosure_of_markedEmbedding S R words i hi hcomm]

end MikhailovaRankThree
end Higman
end GroupApproximation
