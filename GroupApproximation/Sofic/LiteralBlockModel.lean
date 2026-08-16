import GroupApproximation.Sofic.GraphCliffordLamp
import GroupApproximation.Sofic.LiteralBaseAffineQuotient

/-!
# The block model of the literal forty-one-relator group

`docs/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md` computes the group
`E` of Definition `def:E` as a split extension

    E  =  N_E ⋊ V ,     N_E = the Clifford group of the marked orbital graph,

where `V` is the ascending HNN extension of the base along the doubling
endomorphism, the sites are the cosets `V/B`, and two sites are joined by an
edge exactly when they form a `V`-translate of the marked pair
`{τo, v₁τo}`.  This file builds that target group and the homomorphism into
it from the literal presentation, checking all forty-one displayed relators.

## What is and is not built here

Everything below is unconditional.  In particular `V` is the **presented**
ascending HNN group, not `ℤ[1/2]³ ⋊ SL₃(ℤ)` and not a matrix group, and the
lamp factor braids on the **adjacency** relation, not on membership of a
common block.  Both choices are forced, and for the same reason: the
identification of the literal base with `ℤ³ ⋊ SL₃(ℤ)` — the artifact's input
(I1), a literature premise (`rem:classical-base`, \cite{CRW} Theorem 2) that
this repository deliberately does not own — is exactly what would be needed
to replace either by its concrete counterpart.  Concretely, Proposition 4.2
of the artifact (blocks are copies of `K₈`, so "same block" and "adjacent"
agree off the diagonal) rests on (I1); braiding on blocks would therefore
impose relations that are not known to hold in `E`.

`Block` and the fibring `blockOf : Site → Block` are nonetheless built and
shown to be `V`-equivariant and coarser than adjacency
(`blockOf_eq_of_adjacent`), because the block decomposition is what the
soficity argument consumes.  No claim is made here that a fibre has eight
elements or that a block is a clique.

## The route

* `Vertical` is presented on the literal eight-letter alphabet by the twenty
  transported base relators, the six stable-letter relators, and the lamp
  letter itself — that is, it is the literal presentation with `c` killed.
  Using the same alphabet costs nothing and makes `embedBaseWord`,
  `stableRelator` and `compressedBaseWord` reusable verbatim.  Its universal
  property is packaged as `verticalToGroup`.
* `Site := Vertical ⧸ baseSubgroup`, with `baseSubgroup` the image of the
  literal base; `markedSiteA := t·o` and `markedSiteB := v₁t·o`.
* The two marked sites are **distinct**, and this is the only place where the
  exact affine matrix model of `ExplicitLinearModel` is used: `verticalWitness`
  maps `Vertical` to the concrete telescope, under which coincidence of the
  marked sites would put `τ⁻¹v̄₁τ` in the base copy, contradicting
  `v1G_not_mem_range`.  The matrix model is a separator, never a carrier —
  the same discipline as `LiteralNonMFLinearWitness.literal_mark_ne_one`.
* `Adjacent` is the `V`-orbit of the unordered marked pair; `Lamps` is the
  Clifford group of that graph, `Model := Lamps ⋊ Vertical`.
* `toModel` is obtained from `LiteralNonMFPresentation.Realization`, so every
  one of the forty-one relators is discharged: the twenty base relators
  through `baseRelators_kill_baseLetter`, the six stable relators through
  `stableLetter_conj`, `c²` and the six `[c,g]` through `lampModel_sq` and
  `lampModel_root_commute_base`, and the eight centrality relators through
  `marked_word_eq_signModel` — the marked word is the central Clifford sign,
  because the marked pair is adjacent by construction and distinct by the
  witness above.
-/

namespace GroupApproximation
namespace LiteralBlockModel

open LiteralNonMFPresentation ExplicitLinearModel LiteralNonMFLinearWitness
open LiteralBaseAffineQuotient
open scoped commutatorElement

noncomputable section

/-! ## The vertical group

`Vertical` is the literal presentation with the lamp letter killed: the
ascending HNN extension of the literal base along the doubling map. -/

/-- The relators of the vertical group: the transported base relators, the
stable-letter relators, and the lamp letter. -/
def verticalRelators : Set (FreeGroup Generator) :=
  (transportedBaseRelators : Set (FreeGroup Generator)) ∪
    (stableRelators : Set (FreeGroup Generator)) ∪ {lampWord}

theorem mem_verticalRelators_of_transported {r : FreeGroup Generator}
    (h : r ∈ transportedBaseRelators) : r ∈ verticalRelators := by
  simp only [verticalRelators, Set.mem_union, Finset.mem_coe,
    Set.mem_singleton_iff]
  exact Or.inl (Or.inl h)

theorem mem_verticalRelators_of_stable {r : FreeGroup Generator}
    (h : r ∈ stableRelators) : r ∈ verticalRelators := by
  simp only [verticalRelators, Set.mem_union, Finset.mem_coe,
    Set.mem_singleton_iff]
  exact Or.inl (Or.inr h)

theorem lampWord_mem_verticalRelators : lampWord ∈ verticalRelators :=
  Set.mem_union_right _ rfl

/-- The vertical group `V`, the literal presentation with the lamp killed. -/
abbrev Vertical : Type := PresentedGroup verticalRelators

abbrev wordInVertical : FreeGroup Generator →* Vertical :=
  PresentedGroup.mk verticalRelators

/-- The image of a base letter in the vertical group. -/
def baseLetter (i : BaseGenerator) : Vertical :=
  PresentedGroup.of (Generator.base i)

/-- The stable letter of the vertical group. -/
def stableLetter : Vertical := PresentedGroup.of Generator.stable

/-- The lamp letter, which the vertical relators kill. -/
def lampLetter : Vertical := PresentedGroup.of Generator.lamp

@[simp] theorem lampLetter_eq_one : lampLetter = 1 := by
  have h : wordInVertical lampWord = 1 :=
    PresentedGroup.one_of_mem lampWord_mem_verticalRelators
  exact h

/-- Free evaluation at the base letters is the quotient map applied to the
embedded word. -/
theorem lift_baseLetter (w : FreeGroup BaseGenerator) :
    FreeGroup.lift baseLetter w = wordInVertical (embedBaseWord w) := by
  change (FreeGroup.lift baseLetter) w =
    (wordInVertical.comp embedBaseWord) w
  apply freeGroup_hom_eq_on_generators
  intro i
  show FreeGroup.lift baseLetter (FreeGroup.of i) =
    wordInVertical (embedBaseWord (FreeGroup.of i))
  have hof : embedBaseWord (FreeGroup.of i) = vertexLetter i := by
    rw [embedBaseWord, FreeGroup.lift_apply_of]
  rw [FreeGroup.lift_apply_of, hof]
  rfl

/-- The twenty displayed base relators die in the vertical group. -/
theorem baseRelators_kill_baseLetter :
    ∀ r ∈ baseRelators, FreeGroup.lift baseLetter r = 1 := by
  intro r hr
  rw [lift_baseLetter]
  apply PresentedGroup.one_of_mem
  apply mem_verticalRelators_of_transported
  exact Finset.mem_image.mpr ⟨r, hr, rfl⟩

/-- The canonical map from the literal base into the vertical group. -/
def baseMapV : Base →* Vertical :=
  PresentedGroup.toGroup (f := baseLetter)
    (fun r hr => baseRelators_kill_baseLetter r (Finset.mem_coe.mp hr))

@[simp] theorem baseMapV_generator (i : BaseGenerator) :
    baseMapV (PresentedGroup.of i) = baseLetter i := by
  exact PresentedGroup.toGroup.of _

/-- The six displayed stable-letter relations, realised in the vertical
group. -/
theorem stableLetter_conj (i : BaseGenerator) :
    stableLetter * baseLetter i * stableLetter⁻¹ =
      FreeGroup.lift baseLetter (compressedBaseWord i) := by
  have hrel : wordInVertical (stableRelator i) = 1 := by
    apply PresentedGroup.one_of_mem
    apply mem_verticalRelators_of_stable
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  simp only [stableRelator, map_mul, map_inv] at hrel
  have hcomp : wordInVertical (compressedGeneratorWord i) =
      FreeGroup.lift baseLetter (compressedBaseWord i) :=
    (lift_baseLetter (compressedBaseWord i)).symm
  rw [← hcomp]
  exact mul_inv_eq_one.mp hrel

/-! ## The universal property of the vertical group -/

/-- **Universal property of the vertical group.**  A family of images of the
eight letters that satisfies the twenty base relations, implements the
doubling map by conjugation with the stable image, and kills the lamp letter
determines a homomorphism out of `V`. -/
def verticalToGroup {G : Type*} [Group G] (f : Generator → G)
    (hbase : ∀ r ∈ baseRelators,
      FreeGroup.lift (fun i => f (Generator.base i)) r = 1)
    (hstable : ∀ i : BaseGenerator,
      f Generator.stable * f (Generator.base i) * (f Generator.stable)⁻¹ =
        FreeGroup.lift (fun i => f (Generator.base i)) (compressedBaseWord i))
    (hlamp : f Generator.lamp = 1) : Vertical →* G := by
  apply PresentedGroup.toGroup (f := f)
  intro r hr
  simp only [verticalRelators, Set.mem_union, Finset.mem_coe,
    Set.mem_singleton_iff] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    rw [lift_embedBaseWord]
    exact hbase q hq
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
    simp only [stableRelator, map_mul, map_inv]
    rw [show FreeGroup.lift f stableWord = f Generator.stable by
        simp [stableWord],
      show FreeGroup.lift f (vertexLetter i) = f (Generator.base i) by
        simp [vertexLetter],
      compressedGeneratorWord, lift_embedBaseWord]
    exact mul_inv_eq_one.mpr (hstable i)
  · subst hr
    show FreeGroup.lift f (FreeGroup.of Generator.lamp) = 1
    rw [FreeGroup.lift_apply_of]
    exact hlamp

@[simp] theorem verticalToGroup_baseLetter {G : Type*} [Group G]
    (f : Generator → G)
    (hbase : ∀ r ∈ baseRelators,
      FreeGroup.lift (fun i => f (Generator.base i)) r = 1)
    (hstable : ∀ i : BaseGenerator,
      f Generator.stable * f (Generator.base i) * (f Generator.stable)⁻¹ =
        FreeGroup.lift (fun i => f (Generator.base i)) (compressedBaseWord i))
    (hlamp : f Generator.lamp = 1) (i : BaseGenerator) :
    verticalToGroup f hbase hstable hlamp (baseLetter i) =
      f (Generator.base i) := by
  exact PresentedGroup.toGroup.of _

@[simp] theorem verticalToGroup_stableLetter {G : Type*} [Group G]
    (f : Generator → G)
    (hbase : ∀ r ∈ baseRelators,
      FreeGroup.lift (fun i => f (Generator.base i)) r = 1)
    (hstable : ∀ i : BaseGenerator,
      f Generator.stable * f (Generator.base i) * (f Generator.stable)⁻¹ =
        FreeGroup.lift (fun i => f (Generator.base i)) (compressedBaseWord i))
    (hlamp : f Generator.lamp = 1) :
    verticalToGroup f hbase hstable hlamp stableLetter =
      f Generator.stable := by
  exact PresentedGroup.toGroup.of _

/-! ## Sites -/

/-- The image of the literal base in the vertical group: the site
stabiliser. -/
abbrev baseSubgroup : Subgroup Vertical := baseMapV.range

/-- Sites: the coset space `X = V/B`. -/
abbrev Site : Type := Vertical ⧸ baseSubgroup

/-- The root site `o = B`. -/
def rootSite : Site := QuotientGroup.mk 1

theorem smul_rootSite (v : Vertical) :
    v • rootSite = QuotientGroup.mk v := by
  show v • (QuotientGroup.mk 1 : Vertical ⧸ baseSubgroup) =
    QuotientGroup.mk v
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

/-- The base copy fixes the root site. -/
theorem baseMapV_smul_rootSite (b : Base) :
    baseMapV b • rootSite = rootSite := by
  rw [smul_rootSite]
  show (QuotientGroup.mk (baseMapV b) : Site) = QuotientGroup.mk 1
  rw [QuotientGroup.eq, mul_one]
  apply Subgroup.inv_mem
  exact ⟨b, rfl⟩

theorem baseSubgroup_smul_rootSite {v : Vertical} (hv : v ∈ baseSubgroup) :
    v • rootSite = rootSite := by
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hv
  exact baseMapV_smul_rootSite b

/-- The first marked site `a = τo`. -/
def markedSiteA : Site := stableLetter • rootSite

/-- The second marked site `b = v₁τo`. -/
def markedSiteB : Site := (baseLetter v1Index * stableLetter) • rootSite

theorem markedSiteA_eq : markedSiteA = QuotientGroup.mk stableLetter :=
  smul_rootSite _

theorem markedSiteB_eq :
    markedSiteB = QuotientGroup.mk (baseLetter v1Index * stableLetter) :=
  smul_rootSite _

/-! ## The affine separator

The exact affine matrix model enters here and nowhere else, and only to
separate the two marked sites. -/

/-- The concrete telescope-by-`ℤ` group over the exact affine matrix base. -/
abbrev MatrixVertical : Type := MarkedCompression.Vertical alpha conjD_injective

/-- Images of the eight letters in the concrete telescope: the base letters
go to the affine matrices, the stable letter to the shift, the lamp dies. -/
def verticalWitnessGenerator : Generator → MatrixVertical
  | .inl i =>
      MarkedCompression.iotaVertical alpha conjD_injective
        (matrixBaseGenerator i)
  | .inr j =>
      if j = 0 then MarkedCompression.tVertical alpha conjD_injective else 1

@[simp] theorem verticalWitnessGenerator_base (i : BaseGenerator) :
    verticalWitnessGenerator (Generator.base i) =
      MarkedCompression.iotaVertical alpha conjD_injective
        (matrixBaseGenerator i) := rfl

@[simp] theorem verticalWitnessGenerator_stable :
    verticalWitnessGenerator Generator.stable =
      MarkedCompression.tVertical alpha conjD_injective := by
  simp [verticalWitnessGenerator]

@[simp] theorem verticalWitnessGenerator_lamp :
    verticalWitnessGenerator Generator.lamp = 1 := by
  simp [verticalWitnessGenerator]

theorem lift_iotaVertical_matrixBase (q : FreeGroup BaseGenerator) :
    FreeGroup.lift (fun i =>
        MarkedCompression.iotaVertical alpha conjD_injective
          (matrixBaseGenerator i)) q =
      MarkedCompression.iotaVertical alpha conjD_injective
        (FreeGroup.lift matrixBaseGenerator q) := by
  change (FreeGroup.lift (fun i =>
      MarkedCompression.iotaVertical alpha conjD_injective
        (matrixBaseGenerator i))) q =
    ((MarkedCompression.iotaVertical alpha conjD_injective).comp
      (FreeGroup.lift matrixBaseGenerator)) q
  apply freeGroup_hom_eq_on_generators
  intro i
  simp

/-- The comparison map from the presented vertical group to the concrete
affine telescope. -/
def verticalWitness : Vertical →* MatrixVertical :=
  verticalToGroup verticalWitnessGenerator
    (by
      intro r hr
      simp only [verticalWitnessGenerator_base]
      rw [lift_iotaVertical_matrixBase, matrixBaseGenerator_kills r hr,
        map_one])
    (by
      intro i
      simp only [verticalWitnessGenerator_base, verticalWitnessGenerator_stable]
      rw [MarkedCompression.vertical_compress, conjD_matrixBaseGenerator,
        lift_iotaVertical_matrixBase])
    verticalWitnessGenerator_lamp

@[simp] theorem verticalWitness_baseLetter (i : BaseGenerator) :
    verticalWitness (baseLetter i) =
      MarkedCompression.iotaVertical alpha conjD_injective
        (matrixBaseGenerator i) := by
  rw [verticalWitness, verticalToGroup_baseLetter,
    verticalWitnessGenerator_base]

@[simp] theorem verticalWitness_stableLetter :
    verticalWitness stableLetter =
      MarkedCompression.tVertical alpha conjD_injective := by
  rw [verticalWitness, verticalToGroup_stableLetter,
    verticalWitnessGenerator_stable]

theorem verticalWitness_baseMapV (b : Base) :
    verticalWitness (baseMapV b) =
      MarkedCompression.iotaVertical alpha conjD_injective
        (affineQuotient b) := by
  have h : verticalWitness.comp baseMapV =
      (MarkedCompression.iotaVertical alpha conjD_injective).comp
        affineQuotient := by
    apply PresentedGroup.ext
    intro i
    show verticalWitness (baseMapV (PresentedGroup.of i)) =
      MarkedCompression.iotaVertical alpha conjD_injective
        (affineQuotient (PresentedGroup.of i))
    rw [baseMapV_generator, verticalWitness_baseLetter,
      affineQuotient_generator]
  exact DFunLike.congr_fun h b

/-- **The two marked sites are distinct.**  Coincidence would put the
`τ`-conjugate of `v̄₁` inside the level-zero base copy of the concrete affine
telescope, which `lem:linear` forbids.  This is the only use of the matrix
model in this file. -/
theorem markedSiteA_ne_markedSiteB : markedSiteA ≠ markedSiteB := by
  intro h
  rw [markedSiteA_eq, markedSiteB_eq, QuotientGroup.eq] at h
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp h
  apply MarkedCompression.tVertical_inv_conj_not_mem alpha conjD_injective
    v1G_not_mem_range
  refine ⟨affineQuotient b, ?_⟩
  have hw := congrArg verticalWitness hb
  rw [verticalWitness_baseMapV, map_mul, map_mul, map_inv,
    verticalWitness_stableLetter, verticalWitness_baseLetter,
    matrixBaseGenerator_v1] at hw
  rw [hw]
  group

/-! ## The marked orbital graph -/

/-- Two sites are adjacent when they form a `V`-translate of the unordered
marked pair `{τo, v₁τo}`.  This is the orbital graph `𝒢` of §3 of the
structure artifact. -/
def Adjacent (s s' : Site) : Prop :=
  ∃ g : Vertical,
    (s = g • markedSiteA ∧ s' = g • markedSiteB) ∨
      (s = g • markedSiteB ∧ s' = g • markedSiteA)

theorem adjacent_markedPair : Adjacent markedSiteA markedSiteB :=
  ⟨1, Or.inl ⟨(one_smul _ _).symm, (one_smul _ _).symm⟩⟩

theorem adjacent_symm {s s' : Site} (h : Adjacent s s') : Adjacent s' s := by
  obtain ⟨g, hg | hg⟩ := h
  · exact ⟨g, Or.inr ⟨hg.2, hg.1⟩⟩
  · exact ⟨g, Or.inl ⟨hg.2, hg.1⟩⟩

theorem adjacent_smul (v : Vertical) {s s' : Site} (h : Adjacent s s') :
    Adjacent (v • s) (v • s') := by
  obtain ⟨g, hg | hg⟩ := h
  · exact ⟨v * g, Or.inl
      ⟨by rw [hg.1, mul_smul], by rw [hg.2, mul_smul]⟩⟩
  · exact ⟨v * g, Or.inr
      ⟨by rw [hg.1, mul_smul], by rw [hg.2, mul_smul]⟩⟩

theorem vertical_preservesAdj :
    GraphCliffordLamp.PreservesAdj Adjacent Vertical :=
  fun v _ _ h => adjacent_smul v h

/-! ## Blocks

The block of a site is its class modulo the subgroup generated by the base
copy and the transporter of the marked pair.  Adjacent sites lie in a common
block; the converse is Proposition 4.2 of the structure artifact and is *not*
claimed, since its proof consumes the literature identification of the
base. -/

/-- The block stabiliser `B₁`: the base copy together with the transporter of
the marked pair. -/
def blockSubgroup : Subgroup Vertical :=
  Subgroup.closure ((baseSubgroup : Set Vertical) ∪
    {stableLetter⁻¹ * baseLetter v1Index * stableLetter})

theorem baseSubgroup_le_blockSubgroup : baseSubgroup ≤ blockSubgroup := by
  intro v hv
  exact Subgroup.subset_closure (Or.inl hv)

theorem markedTransporter_mem_blockSubgroup :
    stableLetter⁻¹ * baseLetter v1Index * stableLetter ∈ blockSubgroup :=
  Subgroup.subset_closure (Or.inr rfl)

/-- Blocks: the coset space `I = V/B₁`. -/
abbrev Block : Type := Vertical ⧸ blockSubgroup

/-- The fibring of sites over blocks. -/
def blockOf : Site → Block :=
  Quotient.map' id (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    rw [QuotientGroup.leftRel_apply] at hab
    exact baseSubgroup_le_blockSubgroup hab)

@[simp] theorem blockOf_mk (v : Vertical) :
    blockOf (QuotientGroup.mk v : Site) = (QuotientGroup.mk v : Block) := rfl

theorem blockOf_smul (v : Vertical) (s : Site) :
    blockOf (v • s) = v • blockOf s := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
  rw [MulAction.Quotient.smul_mk, blockOf_mk, blockOf_mk,
    MulAction.Quotient.smul_mk]

/-- The marked pair lies in one block. -/
theorem blockOf_marked : blockOf markedSiteA = blockOf markedSiteB := by
  rw [markedSiteA_eq, markedSiteB_eq, blockOf_mk, blockOf_mk,
    QuotientGroup.eq]
  have hassoc : stableLetter⁻¹ * (baseLetter v1Index * stableLetter) =
      stableLetter⁻¹ * baseLetter v1Index * stableLetter := by
    group
  rw [hassoc]
  exact markedTransporter_mem_blockSubgroup

/-- **Adjacent sites lie in a common block.**  The converse — that a block is
a clique — is Proposition 4.2 of the structure artifact and is conditional on
the identification of the literal base; it is not claimed anywhere here. -/
theorem blockOf_eq_of_adjacent {s s' : Site} (h : Adjacent s s') :
    blockOf s = blockOf s' := by
  obtain ⟨g, hg | hg⟩ := h
  · rw [hg.1, hg.2, blockOf_smul, blockOf_smul, blockOf_marked]
  · rw [hg.1, hg.2, blockOf_smul, blockOf_smul, blockOf_marked]

/-! ## The model -/

/-- The lamp factor: the Clifford group of the marked orbital graph. -/
abbrev Lamps : Type := GraphCliffordLamp.GraphClifford Adjacent

/-- The vertical group permutes the sites, hence acts on the lamp factor. -/
def lampAction : Vertical →* MulAut Lamps :=
  GraphCliffordLamp.smulHom Adjacent vertical_preservesAdj

theorem lampAction_apply_lamp (v : Vertical) (s : Site) :
    lampAction v (GraphCliffordLamp.lamp Adjacent s) =
      GraphCliffordLamp.lamp Adjacent (v • s) :=
  GraphCliffordLamp.smulHom_apply_lamp Adjacent vertical_preservesAdj v s

theorem lampAction_apply_sign (v : Vertical) :
    lampAction v (GraphCliffordLamp.sign Adjacent) =
      GraphCliffordLamp.sign Adjacent :=
  GraphCliffordLamp.smulHom_apply_sign Adjacent vertical_preservesAdj v

/-- **The block model of the literal group.** -/
abbrev Model : Type := Lamps ⋊[lampAction] Vertical

/-- The central sign `ζ = w` of the model. -/
def signModel : Model :=
  SemidirectProduct.inl (GraphCliffordLamp.sign Adjacent)

/-- The lamp at a site. -/
def lampModel (s : Site) : Model :=
  SemidirectProduct.inl (GraphCliffordLamp.lamp Adjacent s)

/-- The stable letter of the model. -/
def tModel : Model := SemidirectProduct.inr stableLetter

/-- The base letters of the model. -/
def baseModel (i : BaseGenerator) : Model :=
  SemidirectProduct.inr (baseLetter i)

theorem conj_lampModel (v : Vertical) (s : Site) :
    (SemidirectProduct.inr v : Model) * lampModel s *
        (SemidirectProduct.inr v)⁻¹ = lampModel (v • s) := by
  show (SemidirectProduct.inr v : Model) *
      SemidirectProduct.inl (GraphCliffordLamp.lamp Adjacent s) *
      (SemidirectProduct.inr v)⁻¹ =
    SemidirectProduct.inl (GraphCliffordLamp.lamp Adjacent (v • s))
  rw [← map_inv, ← SemidirectProduct.inl_aut, lampAction_apply_lamp]

theorem lampModel_sq (s : Site) : lampModel s ^ 2 = 1 := by
  show (SemidirectProduct.inl (GraphCliffordLamp.lamp Adjacent s) : Model) ^ 2
    = 1
  rw [← map_pow, GraphCliffordLamp.lamp_sq, map_one]

theorem signModel_sq : signModel ^ 2 = 1 := by
  show (SemidirectProduct.inl (GraphCliffordLamp.sign Adjacent) : Model) ^ 2
    = 1
  rw [← map_pow, GraphCliffordLamp.sign_sq, map_one]

/-- The sign is central in the model. -/
theorem signModel_central (g : Model) : Commute signModel g := by
  obtain ⟨n, v⟩ := g
  show signModel * ⟨n, v⟩ = ⟨n, v⟩ * signModel
  show (⟨GraphCliffordLamp.sign Adjacent, 1⟩ : Model) * ⟨n, v⟩ =
    ⟨n, v⟩ * ⟨GraphCliffordLamp.sign Adjacent, 1⟩
  apply SemidirectProduct.ext
  · show GraphCliffordLamp.sign Adjacent * lampAction 1 n =
      n * lampAction v (GraphCliffordLamp.sign Adjacent)
    rw [map_one, lampAction_apply_sign]
    show GraphCliffordLamp.sign Adjacent * n =
      n * GraphCliffordLamp.sign Adjacent
    exact (GraphCliffordLamp.sign_commute Adjacent n).eq
  · simp only [SemidirectProduct.mul_right, one_mul, mul_one]

/-- The sign survives in the model. -/
theorem signModel_ne_one : signModel ≠ 1 := by
  intro h
  have h1 : GraphCliffordLamp.sign Adjacent = 1 := by
    apply (SemidirectProduct.inl_injective (N := Lamps) (G := Vertical))
    change (SemidirectProduct.inl (GraphCliffordLamp.sign Adjacent) : Model) =
      SemidirectProduct.inl 1
    change signModel = SemidirectProduct.inl 1
    rw [h, map_one]
  exact GraphCliffordLamp.sign_ne_one Adjacent h1

/-- The root lamp is centralised by the base copy, which fixes the root
site. -/
theorem lampModel_root_commute_base (v : Vertical) (hv : v ∈ baseSubgroup) :
    Commute (lampModel rootSite) (SemidirectProduct.inr v : Model) := by
  have h : (SemidirectProduct.inr v : Model) * lampModel rootSite *
      (SemidirectProduct.inr v)⁻¹ = lampModel rootSite := by
    rw [conj_lampModel, baseSubgroup_smul_rootSite hv]
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

/-- **The marked word is the central Clifford sign of the model.**  The two
marked sites are adjacent by construction and distinct by
`markedSiteA_ne_markedSiteB`, so the braiding relation applies to them. -/
theorem marked_word_eq_signModel :
    markedCompressionWord tModel (baseModel v1Index) (lampModel rootSite) =
      signModel := by
  have hd : tModel * lampModel rootSite * tModel⁻¹ = lampModel markedSiteA :=
    conj_lampModel stableLetter rootSite
  have had : baseModel v1Index * lampModel markedSiteA *
      (baseModel v1Index)⁻¹ = lampModel markedSiteB := by
    have h := conj_lampModel (baseLetter v1Index) (stableLetter • rootSite)
    rwa [smul_smul] at h
  have hcomm : ⁅lampModel markedSiteA, lampModel markedSiteB⁆ = signModel := by
    show ⁅(SemidirectProduct.inl
          (GraphCliffordLamp.lamp Adjacent markedSiteA) : Model),
        SemidirectProduct.inl
          (GraphCliffordLamp.lamp Adjacent markedSiteB)⁆ =
      SemidirectProduct.inl (GraphCliffordLamp.sign Adjacent)
    rw [← map_commutatorElement,
      GraphCliffordLamp.commutator_lamp_lamp Adjacent
        markedSiteA_ne_markedSiteB adjacent_markedPair]
  rw [markedCompressionWord, hd, had, hcomm]

/-! ## The homomorphism from the literal presentation -/

theorem lift_baseModel (q : FreeGroup BaseGenerator) :
    FreeGroup.lift baseModel q =
      SemidirectProduct.inr (FreeGroup.lift baseLetter q) := by
  change (FreeGroup.lift baseModel) q =
    ((SemidirectProduct.inr : Vertical →* Model).comp
      (FreeGroup.lift baseLetter)) q
  apply freeGroup_hom_eq_on_generators
  intro i
  show FreeGroup.lift baseModel (FreeGroup.of i) =
    SemidirectProduct.inr (FreeGroup.lift baseLetter (FreeGroup.of i))
  simp [baseModel]

/-- The model realizes every one of the forty-one displayed relators. -/
def modelRealization : Realization Model where
  baseGenerator := baseModel
  stable := tModel
  lamp := lampModel rootSite
  base_relations := by
    intro r hr
    rw [lift_baseModel, baseRelators_kill_baseLetter r hr, map_one]
  stable_relations i := by
    rw [lift_baseModel]
    show (SemidirectProduct.inr stableLetter : Model) *
        SemidirectProduct.inr (baseLetter i) *
        (SemidirectProduct.inr stableLetter)⁻¹ =
      SemidirectProduct.inr (FreeGroup.lift baseLetter (compressedBaseWord i))
    rw [← map_inv, ← map_mul, ← map_mul, stableLetter_conj]
  lamp_sq := lampModel_sq rootSite
  lamp_centralizes_base i :=
    lampModel_root_commute_base (baseLetter i)
      ⟨PresentedGroup.of i, baseMapV_generator i⟩
  marked_central g := by
    rw [marked_word_eq_signModel]
    exact signModel_central g

/-- **The literal eight-generator presentation maps to its block model.**
All forty-one displayed relators are discharged: the twenty base relators,
the six stable-letter relators, `c²`, the six lamp commutators, and the eight
centrality relators for the marked word. -/
def toModel : MarkedGroup →* Model := realizationHom modelRealization

theorem modelRealization_marked_word :
    markedCompressionWord modelRealization.stable
        (modelRealization.baseGenerator v1Index) modelRealization.lamp =
      signModel :=
  marked_word_eq_signModel

@[simp] theorem toModel_mark : toModel mark = signModel := by
  rw [toModel, realizationHom_mark, modelRealization_marked_word]

@[simp] theorem toModel_stable : toModel stable = tModel := by
  simp [toModel, modelRealization]

@[simp] theorem toModel_lamp : toModel lamp = lampModel rootSite := by
  simp [toModel, modelRealization]

theorem toModel_base_generator (i : BaseGenerator) :
    toModel (baseMap (PresentedGroup.of i)) = baseModel i := by
  rw [toModel, realizationHom_base_generator]
  rfl

theorem toModel_comp_baseMap :
    toModel.comp baseMap =
      (SemidirectProduct.inr : Vertical →* Model).comp baseMapV := by
  apply PresentedGroup.ext
  intro i
  show toModel (baseMap (PresentedGroup.of i)) =
    SemidirectProduct.inr (baseMapV (PresentedGroup.of i))
  rw [toModel_base_generator, baseMapV_generator]
  rfl

@[simp] theorem toModel_baseMap (g : Base) :
    toModel (baseMap g) = SemidirectProduct.inr (baseMapV g) :=
  DFunLike.congr_fun toModel_comp_baseMap g

/-! ## Surjectivity -/

theorem inr_mem_toModel_range (v : Vertical) :
    (SemidirectProduct.inr v : Model) ∈ toModel.range := by
  have hcases : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  apply PresentedGroup.generated_by verticalRelators
    (toModel.range.comap (SemidirectProduct.inr : Vertical →* Model))
  intro j
  rw [Subgroup.mem_comap]
  match j with
  | Sum.inl i =>
      exact ⟨baseMap (PresentedGroup.of i), toModel_base_generator i⟩
  | Sum.inr k =>
      rcases hcases k with rfl | rfl
      · exact ⟨stable, toModel_stable⟩
      · have h1 : (PresentedGroup.of (Sum.inr 1) : Vertical) = 1 :=
          lampLetter_eq_one
        rw [h1, map_one]
        exact Subgroup.one_mem _

theorem lampModel_mem_toModel_range (s : Site) :
    lampModel s ∈ toModel.range := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective s
  rw [← smul_rootSite, ← conj_lampModel]
  exact toModel.range.mul_mem
    (toModel.range.mul_mem (inr_mem_toModel_range v) ⟨lamp, toModel_lamp⟩)
    (toModel.range.inv_mem (inr_mem_toModel_range v))

theorem inl_mem_toModel_range (n : Lamps) :
    (SemidirectProduct.inl n : Model) ∈ toModel.range := by
  apply GraphCliffordLamp.mem_subgroup_of_sign_mem_of_lamp_mem Adjacent
    (toModel.range.comap (SemidirectProduct.inl : Lamps →* Model))
  · exact ⟨mark, toModel_mark⟩
  · exact lampModel_mem_toModel_range

/-- **The block model is exactly the image of the literal presentation.** -/
theorem toModel_surjective : Function.Surjective toModel := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  exact toModel.range.mul_mem (inl_mem_toModel_range g.left)
    (inr_mem_toModel_range g.right)

/-! ## Consequences of surjectivity -/

instance : Countable Vertical :=
  (PresentedGroup.mk_surjective verticalRelators).countable

instance : Countable Site :=
  Function.Surjective.countable (Quotient.mk_surjective (α := Vertical))

/-- The block model is finitely generated, being the image of a finite
presentation. -/
theorem model_finitelyGenerated : Group.FG Model := by
  letI : Group.FG MarkedGroup :=
    Group.fg_of_surjective
      (PresentedGroup.mk_surjective
        (relators : Set (FreeGroup Generator)))
  exact Group.fg_of_surjective toModel_surjective

/-- The block-model package for the literal group: a surjection from the
literal forty-one-relator presentation onto a semidirect product of the
Clifford group of the marked orbital graph by the presented ascending HNN
group, carrying the marked word to a nontrivial central involution. -/
theorem literalBlockModelPackage :
    Function.Surjective toModel ∧
      toModel mark = signModel ∧
      signModel ≠ 1 ∧
      signModel ^ 2 = 1 ∧
      (∀ g : Model, Commute signModel g) :=
  ⟨toModel_surjective, toModel_mark, signModel_ne_one, signModel_sq,
    signModel_central⟩

end

end LiteralBlockModel
end GroupApproximation
