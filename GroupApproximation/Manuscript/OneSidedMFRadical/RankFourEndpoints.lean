import GroupApproximation.Leavitt.RankFourCompressors
import GroupApproximation.Leavitt.ElementaryNormalGeneration
import GroupApproximation.Leavitt.LeavittMarkNontrivial
import GroupApproximation.Steinberg.BinaryLeavitt
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Sofic.FullRadicalClosureProperties
import GroupApproximation.Sofic.SimpleFullMFRadical

/-!
# The exact rank-four endpoint: definitions and closed algebra

This module fixes the group used in `non_mf_groups_exist.tex`:

`H = EL₄(L_{𝔽₂}(1,2))`.

`thm:headline` names exactly this group, and the printed proof of
`thm:full-defect-ring` uses exactly four coordinates: "three for the subgroup
`EL₃(R)`, which has property (T) once `R` is replaced by a finitely generated
unital subring, and one for its centralizer."

The following clauses are closed here, at exactly this rank:

* `H` is countable, finitely generated, and has property `(T)`;
* the printed coefficient `q = 1 - s₀t₀ = s₁t₁` is nonzero;
* the printed defect `d = e₀₂(q)` is nontrivial; and
* `d` normally generates `H`.

Normal generation is `normalClosure_elementaryRoot_p1_eq_top`, which needs only
three indices and any ring carrying a binary Leavitt family; the rank-`≥ 5`
Hilbert-hotel route used by the superseded rank-twelve development is not
available here and is not needed.

The printed compressor `u = u₃u₂u₁` is already a literal word in twelve
elementary transvections in `Leavitt.RankFourCompressors`, so no block-frame
flattening is required at rank four: `RankFour.Ambient R` *is*
`EL₄(L_{𝔽₂}(1,2))`.  What this module names, and `RankFourConfiguration`
proves, is `PrintedDefectConfiguration`: that `u` compresses the upper-left
corner, that the printed diagonal mark `c` centralizes it, and that the printed
commutator is the defect.

Likewise this file names the exact simplicity proposition without reproving
it.  `RankFourSimplicity.manuscriptPropositionSimple` closes it
unconditionally via exhaustive direct root extraction and elementary-root
normal generation.

## Zero-based indices

The manuscript indexes coordinates `1,2,3,4`; Lean indexes them `0,1,2,3`.  The
printed `L = EL₃(R)` on coordinates `1,2,3` is `corner` on `0,1,2`; the printed
`c = [e₄₁(e), e₁₄(t)]` is `c = ⁅e₃₀(q), e₀₃(t₀)⁆`; the printed `ℓ = e₂₃(1)` is
`ell = e₁₂(1)`; and the printed `d = e₁₃(e)` is `defect = e₀₂(q)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankFourEndpoint

open scoped commutatorElement

/-- The coefficient ring `R = L_{𝔽₂}(1,2)` in the current manuscript. -/
abbrev R : Type := UniversalLeavitt.BinaryLeavittAlgebra

/-- Its canonical binary Leavitt family. -/
def leavittFamily : LeavittFamily R := UniversalLeavitt.family

/-- The exact group in `thm:headline`: `EL₄(L_{𝔽₂}(1,2))`. -/
noncomputable abbrev H : Type := BinaryLeavittSteinberg.ElementaryBase 4

/-- The printed complementary idempotent `e = 1 - s₀t₀ = s₁t₁`. -/
def q : R := leavittFamily.p1

/-- Two elementary roots at equal index pairs agree; the index proofs are
irrelevant.  This is the bridge between the printed numerals `0,1,2,3` and the
corner inclusion `RankFour.coreIndex` used by `Leavitt.RankFourCompressors`. -/
theorem elementaryRoot_congr {i j i' j' : Fin 4} (hij : i ≠ j) (hij' : i' ≠ j')
    (hi : i = i') (hj : j = j') (a : R) :
    elementaryRoot i j hij a = elementaryRoot i' j' hij' a := by
  subst hi
  subst hj
  rfl

/-- The printed defect `d = e₀₂(q)` as an element of `H`. -/
noncomputable def defect : H :=
  elementaryRoot (0 : Fin 4) 2 (by decide) q

/-- The printed coefficient is nonzero. -/
theorem q_ne_zero : q ≠ 0 := by
  exact leavittFamily.p1_ne_zero

/-- The printed elementary defect is nontrivial. -/
theorem defect_ne_one : defect ≠ 1 := by
  change elGen (0 : Fin 4) 2 (by decide) leavittFamily.p1 ≠ 1
  exact LeavittMark.elGen_p1_ne_one leavittFamily 0 2 (by decide)

/-- The rank-four index type has at least three indices, which is all the
normal-generation and simplicity theorems ask of it. -/
theorem three_le_card : 3 ≤ Fintype.card (Fin 4) := by norm_num

/-- **The normal-generation clause of `prop:defect`, closed at rank four.**
The proof is the general elementary-root normal-generation theorem over any
ring with a binary Leavitt family, which needs only three indices; the
rank-`≥ 5` Hilbert-hotel transport is not used. -/
theorem normalClosure_defect_eq_top :
    Subgroup.normalClosure ({defect} : Set H) = ⊤ := by
  simpa [defect, q] using
    (normalClosure_elementaryRoot_p1_eq_top (R := R) (ι := Fin 4)
      leavittFamily three_le_card (i := 0) (j := 2) (by decide))

/-- The exact rank-four group is nontrivial, witnessed by the printed
defect. -/
theorem nontrivial : Nontrivial H :=
  ⟨⟨defect, 1, defect_ne_one⟩⟩

/-- The exact rank-four group is finitely generated. -/
theorem finitelyGenerated : Group.FG H :=
  elementaryGroup_finitelyGenerated 4 (by omega)

/-- The exact rank-four group is countable. -/
theorem countable : Countable H :=
  countable_of_fg finitelyGenerated

local instance rankFourCountable : Countable H := countable

/-- The exact rank-four group has Kazhdan's property `(T)`. -/
theorem hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} H :=
  BinaryLeavittSteinberg.elementaryBase_hasKazhdanPropertyT (n := 4) (by omega)

/-- The closed simplicity-free structural profile used by the defect route. -/
theorem closedStructuralProfile :
    Countable H ∧ Group.FG H ∧ Nontrivial H ∧
      HasKazhdanPropertyT.{0, 0} H ∧
      defect ≠ 1 ∧ Subgroup.normalClosure ({defect} : Set H) = ⊤ :=
  ⟨countable, finitelyGenerated, nontrivial, hasKazhdanPropertyT,
    defect_ne_one, normalClosure_defect_eq_top⟩

/-! ## The upper-left `EL₃` corner

The corner subgroup and its two structural facts -- that the stabilization
embedding of `Leavitt.RankFourCompressors` lands in it, and that it is
contained in that embedding's range -- are proved over an arbitrary
coefficient ring.  Running the closure induction at the concrete
`L_{𝔽₂}(1,2)` exhausts the heartbeat budget in `whnf`: the subgroup-subtype
multiplication has to be unfolded through the ring's `RingQuot` instance
chain.  At an abstract ring there is nothing to unfold. -/

section Generic

variable {A : Type*} [Ring A]

/-- The elementary roots supported on the upper-left `3 × 3` corner, over an
arbitrary coefficient ring. -/
def genericCornerRootSet (A : Type*) [Ring A] : Set (RankFour.Ambient A) :=
  {x | ∃ (i j : Fin 3) (hij : i ≠ j) (a : A),
    elementaryRoot (RankFour.coreIndex i) (RankFour.coreIndex j)
      (RankFour.coreIndex_injective.ne hij) a = x}

/-- The upper-left `EL₃(A)` subgroup of `EL₄(A)`. -/
def genericCorner (A : Type*) [Ring A] : Subgroup (RankFour.Ambient A) :=
  Subgroup.closure (genericCornerRootSet A)

theorem coreTransvection_mem_genericCorner (i j : Fin 3) (hij : i ≠ j) (a : A) :
    RankFour.coreEmbedding (RankFour.coreTransvection i j hij a) ∈
      genericCorner A := by
  rw [RankFour.coreEmbedding_coreTransvection]
  exact Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩

/-- The embedding lands in the corner.  The induction is run through
`elementaryRootSet_generate` and `Subgroup.closure_le` rather than through
`Subgroup.closure_induction` on the subtype: the latter needs a `change`
across the subgroup-subtype group structure at every step, and that
definitional check exhausts the heartbeat budget. -/
theorem coreEmbedding_mem_genericCorner (g : RankFour.Core A) :
    RankFour.coreEmbedding g ∈ genericCorner A := by
  have h : Subgroup.closure (elementaryRootSet (Fin 3) A) ≤
      (genericCorner A).comap (RankFour.coreEmbedding (A := A)) := by
    rw [Subgroup.closure_le]
    rintro x ⟨i, j, hij, hx⟩
    obtain ⟨a, rfl⟩ := (mem_elementaryRootSubgroup_iff i j hij x).mp hx
    exact coreTransvection_mem_genericCorner i j hij a
  have hg : g ∈ Subgroup.closure (elementaryRootSet (Fin 3) A) := by
    rw [elementaryRootSet_generate]
    exact Subgroup.mem_top g
  exact Subgroup.mem_comap.mp (h hg)

theorem genericCorner_le_range :
    genericCorner A ≤ (RankFour.coreEmbedding (A := A)).range := by
  rw [genericCorner, Subgroup.closure_le]
  rintro x ⟨i, j, hij, a, rfl⟩
  exact ⟨RankFour.coreTransvection i j hij a,
    RankFour.coreEmbedding_coreTransvection i j hij a⟩

end Generic

/-- The inclusion of the upper-left three indices, which is the one
`Leavitt.RankFourCompressors` uses. -/
def cornerIndex (i : Fin 3) : Fin 4 := RankFour.coreIndex i

theorem cornerIndex_injective : Function.Injective cornerIndex :=
  RankFour.coreIndex_injective

@[simp] theorem cornerIndex_zero : cornerIndex 0 = (0 : Fin 4) := by decide

@[simp] theorem cornerIndex_one : cornerIndex 1 = (1 : Fin 4) := by decide

@[simp] theorem cornerIndex_two : cornerIndex 2 = (2 : Fin 4) := by decide

/-- The elementary roots supported on the upper-left `3 × 3` corner. -/
def cornerRootSet : Set H := genericCornerRootSet R

/-- The literal upper-left `EL₃(R)` subgroup of `H`; the printed `L`. -/
noncomputable def corner : Subgroup H := Subgroup.closure cornerRootSet

theorem corner_eq_genericCorner : corner = genericCorner R := rfl

/-- The upper-left embedding `EL₃(R) → EL₄(R)` of
`Leavitt.RankFourCompressors` lands in the printed corner. -/
theorem coreEmbedding_mem_corner (g : RankFour.Core R) :
    RankFour.coreEmbedding g ∈ corner :=
  coreEmbedding_mem_genericCorner g

theorem corner_le_coreEmbedding_range :
    corner ≤ (RankFour.coreEmbedding (A := R)).range :=
  genericCorner_le_range

theorem coreEmbedding_range_eq_corner :
    (RankFour.coreEmbedding (A := R)).range = corner :=
  le_antisymm (by rintro _ ⟨g, rfl⟩; exact coreEmbedding_mem_corner g)
    corner_le_coreEmbedding_range

/-- The printed corner as a quotient of `EL₃(R)`. -/
noncomputable def cornerEmbeddingToCorner :
    BinaryLeavittSteinberg.ElementaryBase 3 →* corner :=
  (RankFour.coreEmbedding (A := R)).codRestrict corner coreEmbedding_mem_corner

theorem cornerEmbeddingToCorner_surjective :
    Function.Surjective cornerEmbeddingToCorner := by
  intro x
  obtain ⟨g, hg⟩ := corner_le_coreEmbedding_range x.property
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact hg

/-- **"Both groups have property (T)", corner half.**  The printed
`L = EL₃(R)` has property `(T)`; the embedding of `EL₃(R)` onto it is even
injective, but surjectivity is all the transport needs. -/
theorem corner_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} corner :=
  HasKazhdanPropertyT.of_surjective cornerEmbeddingToCorner
    cornerEmbeddingToCorner_surjective
    (BinaryLeavittSteinberg.elementaryBase_hasKazhdanPropertyT
      (n := 3) (by omega))

/-! ## The printed compressor, centralizer mark and corner element -/

/-- **The printed compressor `u = u₃u₂u₁`**, with
`uᵢ = e₄ᵢ(t-1)eᵢ₄(1)e₄ᵢ(s-1)eᵢ₄(-t)` at `s = s₀`, `t = t₀`.  It is a literal
word in twelve elementary transvections, so its membership in `EL₄(R)` needs no
Whitehead argument. -/
noncomputable def u : H := RankFour.compressor leavittFamily

/-- **The printed centralizer mark `c = [e₄₁(e), e₁₄(t)] = diag(1,1,1,1+et)`,**
in zero-based coordinates `⁅e₃₀(q), e₀₃(t₀)⁆`.  At rank four the mark cannot be
a single elementary root: every index pair meets the corner, and the printed
element is a diagonal matrix supported on the fourth coordinate alone. -/
noncomputable def c : H :=
  ⁅elementaryRoot (3 : Fin 4) 0 (by decide) q,
    elementaryRoot (0 : Fin 4) 3 (by decide) leavittFamily.t0⁆

/-- The printed corner element `ell = e₁₂(1)` (printed `e₂₃(1)`). -/
noncomputable def ell : H :=
  elementaryRoot (1 : Fin 4) 2 (by decide) 1

theorem ell_eq_cornerRoot :
    ell = elementaryRoot (cornerIndex 1) (cornerIndex 2)
      (cornerIndex_injective.ne (by decide)) 1 :=
  elementaryRoot_congr _ _ (by decide) (by decide) 1

/-- The printed element `ell` belongs to the upper-left corner. -/
theorem ell_mem_corner : ell ∈ corner := by
  rw [ell_eq_cornerRoot]
  exact Subgroup.subset_closure ⟨1, 2, by decide, 1, rfl⟩

/-- The exact remaining group-level content of the compression step in the
proof of `thm:full-defect-ring`, at the manuscript's own ring and rank.

The subgroup is the upper-left `EL₃` corner; `u` is the printed comb
compressor, `c` the printed diagonal mark, and `ell` the printed `e₂₃(1)`.  The
four conjuncts are the four printed assertions: property `(T)` for `L`,
centrality of `c` relative to `L`, the one-sided compression `uLu⁻¹ ≤ L`, and
the displayed commutator `[ucu⁻¹, ℓ] = d`.

The condition is deliberately stated using a one-sided compressor itself,
matching the current manuscript rather than the stronger subgroup generated by
all compressors used in older files. -/
def PrintedDefectConfiguration : Prop :=
  HasKazhdanPropertyT.{0, 0} corner ∧
    (∀ gamma ∈ corner, Commute c gamma) ∧
    (∀ gamma ∈ corner, u * gamma * u⁻¹ ∈ corner) ∧
    ⁅u * c * u⁻¹, ell⁆ = defect

/-- The exact content of `prop:simple`, kept as a named proposition so audits
can distinguish the final simplicity theorem from its root-normal-generation
support.  It is proved by `RankFourSimplicity.manuscriptPropositionSimple`. -/
def PropositionSimple : Prop := IsSimpleGroup H

/-- The group-level printed configuration makes the printed defect equal to
the whole rank-four group.  This uses the already closed normal-generation
theorem for `d`; it does not use simplicity. -/
theorem printedDefect_eq_top_of_configuration
    (hconfiguration : PrintedDefectConfiguration) :
    printedDefect corner = ⊤ := by
  obtain ⟨_, hcentral, hcompresses, hcomm⟩ := hconfiguration
  have hd : defect ∈ printedDefect corner := by
    rw [← hcomm]
    exact printedDefect_generator_mem corner hcompresses hcentral ell_mem_corner
  have hclosure : Subgroup.normalClosure ({defect} : Set H) ≤
      printedDefect corner := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    simpa [hx] using hd
  apply top_unique
  rw [← normalClosure_defect_eq_top]
  exact hclosure

/-- The group-level printed configuration alone closes the full-radical
calculation in `thm:headline`.  The proof is exactly the current manuscript's
route: the displayed defect normally generates, so the printed defect
saturates, and the one-sided compression criterion applies. -/
theorem residual_eq_top_of_configuration
    (hconfiguration : PrintedDefectConfiguration) :
    actualCoronaMFResidual H = ⊤ := by
  letI : Countable H := countable
  have htop : printedDefect corner = ⊤ :=
    printedDefect_eq_top_of_configuration hconfiguration
  obtain ⟨hcornerT, _, _, _⟩ := hconfiguration
  have hfull :=
    (manuscriptOneSidedCompressionCriterion (G := H) corner hcornerT).2.2
      hasKazhdanPropertyT htop
  rwa [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual] at hfull

/-- The six structural clauses of `thm:headline`: `H` is nontrivial, simple,
has property `(T)`, has full MF radical in the basis-free reading
`actualCoronaMFResidual`, kills every homomorphism to a countable MF group, and
is not MF.

This is NOT the whole printed theorem.  It carries neither the finite
generation the theorem states first, nor the reduced-C⋆ clause, nor the
maximal-C⋆ clause it now ends with; the complete printed statement is
`manuscriptPrintedHeadlineRankFour`. -/
def HeadlineConclusion : Prop :=
  Nontrivial H ∧
    IsSimpleGroup H ∧
    HasKazhdanPropertyT.{0, 0} H ∧
    actualCoronaMFResidual H = ⊤ ∧
    (∀ (M : Type) [Group M] [Countable M],
      IsCDEOperatorMF M → ∀ (f : H →* M) (x : H), f x = 1) ∧
    ¬ IsCDEOperatorMF H

/-! ## Assembling the headline from the two named inputs -/

/-- A nontrivial countable group with full actual corona MF residual is not
MF in the literal CDE sense. -/
theorem not_isCDEOperatorMF_of_residual_eq_top
    (hfull : actualCoronaMFResidual H = ⊤) :
    ¬ IsCDEOperatorMF H := by
  letI : Countable H := countable
  letI : Nontrivial H := nontrivial
  exact not_isCDEOperatorMF_of_actualCoronaMFResidual_eq_top hfull

/-- Once simplicity and the full-radical calculation are available, every
remaining clause of `thm:headline` is already closed.  This theorem makes the
dependency boundary exact: it consumes no matrix or normal-subgroup fact other
than those two named propositions. -/
theorem headlineConclusion_of
    (hsimple : PropositionSimple)
    (hfull : actualCoronaMFResidual H = ⊤) :
    HeadlineConclusion := by
  letI : Countable H := countable
  letI : Nontrivial H := nontrivial
  have hnot : ¬ IsCDEOperatorMF H :=
    not_isCDEOperatorMF_of_residual_eq_top hfull
  refine ⟨nontrivial, hsimple, hasKazhdanPropertyT, hfull, ?_, hnot⟩
  intro M _ _ hM f x
  exact eq_one_of_isSimpleGroup_of_target_isCDEOperatorMF
    hsimple hnot hM f x

/-- Consequently the current headline has exactly two unresolved inputs:
the rank-four group-level realization of the printed matrices and the
normal-subgroup/simplicity theorem. -/
theorem headlineConclusion_of_configuration_and_simplicity
    (hconfiguration : PrintedDefectConfiguration)
    (hsimple : PropositionSimple) :
    HeadlineConclusion :=
  headlineConclusion_of hsimple
    (residual_eq_top_of_configuration hconfiguration)

end RankFourEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
