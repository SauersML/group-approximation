import GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupHeadline
import GroupApproximation.Manuscript.OneSidedMFRadical.BinaryLeavittPurelyInfiniteIdempotent
import GroupApproximation.Leavitt.CongruenceSubgroups
import GroupApproximation.Leavitt.PreusserAssembly
import GroupApproximation.Leavitt.ExchangeRefinement
import GroupApproximation.Leavitt.ExchangePrerequisite
import GroupApproximation.Leavitt.BinaryLeavittSimple
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Leavitt.AryPurelyInfinite
import GroupApproximation.KOne.AlgebraicKOne
import GroupApproximation.Meta.AxiomGuard

/-!
# `non_mf_groups_exist.tex`, "The binary example": sentence-level closure

`non_mf_groups_exist.tex`, the subsection "The binary example" (`R = L_{𝔽₂}(1,2)`,
`H = R^×`, identified with `EL₄(R)`), the printed proof of Theorem
`thm:headline`, and the definitions paragraph that follows it (equivalent and
infinite idempotents, purely infinite simple rings, `GL(R)`, `EL(R)`,
Whitehead's lemma, `K₁(R)`, and the canonical map `κ`).

Every declaration in this module either is new, elementary algebra proved
directly from `LeavittFamily`'s defining equations, or is a rank-four
restatement of a generic fact already proved for an arbitrary ring/index type
in `CongruenceSubgroups`, `PreusserAssembly`, or `BinaryLeavittSimple` — most of
those generic facts were previously only wired up at the *superseded* rank
twelve (`RankTwelveSimplicitySentences.lean`); this module is their rank-four
counterpart, matching the current manuscript.

## The four citations the printed proof of `thm:headline` names

"The ring `R` is purely infinite simple~\cite{AbramsAranda} and therefore an
exchange ring~\cite{AraExchange}, so by Preusser's sandwich
theorem~\cite[Theorem~3]{Preusser} ...", and later "since
`Z(R)=𝔽₂`~\cite[Corollary~4.3]{ArandaCrow}".  All four turn out to already have
a literal, unconditional, hypothesis-free proof in the tree for the
manuscript's own ring, independently of any implication chain between the
citations:

* **purely infinite simple**, in the exact Ara–Goodearl–Pardo idempotent form
  `MFQuotientUnits.IsPurelyInfiniteSimpleRing` —
  `Manuscript.OneSidedMFRadical.manuscriptBinaryLeavittPurelyInfiniteSimpleIdempotent`;
* **exchange ring**, in Nicholson's finite-partition form —
  `BinaryLeavitt.hasFiniteRightExchangePartitions`;
* **Preusser's sandwich theorem**, generically over any ring with that
  exchange property and any index type of cardinality `≥ 3` —
  `PreusserAssembly.preusser_sandwich`, discharged from Preusser's own
  Propositions 20 and 21 rather than assumed;
* **`Z(R) = 𝔽₂`**, literally as `Subalgebra.center (ZMod 2) R = ⊥` —
  `BinaryLeavitt.center_eq_bot`.

`manuscriptSentence_purelyInfiniteExchangePreusserSandwich` and
`manuscriptSentence_centerEqF2GivesGEqOne` below record this: they are stated
and proved as ordinary `formalized` sentence carriers of this lane, not as
`partial` placeholders, even though the campaign's initial task list assigned
"prove the literature facts behind these citations" to a separate lane
(`o-preusser`).  See this lane's report to `main` for the reassignment note.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace BinaryExampleSentences

open OneSidedMFRadical.RankFourEndpoint
open scoped commutatorElement

/-! ## Opening of "The binary example" (tex, "Put `R = L_{𝔽₂}(1,2)`...") -/

/-- Printed: "Put `H = R^×`." The unit group of the manuscript's coefficient
ring, before its later identification with `EL₄(R)`. -/
abbrev BinaryExampleUnitGroup : Type := Rˣ

/-- Printed map `x ↦ (t₀x, t₁x)`, from `R` to `R ⊕ R` (written `R × R`). -/
def binaryExampleSplit (x : R) : R × R := (leavittFamily.t0 * x, leavittFamily.t1 * x)

/-- Printed map `(y, z) ↦ s₀y + s₁z`, from `R ⊕ R` to `R`. -/
def binaryExampleMerge (p : R × R) : R := leavittFamily.s0 * p.1 + leavittFamily.s1 * p.2

/-- **Printed:** "the maps `x ↦ (t₀x, t₁x)` and `(y,z) ↦ s₀y+s₁z` are mutually
inverse isomorphisms of right `R`-modules between `R` and `R ⊕ R`."

The six conjuncts are, in order: the two maps are mutually inverse, and each is
additive and right-`R`-linear — exactly the data of a right-module
isomorphism, stated without invoking Mathlib's (left-)`Module` machinery,
which does not fit a noncommutative *right* action. -/
theorem manuscriptSentence_leavittModuleEquivProd :
    Function.LeftInverse binaryExampleMerge binaryExampleSplit ∧
      Function.RightInverse binaryExampleMerge binaryExampleSplit ∧
      (∀ x y : R, binaryExampleSplit (x + y)
          = binaryExampleSplit x + binaryExampleSplit y) ∧
      (∀ x a : R, binaryExampleSplit (x * a)
          = (leavittFamily.t0 * x * a, leavittFamily.t1 * x * a)) ∧
      (∀ p q : R × R, binaryExampleMerge (p + q)
          = binaryExampleMerge p + binaryExampleMerge q) ∧
      (∀ (p : R × R) (a : R), binaryExampleMerge (p.1 * a, p.2 * a)
          = binaryExampleMerge p * a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show leavittFamily.s0 * (leavittFamily.t0 * x)
        + leavittFamily.s1 * (leavittFamily.t1 * x) = x
    rw [← mul_assoc, ← mul_assoc, ← add_mul, leavittFamily.sum_range, one_mul]
  · intro p
    show (leavittFamily.t0 * (leavittFamily.s0 * p.1 + leavittFamily.s1 * p.2),
        leavittFamily.t1 * (leavittFamily.s0 * p.1 + leavittFamily.s1 * p.2)) = p
    ext
    · show leavittFamily.t0 * (leavittFamily.s0 * p.1 + leavittFamily.s1 * p.2) = p.1
      rw [mul_add, ← mul_assoc, ← mul_assoc, leavittFamily.t0_s0, leavittFamily.t0_s1,
        one_mul, zero_mul, add_zero]
    · show leavittFamily.t1 * (leavittFamily.s0 * p.1 + leavittFamily.s1 * p.2) = p.2
      rw [mul_add, ← mul_assoc, ← mul_assoc, leavittFamily.t1_s0, leavittFamily.t1_s1,
        zero_mul, one_mul, zero_add]
  · intro x y
    show (leavittFamily.t0 * (x + y), leavittFamily.t1 * (x + y))
        = (leavittFamily.t0 * x, leavittFamily.t1 * x) + (leavittFamily.t0 * y, leavittFamily.t1 * y)
    ext
    · show leavittFamily.t0 * (x + y) = leavittFamily.t0 * x + leavittFamily.t0 * y
      exact mul_add _ _ _
    · show leavittFamily.t1 * (x + y) = leavittFamily.t1 * x + leavittFamily.t1 * y
      exact mul_add _ _ _
  · intro x a
    show (leavittFamily.t0 * (x * a), leavittFamily.t1 * (x * a))
        = (leavittFamily.t0 * x * a, leavittFamily.t1 * x * a)
    rw [mul_assoc, mul_assoc]
  · intro p q
    show leavittFamily.s0 * (p.1 + q.1) + leavittFamily.s1 * (p.2 + q.2)
        = leavittFamily.s0 * p.1 + leavittFamily.s1 * p.2
          + (leavittFamily.s0 * q.1 + leavittFamily.s1 * q.2)
    rw [mul_add, mul_add]
    abel
  · intro p a
    show leavittFamily.s0 * (p.1 * a) + leavittFamily.s1 * (p.2 * a)
        = (leavittFamily.s0 * p.1 + leavittFamily.s1 * p.2) * a
    rw [add_mul, mul_assoc, mul_assoc]

/-- **Printed:** "`H ≅ GL₄(R) = EL₄(R)`~\cite[Proposition~4.2 and
Corollary~4.4]{KhanhThanh}" (with `H = R^×` at this point in the text).

The identification is proved outright in `UnitGroupHeadline`, not taken from
the citation: `glFourEquivUnits` is the self-similarity `M₄(R) ≅ R` of
Proposition `prop:selfsim`, and `elementaryGroup_four_eq_top` is
`BinaryLeavitt.elementaryGroup_eq_top` at rank four. -/
theorem manuscriptSentence_unitsEquivGLFourEqELFour :
    Nonempty (Rˣ ≃* (Matrix (Fin 4) (Fin 4) R)ˣ) ∧
      elementaryGroup (Fin 4) R = ⊤ :=
  ⟨⟨OneSidedMFRadical.UnitGroupHeadline.glFourEquivUnits.symm⟩,
    OneSidedMFRadical.UnitGroupHeadline.elementaryGroup_four_eq_top⟩

/-- **Printed:** "We identify `H` with `EL₄(R)`."

From this point on, the manuscript's `H` denotes `EL₄(R)`
(`OneSidedMFRadical.RankFourEndpoint.H`); `unitsEquivHeadline` is the
isomorphism carrying out the identification. -/
theorem manuscriptSentence_weIdentifyHWithELFour :
    Nonempty (Rˣ ≃* OneSidedMFRadical.RankFourEndpoint.H) :=
  ⟨OneSidedMFRadical.UnitGroupHeadline.unitsEquivHeadline⟩

/-! ## The printed proof of Theorem `thm:headline` -/

/-- **Printed:** "The relations give `t₀s₀=1` and `t₁(1-s₀t₀)s₁=1`, so `R`
satisfies the hypothesis of Theorem~\ref{thm:full-defect-ring}, and every
homomorphism from `H` to an MF group is trivial."

The two displayed equations are `LeavittFamily.t0_s0` and a short computation
from `t1_s0`/`t1_s1`; the conclusion is the sixth conjunct of
`manuscriptBinaryLeavittFullRadicalRankFour` (the full-radical package built
from exactly this ring, at rank four, via the printed defect-saturation
route). -/
theorem manuscriptSentence_relationsGiveTrivialHomomorphisms :
    leavittFamily.t0 * leavittFamily.s0 = 1 ∧
      leavittFamily.t1 * (1 - leavittFamily.s0 * leavittFamily.t0) * leavittFamily.s1 = 1 ∧
      ∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
        ∀ (f : H →* M) (x : H), f x = 1 := by
  refine ⟨leavittFamily.t0_s0, ?_, ?_⟩
  · have h1 : leavittFamily.t1 * (1 - leavittFamily.s0 * leavittFamily.t0)
        = leavittFamily.t1 := by
      rw [mul_sub, mul_one, ← mul_assoc, leavittFamily.t1_s0, zero_mul, sub_zero]
    rw [h1, leavittFamily.t1_s1]
  · obtain ⟨-, -, -, -, -, h, -⟩ :=
      OneSidedMFRadical.manuscriptBinaryLeavittFullRadicalRankFour
    exact h

/-! "The ring `R` is finitely generated, so `H` has property `(T)` by [EJZ,
Theorem 1.1], and hence is finitely generated [BHV, Theorem 1.3.1]" is closed
by lane `o-preusser` in `HeadlineCitationSentences.lean`, in the printed
vocabulary and along the printed route (Ershov–Jaikin-Zapirain, then
Bekka–de la Harpe–Valette's coset-`ℓ²` property-`(T)`-implies-finite-generation
argument, `Kazhdan.KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT`), not
duplicated here:
`HeadlineCitationSentences.manuscriptSentence_finitelyGeneratedGivesPropertyT`
and `HeadlineCitationSentences.headlineGroup_finitelyGenerated_via_propertyT`. -/

/-- **Printed:** "Since `e₁₂(1)≠1`, the group `H` is nontrivial." -/
theorem manuscriptSentence_e12OneForcesNontrivial :
    elementaryRoot (0 : Fin 4) 1 (by decide) (1 : R) ≠ 1 ∧ Nontrivial H :=
  ⟨fun h => one_ne_zero ((elementaryRoot_eq_one_iff (0 : Fin 4) 1 (by decide) (1 : R)).mp h),
    nontrivial⟩

/-- **Printed:** "Let `N` be a normal subgroup of `H`." -/
theorem manuscriptSentence_letNBeNormalSubgroup : ∃ N : Subgroup H, N.Normal :=
  ⟨⊥, inferInstance⟩

/-- **Printed:** "The ring `R` is purely infinite simple~\cite{AbramsAranda}
and therefore an exchange ring~\cite{AraExchange}, so by Preusser's sandwich
theorem~\cite[Theorem~3]{Preusser} there is an ideal `I` of `R` with
`EL₄(R,I)≤N≤C₄(R,I)`."

See the module docstring: all three clauses are proved unconditionally for the
manuscript's own ring, at rank four. -/
theorem manuscriptSentence_purelyInfiniteExchangePreusserSandwich
    (N : Subgroup H) (hN : N.Normal) :
    MFQuotientUnits.IsPurelyInfiniteSimpleRing R ∧
      ExchangePrerequisite.HasFiniteRightExchangePartitions R ∧
      ∃ I : TwoSidedIdeal R, relativeElementary (Fin 4) I ≤ N ∧
        N.map (elementaryGroup (Fin 4) R).subtype ≤ congruenceSubgroup (Fin 4) I := by
  refine ⟨OneSidedMFRadical.manuscriptBinaryLeavittPurelyInfiniteSimpleIdempotent,
    BinaryLeavitt.hasFiniteRightExchangePartitions (ZMod 2), ?_⟩
  exact PreusserAssembly.preusser_sandwich three_le_card
    (BinaryLeavitt.hasFiniteRightExchangePartitions (ZMod 2)) N hN

/-- **Printed:** "Since `R` is simple, either `I=R`, and then `N≥EL₄(R)=H`, or
`I=0`, and then every `g∈N` is central in `GL₄(R)`." (Both branches, as the
trichotomy plus the two branch statements.) -/
theorem manuscriptSentence_simpleGivesTrichotomy (I : TwoSidedIdeal R) :
    I = ⊥ ∨ I = ⊤ := by
  haveI := coefficientRing_isSimple
  exact IsSimpleOrder.eq_bot_or_eq_top I

/-- The `I = R` branch: `EL₄(R,R) = EL₄(R)`, so a normal subgroup containing
the sandwich's lower bound at `I = ⊤` is all of `H`. -/
theorem manuscriptSentence_idealTopGivesNEqTop
    (N : Subgroup H) (hIle : relativeElementary (Fin 4) (⊤ : TwoSidedIdeal R) ≤ N) :
    relativeElementary (Fin 4) (⊤ : TwoSidedIdeal R) = ⊤ ∧ N = ⊤ := by
  refine ⟨relativeElementary_top, ?_⟩
  rw [relativeElementary_top] at hIle
  exact top_le_iff.mp hIle

/-- **Printed (continuing the "`I=0`" branch):** `N ≤ C₄(R,0) = Z(\GL_4(R))`. -/
theorem manuscriptSentence_idealZeroGivesCentral
    (N : Subgroup H)
    (hIcong : N.map (elementaryGroup (Fin 4) R).subtype
      ≤ congruenceSubgroup (Fin 4) (⊥ : TwoSidedIdeal R)) :
    N.map (elementaryGroup (Fin 4) R).subtype
        ≤ Subgroup.center (Matrix (Fin 4) (Fin 4) R)ˣ ∧
      congruenceSubgroup (Fin 4) (⊥ : TwoSidedIdeal R)
        = Subgroup.center (Matrix (Fin 4) (Fin 4) R)ˣ := by
  have hcb : congruenceSubgroup (Fin 4) (⊥ : TwoSidedIdeal R)
      = Subgroup.center (Matrix (Fin 4) (Fin 4) R)ˣ :=
    congruenceSubgroup_bot (ι := Fin 4) (R := R)
      (by norm_num : 1 < Fintype.card (Fin 4)) (0 : Fin 4)
  refine ⟨?_, hcb⟩
  rw [← hcb]
  exact hIcong

/-- **Printed:** the case argument fixes an element of `N` to analyse. -/
theorem manuscriptSentence_fixGInN (N : Subgroup H) :
    ∃ g : (Matrix (Fin 4) (Fin 4) R)ˣ, g ∈ N.map (elementaryGroup (Fin 4) R).subtype :=
  ⟨1, Subgroup.one_mem _⟩

/-- **Printed:** "In the second case, commuting with each `e_{ij}(1)` forces
`g=\lambda I_4` with `\lambda\in R^\times`." -/
theorem manuscriptSentence_commutingSingleForcesScalar
    (g : (Matrix (Fin 4) (Fin 4) R)ˣ)
    (hg : ∀ (i j : Fin 4) (hij : i ≠ j),
      (g : Matrix (Fin 4) (Fin 4) R) *
          (elementaryUnit i j hij (1 : R) : Matrix (Fin 4) (Fin 4) R)
        = (elementaryUnit i j hij (1 : R) : Matrix (Fin 4) (Fin 4) R) *
            (g : Matrix (Fin 4) (Fin 4) R)) :
    ∃ u : Rˣ,
      (g : Matrix (Fin 4) (Fin 4) R) = Matrix.diagonal fun _ ↦ (u : R) := by
  have hg' : ∀ (i j : Fin 4) (hij : i ≠ j),
      (g : Matrix (Fin 4) (Fin 4) R) * Matrix.single i j (1 : R)
        = Matrix.single i j (1 : R) * (g : Matrix (Fin 4) (Fin 4) R) := by
    intro i j hij
    have h := hg i j hij
    have hval : (elementaryUnit i j hij (1 : R) : Matrix (Fin 4) (Fin 4) R)
        = 1 + Matrix.single i j (1 : R) := rfl
    rw [hval, mul_add, add_mul, mul_one, one_mul] at h
    exact add_left_cancel h
  have hdiag : (g : Matrix (Fin 4) (Fin 4) R)
      = Matrix.diagonal fun _ ↦ (g : Matrix (Fin 4) (Fin 4) R) 0 0 :=
    eq_diagonal_of_commute_single (ι := Fin 4)
      (by norm_num : 1 < Fintype.card (Fin 4)) 0 _ hg'
  have h1 : (g : Matrix (Fin 4) (Fin 4) R) 0 0 *
      ((g⁻¹ : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) 0 0 = 1 := by
    have hone : Matrix.diagonal (fun _ : Fin 4 ↦ (g : Matrix (Fin 4) (Fin 4) R) 0 0) *
        ((g⁻¹ : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) = 1 := by
      rw [← hdiag]
      exact g.mul_inv
    have h : (Matrix.diagonal (fun _ : Fin 4 ↦ (g : Matrix (Fin 4) (Fin 4) R) 0 0) *
        ((g⁻¹ : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R)) 0 0
        = (1 : Matrix (Fin 4) (Fin 4) R) 0 0 := by rw [hone]
    rwa [Matrix.diagonal_mul, Matrix.one_apply_eq] at h
  have h2 : ((g⁻¹ : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) 0 0 *
      (g : Matrix (Fin 4) (Fin 4) R) 0 0 = 1 := by
    have htwo : ((g⁻¹ : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) *
        Matrix.diagonal (fun _ : Fin 4 ↦ (g : Matrix (Fin 4) (Fin 4) R) 0 0) = 1 := by
      rw [← hdiag]
      exact g.inv_mul
    have h : (((g⁻¹ : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) *
        Matrix.diagonal (fun _ : Fin 4 ↦ (g : Matrix (Fin 4) (Fin 4) R) 0 0)) 0 0
        = (1 : Matrix (Fin 4) (Fin 4) R) 0 0 := by rw [htwo]
    rwa [Matrix.mul_diagonal, Matrix.one_apply_eq] at h
  exact ⟨⟨(g : Matrix (Fin 4) (Fin 4) R) 0 0,
      ((g⁻¹ : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) 0 0, h1, h2⟩,
    hdiag⟩

/-- **Printed:** "and commuting with each `e_{ij}(a)` then gives
`\lambda a=a\lambda` for all `a\in R`." -/
theorem manuscriptSentence_commutingGeneralForcesCentral
    (u : Rˣ)
    (hg : ∀ (i j : Fin 4) (hij : i ≠ j) (a : R),
      (Matrix.diagonal fun _ : Fin 4 ↦ (u : R)) *
          (elementaryUnit i j hij a : Matrix (Fin 4) (Fin 4) R)
        = (elementaryUnit i j hij a : Matrix (Fin 4) (Fin 4) R) *
            (Matrix.diagonal fun _ : Fin 4 ↦ (u : R))) :
    (∀ x : R, (u : R) * x = x * (u : R)) := by
  have hg' : ∀ (i j : Fin 4) (a : R), i ≠ j →
      (Matrix.diagonal fun _ : Fin 4 ↦ (u : R)) * Matrix.single i j a
        = Matrix.single i j a * (Matrix.diagonal fun _ : Fin 4 ↦ (u : R)) := by
    intro i j a hij
    have h := hg i j hij a
    have hval : (elementaryUnit i j hij a : Matrix (Fin 4) (Fin 4) R)
        = 1 + Matrix.single i j a := rfl
    rw [hval, mul_add, add_mul, mul_one, one_mul] at h
    exact add_left_cancel h
  exact commute_of_commute_single (ι := Fin 4)
    (by norm_num : 1 < Fintype.card (Fin 4)) (u : R) hg'

/-- **Printed:** "So `\lambda` lies in `Z(R)=\F_2`~\cite[Corollary
4.3]{ArandaCrow}, and `N=1`."

`Z(R) = 𝔽₂` is literally `Subalgebra.center (ZMod 2) R = ⊥`
(`BinaryLeavitt.center_eq_bot`), proved unconditionally in the tree; combined
with `λ` being a unit this forces `λ = 1`
(`BinaryLeavitt.central_units_trivial`), hence `g = 1`. -/
theorem manuscriptSentence_centerEqF2GivesGEqOne
    (g : (Matrix (Fin 4) (Fin 4) R)ˣ) (u : Rˣ)
    (hdiag : (g : Matrix (Fin 4) (Fin 4) R) = Matrix.diagonal fun _ ↦ (u : R))
    (hcentral : ∀ x : R, (u : R) * x = x * (u : R)) :
    Subalgebra.center (ZMod 2) R = ⊥ ∧ g = 1 := by
  refine ⟨BinaryLeavitt.center_eq_bot (ZMod 2), ?_⟩
  have hu1 : u = 1 := BinaryLeavitt.central_units_trivial u hcentral
  simp only [hu1, Units.val_one] at hdiag
  apply Units.ext
  rw [hdiag, Matrix.diagonal_one, Units.val_one]

/-- **Printed:** "Thus `N=1`." -/
theorem manuscriptSentence_thusNTrivial
    (N : Subgroup H)
    (hall : ∀ g ∈ N.map (elementaryGroup (Fin 4) R).subtype, g = 1) :
    N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxmap : (elementaryGroup (Fin 4) R).subtype x
      ∈ N.map (elementaryGroup (Fin 4) R).subtype := ⟨x, hx, rfl⟩
  have hxone : (elementaryGroup (Fin 4) R).subtype x = 1 := hall _ hxmap
  exact (elementaryGroup (Fin 4) R).subtype_injective hxone

/-- **Printed:** "So `H` is simple."

Proved here by the independent, unconditional root-extraction route
(`RankFourEndpoint.manuscriptPropositionSimple`), not by literally replaying
the case split above; the case-split declarations of this module are the
literal sentence-by-sentence carriers of the printed route, and this
declaration is the printed *conclusion*, which the tree already has by a
different, hypothesis-free proof. -/
theorem manuscriptSentence_HIsSimple : IsSimpleGroup H :=
  manuscriptPropositionSimple

/-- **Printed:** "It is nontrivial, and every homomorphism from it to an MF
group is trivial, so `H` is not MF." -/
theorem manuscriptSentence_HNontrivialAndNotMF :
    Nontrivial H ∧
      (∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
        ∀ (f : H →* M) (x : H), f x = 1) ∧
      ¬ IsCDEOperatorMF H := by
  obtain ⟨-, hnt, -, -, -, h, hnot⟩ :=
    OneSidedMFRadical.manuscriptBinaryLeavittFullRadicalRankFour
  exact ⟨hnt, h, hnot⟩

/-- **Printed:** "Since `R≠0` satisfies the hypothesis of
Theorem~\ref{thm:full-defect-ring}, Corollary~\ref{cor:one-sided-ring-maximal}
shows that `C*_r(H)` is separable, stably finite, and not MF, and that
`C*_max(H)` contains a proper isometry." -/
theorem manuscriptSentence_reducedAndMaximalCStarClauses :
    OneSidedMFRadical.ReducedCStarConsequenceRankFour ∧
      OneSidedMFRadical.MaximalCStarNotFiniteRankFour :=
  ⟨OneSidedMFRadical.manuscriptReducedCStarConsequenceRankFour,
    OneSidedMFRadical.manuscriptMaximalCStarNotFiniteRankFour⟩

/-! ## The definitions paragraph following the proof

"All rings in the following discussion are unital and associative. Two
idempotents `e,f` of a ring are *equivalent* if `e=xy` and `f=yx` for some
`x,y`; an idempotent `e` is *infinite* if `e=f+g` for orthogonal idempotents
`f,g` with `f` equivalent to `e` and `g≠0`; and a simple ring is *purely
infinite* if every nonzero right ideal contains an infinite
idempotent~\cite[Definitions~1.2]{AGP}. The algebras `L_k(1,d)` are purely
infinite simple~\cite{AbramsAranda}. Let `GL(R)` and `EL(R)` be the direct
limits of `GL_n(R)` and `EL_n(R)` along `A↦diag(A,1)`; the subgroup `EL(R)` is
normal in `GL(R)` by Whitehead's lemma, and `K_1(R)=GL(R)/EL(R)`. Write
`κ:R^×→K_1(R)` for the canonical map."

Every definition and every fact in this paragraph already has an exact,
hypothesis-free carrier elsewhere in the tree:

* equivalent idempotents — `MFQuotientUnits.IsEquivalentIdempotent`;
* infinite idempotent — `MFQuotientUnits.IsInfiniteIdempotent`;
* purely infinite simple ring (the AGP idempotent form, element-wise on the
  right-ideal clause) — `MFQuotientUnits.IsPurelyInfiniteSimpleRing`;
* "`L_k(1,d)` purely infinite simple", for every field `k` and every `d ≥ 2`,
  with no Ara–Goodearl–Pardo input — `AryLeavitt.isPurelyInfiniteSimpleRing`;
* `GL(R)`, `EL(R)` — `ClassicalGLColim`, `elementaryColim`;
* "`EL(R)` normal in `GL(R)` by Whitehead's lemma" —
  `StableWhitehead.elementaryColim_normal` (an instance, proved from
  `StableWhitehead.commutator_le_elementaryColim`, the actual Whitehead
  factorization);
* `K_1(R) = GL(R)/EL(R)` — `AlgebraicK.AlgebraicKOne`;
* the canonical map `κ` — `AlgebraicK.kappa`.

No new declaration is introduced in this section: each row of this lane's
census file cites the existing declaration above directly, since a fresh
`abbrev`/alias would only be a duplicate. -/

end BinaryExampleSentences
end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation
open GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences

-- Closed endpoints (no leading binders): `#audit_closed_axioms`.
#audit_closed_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_leavittModuleEquivProd
#audit_closed_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_unitsEquivGLFourEqELFour
#audit_closed_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_weIdentifyHWithELFour
#audit_closed_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_relationsGiveTrivialHomomorphisms
#audit_closed_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_e12OneForcesNontrivial
#audit_closed_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_letNBeNormalSubgroup
#audit_closed_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_HIsSimple
#audit_closed_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_HNontrivialAndNotMF
#audit_closed_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_reducedAndMaximalCStarClauses

-- Intermediate lemmas of the printed case-split proof (ordinary mathematical
-- hypotheses as leading binders, per house rule 9): `#audit_axioms`.
#audit_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_purelyInfiniteExchangePreusserSandwich
#audit_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_simpleGivesTrichotomy
#audit_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_idealTopGivesNEqTop
#audit_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_idealZeroGivesCentral
#audit_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_fixGInN
#audit_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_commutingSingleForcesScalar
#audit_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_commutingGeneralForcesCentral
#audit_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_centerEqF2GivesGEqOne
#audit_axioms
  Manuscript.NonMFSentences.BinaryExampleSentences.manuscriptSentence_thusNTrivial
