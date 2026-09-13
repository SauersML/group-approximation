import Mathlib.GroupTheory.HNNExtension
import GroupApproximation.Criterion.CompressionCentralizerDefect
import GroupApproximation.Leavitt.FullIdempotentNormalGeneration
import GroupApproximation.Leavitt.ProperlyInfiniteUnit
import GroupApproximation.Manuscript.OneSidedMFRadical.UniversalGroupB
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Meta.AxiomGuard

/-!
# Introduction, tex 182–219: the criterion, compressors and the universal ring

`non_mf_groups_exist.tex`, Introduction.  Four sentences whose census carriers were missing,
or were stated below the printed generality.  Each is a named proposition with a closed proof.

* census key `270c3118af88`, tex 182–185:
  "The criterion behind every example is Theorem~\ref{thm:compression-criterion}: for a
  property-(T) subgroup $L\le G$, every normal property-(T) subgroup of $G$ inside
  $\mathfrak D_G(L)$ dies in every MF image."
  The theorem it names is printed for countable `G`, and "dies in every MF image" is its clause
  "every homomorphism from $G$ to an MF group is trivial on $K$".  The radical form
  `manuscriptOneSidedCompressionCriterion` stops at `K ≤ manuscriptCoronaMFResidual G`; the step
  to every MF target is the residual calculus, as in `manuscriptFullRadicalKillsMFTargets`.
* census key `9bab404c96c5`, tex 207–208:
  "The stable letter of an ascending HNN extension of a property-(T) group along a proper
  self-embedding is a compressor."
  The extension is Mathlib's `HNNExtension L ⊤ φ(L)`, associating the whole group with its image.
* census key `6b5d4b5c3081`, tex 211–215:
  "A pair $s,t\in R$ with $ts=1$ gives a compressor in the same way: an explicit element
  $u\in\EL_4(R)$ conjugates $\EL_3(R)$ into itself by $e_{ij}(a)\mapsto e_{ij}(sat)$, and if
  $1-st$ generates $R$ as a two-sided ideal, then one commutator $[ucu^{-1},\ell]$ normally
  generates all of $\EL_4(R)$."
  Over every unital ring.  The explicit `u` is `OneSidedCompressor.compressor`, `c` is
  `OneSidedCompressor.centralMark` and `ℓ = e₂₃(1)` is `OneSidedCompressor.printedEll`.
* census key `29d7a8ccf93a`, tex 215–219:
  "It suffices to do this once, in the universal unital associative ring
  $\mathcal C=\mathbb Z\langle s_0,s_1,t_0,t_1\rangle/(t_is_j-\delta_{ij}:i,j\in\{0,1\})$, since
  $\EL_4(\mathcal C)$ maps to every $\EL_n(R)$ below with normally generating image."
  "Below" is Theorem~\ref{thm:full-defect-ring}: countable unital `R` with `ts = 1` and `1 - st`
  full, every `n ≥ 2`.  `𝒞` is `UniversalPair.UniversalPairRing`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace IntroCompressorSentences

open scoped commutatorElement

/-! ## tex 182–185, `270c3118af88`: every MF image kills `K` -/

/-- **Introduction, tex 182–185.**

> for a property-(T) subgroup $L\le G$, every normal property-(T) subgroup of $G$ inside
> $\mathfrak D_G(L)$ dies in every MF image.

At the generality of Theorem~\ref{thm:compression-criterion}: `G` countable, every MF target
group `M`, every homomorphism `f : G → M`. -/
def PrintedIntroCriterionKillsMFImages : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      ∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
        K ≤ OneSidedMFRadical.printedDefect L →
          ∀ (M : Type) [Group M], IsOperatorMF M →
            ∀ (f : G →* M), ∀ k ∈ K, f k = 1

/-- **Introduction, tex 182–185, proved.**  The criterion puts `K` in the corona MF residual; the
image of `f` is a countable MF group, whose residual is trivial, and residuals map into
residuals. -/
theorem manuscriptSentence_introCriterionKillsMFImages :
    PrintedIntroCriterionKillsMFImages := by
  intro G _ _ L hL K _ hK hKD M _ hM f k hk
  have hres : k ∈ manuscriptCoronaMFResidual G :=
    (OneSidedMFRadical.manuscriptOneSidedCompressionCriterion G L hL).1 K hK hKD hk
  letI : Countable f.range :=
    Function.Surjective.countable f.rangeRestrict_surjective
  have hRangeMF : IsOperatorMF f.range := by
    obtain ⟨X, hX, ρ, hρ⟩ := hM
    exact ⟨X, hX, ρ.comp f.range.subtype, hρ.comp (fun _ _ h ↦ Subtype.ext h)⟩
  have hbot : manuscriptCoronaMFResidual f.range = ⊥ :=
    isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot.mp
      ((isCDEOperatorMF_iff_isOperatorMF f.range).mpr hRangeMF)
  have hle := map_manuscriptCoronaMFResidual_le f.rangeRestrict
    (Subgroup.mem_map_of_mem f.rangeRestrict hres)
  rw [hbot] at hle
  have h1 : f.rangeRestrict k = 1 := by simpa using hle
  simpa using congrArg Subtype.val h1

/-! ## tex 207–208, `9bab404c96c5`: the stable letter of an ascending HNN extension -/

/-- The associating isomorphism of the ascending HNN extension of `L` along an injective
endomorphism `φ`: the whole group, as the subgroup `⊤`, onto its image `φ(L)`. -/
noncomputable def ascendingIso {L : Type} [Group L] (φ : L →* L)
    (hφ : Function.Injective φ) : (⊤ : Subgroup L) ≃* φ.range :=
  Subgroup.topEquiv.trans (MonoidHom.ofInjective hφ)

/-- **Introduction, tex 207–208.**

> The stable letter of an ascending HNN extension of a property-(T) group along a proper
> self-embedding is a compressor.

For every group `L` with property (T) and every injective endomorphism `φ` with `φ(L) ≠ L`, the
stable letter `t` of `HNNExtension L ⊤ φ(L)` is a compressor of the copy `of(L)`:
`t · of(L) · t⁻¹ ≤ of(L)`. -/
def PrintedAscendingHNNStableLetterCompressor : Prop :=
  ∀ (L : Type) [Group L], HasKazhdanPropertyT.{0, 0} L →
    ∀ (φ : L →* L) (hφ : Function.Injective φ), φ.range ≠ ⊤ →
      (HNNExtension.t : HNNExtension L ⊤ φ.range (ascendingIso φ hφ)) ∈
        compressionSet
          (HNNExtension.of : L →* HNNExtension L ⊤ φ.range (ascendingIso φ hφ)).range

/-- **Introduction, tex 207–208, proved.**  `t · of(x) · t⁻¹ = of(φ x)`, which is Mathlib's
defining relation `HNNExtension.equiv_eq_conj`. -/
theorem manuscriptSentence_ascendingHNNStableLetterCompressor :
    PrintedAscendingHNNStableLetterCompressor := by
  intro L _ _ φ hφ _
  rw [mem_compressionSet_iff]
  intro ℓ hℓ
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hℓ
  exact MonoidHom.mem_range.mpr
    ⟨φ x, HNNExtension.equiv_eq_conj (φ := ascendingIso φ hφ) ⟨x, Subgroup.mem_top x⟩⟩

/-! ## tex 211–215, `6b5d4b5c3081`: a pair `s, t` with `ts = 1` gives a compressor -/

/-- The printed pair `s, t` with `ts = 1`, as a one-sided inverse. -/
def pairOf {R : Type} [Ring R] (s t : R) (hts : t * s = 1) :
    OneSidedCompressor.OneSidedInverse R :=
  ⟨s, t, hts⟩

/-- **Introduction, tex 211–215.**

> A pair $s,t\in R$ with $ts=1$ gives a compressor in the same way: an explicit element
> $u\in\EL_4(R)$ conjugates $\EL_3(R)$ into itself by $e_{ij}(a)\mapsto e_{ij}(sat)$, and if
> $1-st$ generates $R$ as a two-sided ideal, then one commutator $[ucu^{-1},\ell]$ normally
> generates all of $\EL_4(R)$.

Over every unital ring `R`.  `u` is the explicit `OneSidedCompressor.compressor` of the pair,
`EL₃(R)` is the core `OneSidedCompressor.core R` on coordinates `1, 2, 3`, and "generates `R` as
a two-sided ideal" is `1 = ∑ₖ aₖ (1 - st) bₖ`. -/
def PrintedIntroPairGivesCompressor : Prop :=
  ∀ (R : Type) [Ring R] (s t : R) (hts : t * s = 1),
    OneSidedCompressor.compressor (pairOf s t hts) ∈
        compressionSet (OneSidedCompressor.core R) ∧
      (∀ (i j : Fin 3) (hij : i ≠ j) (a : R),
        OneSidedCompressor.compressor (pairOf s t hts) *
            elementaryRoot (OneSidedCompressor.coreIdx i) (OneSidedCompressor.coreIdx j)
              (OneSidedCompressor.coreIdx_injective.ne hij) a *
            (OneSidedCompressor.compressor (pairOf s t hts))⁻¹ =
          elementaryRoot (OneSidedCompressor.coreIdx i) (OneSidedCompressor.coreIdx j)
            (OneSidedCompressor.coreIdx_injective.ne hij) (s * a * t)) ∧
      ((∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
        ∃ c : elementaryGroup (Fin 4) R, (∀ g ∈ OneSidedCompressor.core R, Commute c g) ∧
          ∃ ℓ ∈ OneSidedCompressor.core R,
            Subgroup.normalClosure
              ({⁅OneSidedCompressor.compressor (pairOf s t hts) * c *
                  (OneSidedCompressor.compressor (pairOf s t hts))⁻¹, ℓ⁆} :
                Set (elementaryGroup (Fin 4) R)) = ⊤)

/-- **Introduction, tex 211–215, proved.**  The general lemmas of `OneSidedCompressor` at the
pair, and normal generation from the full idempotent
(`FullIdempotent.elementaryGroup_normal_eq_top_of_full`). -/
theorem manuscriptSentence_introPairGivesCompressor : PrintedIntroPairGivesCompressor := by
  intro R _ s t hts
  refine ⟨OneSidedCompressor.compressor_mem_compressionSet _, ?_, ?_⟩
  · intro i j hij a
    exact mul_inv_eq_of_eq_mul (OneSidedCompressor.compressor_mul_coreRoot _ i j hij a)
  · intro hfull
    refine ⟨OneSidedCompressor.centralMark (pairOf s t hts),
      OneSidedCompressor.centralMark_commute_core _, OneSidedCompressor.printedEll R,
      OneSidedCompressor.printedEll_mem_core, ?_⟩
    rw [OneSidedCompressor.defect_eq]
    exact FullIdempotent.elementaryGroup_normal_eq_top_of_full (by simp) _
      (OneSidedCompressor.coreIdx_injective.ne OneSidedCompressor.zeroNeTwo)
      (Subgroup.subset_normalClosure rfl) hfull

/-! ## tex 215–219, `29d7a8ccf93a`: `EL₄(𝒞)` maps onto a normal generating set of `EL_n(R)` -/

/-- **Introduction, tex 215–219.**

> since $\EL_4(\mathcal C)$ maps to every $\EL_n(R)$ below with normally generating image.

"Below" is the setting of Theorem~\ref{thm:full-defect-ring}: every countable unital ring `R`
with `ts = 1` and `1 - st` full, and every `n ≥ 2`. -/
def PrintedIntroUniversalGroupMapsEveryEL : Prop :=
  ∀ (R : Type) [Ring R] [Countable R] (s t : R), t * s = 1 →
    (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
      ∀ (n : ℕ), 2 ≤ n →
        ∃ φ : elementaryGroup (Fin 4) UniversalPair.UniversalPairRing →*
            elementaryGroup (Fin n) R,
          Subgroup.normalClosure (φ.range : Set (elementaryGroup (Fin n) R)) = ⊤

/-- **Introduction, tex 215–219, proved.**  Two copies from the full idempotent
(`RankDescent.ofFull`, Lemma~\ref{lem:two-copies}), then
`UniversalGroupB.exists_hom_normallyGenerating`. -/
theorem manuscriptSentence_introUniversalGroupMapsEveryEL :
    PrintedIntroUniversalGroupMapsEveryEL := by
  intro R _ _ s t hts hfull n hn
  obtain ⟨m, a, b, hab⟩ := hfull
  exact OneSidedMFRadical.UniversalGroupB.exists_hom_normallyGenerating
    (RankDescent.ofFull (pairOf s t hts) a b hab) n hn

end IntroCompressorSentences
end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMFSentences

#audit_closed_axioms IntroCompressorSentences.manuscriptSentence_introCriterionKillsMFImages
#audit_closed_axioms IntroCompressorSentences.manuscriptSentence_ascendingHNNStableLetterCompressor
#audit_closed_axioms IntroCompressorSentences.manuscriptSentence_introPairGivesCompressor
#audit_closed_axioms IntroCompressorSentences.manuscriptSentence_introUniversalGroupMapsEveryEL
