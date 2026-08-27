import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.RadicalFunctoriality
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.CommensurabilityInvariance
import GroupApproximation.Manuscript.OneSidedMFRadical.LiteralMFClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedResidualCalculusProof
import GroupApproximation.Algebra.CountableInstances

/-!
# Sentence-level proof of `prop:mf-residual-calculus`, current revision

`non_mf_groups_exist.tex`, the proof of

```
\begin{proposition}[basic properties of the MF radical]
\label{prop:mf-residual-calculus}
```

as printed at the current revision.  The proof paragraph reads (with `R`
short for `Rad_MF(G)`):

1. "An intersection of kernels is normal.  If `α : G → G` is an endomorphism
   and `x ∈ Rad_MF(G)`, then every corona homomorphism `π` satisfies
   `π(α(x)) = (π ∘ α)(x) = 1`."
2. "Thus the radical is fully invariant."
3. "Put `R = Rad_MF(G)`.  If `1 ≠ x ∈ G/R` and `g` represents `x`, then
   `g ∉ R`, so a homomorphism from `G` to an MF group separates `g` from `1`."
4. "It kills `R` and induces a homomorphism separating `x`."
5. "So `G/R` is residually MF, and MF by Korchagin [Proposition 6]; this also
   covers the trivial quotient."
6. "Finally, a corona embedding gives `Rad_MF(G) = 1` when `G` is MF, and the
   quotient result gives the converse."

Each sentence is a `def ... : Prop` named after the fleet's per-sentence audit
key, together with a `theorem manuscriptSentence_<key>` proving it.

## Relation to `PrintedResidualCalculusProof.lean`

That module formalizes an *earlier, longer* printed proof of the same
proposition — ten sentences built around a direct diagonalization
construction of a marked almost-representation of `G/R`.  Sentences 1 and 2
above are verbatim identical between the two proof texts (`α`, `π ∘ α`, full
invariance), so this file reuses `PrintedResidualCalculusProof`'s own
declarations for them rather than re-deriving.  Sentences 3–6 are new: the
current proof text replaces the old diagonalization argument for "`G/R` is
MF" with a citation of Korchagin's residually-MF criterion, and no sentence
of the old proof matches that citation.  The tree's existing *unconditional*
proof that `G ⧸ Rad_MF(G)` is MF
(`ActualCoronaMFRadical.actualCoronaMFQuotient_isCDEOperatorMF`) is not used
here on purpose: it goes by the old diagonalization route, and using it would
substitute a different argument for the one the current text cites, breaking
the printed proof's own dependency graph.  Korchagin's Proposition 6 is
therefore entered below as a literature input, exactly where the manuscript
cites it, and the sentence-5 theorem uses only sentences 3 and 4 plus that
input.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

noncomputable section

attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

/-! ## Sentence `6b6db6812331`

"An intersection of kernels is normal.  If `α : G → G` is an endomorphism and
`x ∈ Rad_MF(G)`, then every corona homomorphism `π` satisfies
`π(α(x)) = (π ∘ α)(x) = 1`." -/

/-- **Sentence `6b6db6812331`.**  This exact sentence pair is already stated
and proved, verbatim, by `PrintedResidualCalculusProof`'s first two
declarations (the printed text is unchanged there); nothing new is derived
here. -/
theorem manuscriptSentence_6b6db6812331 :
    PrintedIntersectionOfKernelsIsNormal ∧
      PrintedFullInvarianceThroughComposition :=
  ⟨manuscriptPrintedIntersectionOfKernelsIsNormal,
    manuscriptPrintedFullInvarianceThroughComposition⟩

/-! ## Sentence `c607d5888749`

"Thus the radical is fully invariant." -/

/-- **Sentence `c607d5888749`.** -/
def RadicalIsFullyInvariant : Prop :=
  ∀ (G : Type) [Group G], RadicalFunctoriality.IsFullyInvariant
    (actualCoronaMFResidual G)

/-- Closed proof, read off the second conjunct of
`PrintedFullInvarianceThroughComposition`, which already carries exactly this
clause. -/
theorem manuscriptSentence_c607d5888749 : RadicalIsFullyInvariant :=
  fun G _ ↦ (manuscriptPrintedFullInvarianceThroughComposition G).2

/-! ## Sentence `895c79044a40`

"Put `R = Rad_MF(G)`.  If `1 ≠ x ∈ G/R` and `g` represents `x`, then
`g ∉ R`, so a homomorphism from `G` to an MF group separates `g` from `1`." -/

/-- **Sentence `895c79044a40`.**  The nonmembership clause is
`QuotientGroup.eq_one_iff`.  The separating homomorphism is extracted from
the negation of `mem_literalMFClosure_iff` at `N = ⊥`: `R = Rad_MF(G)` is
`literalMFClosure G ⊥` (`literalMFClosure_bot`, read through
`manuscriptCoronaMFResidual_eq_actualCoronaMFResidual`), and that closure is
by definition the intersection of the kernels of all homomorphisms from `G`
into countable MF groups — the manuscript's own characterization of `R` from
the "MF radical" section a few paragraphs earlier. -/
def SeparatingHomToMFGroupFromNonMembership : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (x : G ⧸ actualCoronaMFResidual G)
      (g : G), x ≠ 1 → (QuotientGroup.mk g : G ⧸ actualCoronaMFResidual G) = x →
    g ∉ actualCoronaMFResidual G ∧
      ∃ (M : Type) (_ : Group M) (_ : Countable M),
        IsCDEOperatorMF M ∧ ∃ f : G →* M, f g ≠ 1

theorem manuscriptSentence_895c79044a40 :
    SeparatingHomToMFGroupFromNonMembership := by
  intro G _ _ x g hx hgx
  have hg1 : (QuotientGroup.mk g : G ⧸ actualCoronaMFResidual G) ≠ 1 := by
    rw [hgx]; exact hx
  have hgR : g ∉ actualCoronaMFResidual G := fun hmem ↦
    hg1 ((QuotientGroup.eq_one_iff g).mpr hmem)
  refine ⟨hgR, ?_⟩
  have heq : literalMFClosure G (⊥ : Subgroup G) = actualCoronaMFResidual G :=
    literalMFClosure_bot.trans manuscriptCoronaMFResidual_eq_actualCoronaMFResidual
  have hgClosure : g ∉ literalMFClosure G (⊥ : Subgroup G) := by
    rw [heq]; exact hgR
  rw [mem_literalMFClosure_iff] at hgClosure
  simp only [not_forall] at hgClosure
  obtain ⟨M, instM, instC, f, hMF, -, hfg⟩ := hgClosure
  exact ⟨M, instM, instC, hMF, f, hfg⟩

/-! ## Sentence `3a8a0f98943e`

"It kills `R` and induces a homomorphism separating `x`." -/

/-- **Sentence `3a8a0f98943e`.**  Continuing from `895c79044a40`: any
homomorphism `f` into a countable MF group that separates a point from `1`
has `f.ker` among the kernels intersected by `literalMFClosure G ⊥`
(`mem_literalMFKernels`), so `R ≤ f.ker` by `literalMFClosure_le`; the
induced homomorphism on `G ⧸ R` is `QuotientGroup.lift`, and it still
separates the class of `g`. -/
def SeparatingHomKillsRadicalAndDescends : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (M : Type) [Group M] [Countable M],
    IsCDEOperatorMF M → ∀ (f : G →* M) (g : G), f g ≠ 1 →
      actualCoronaMFResidual G ≤ f.ker ∧
        ∃ fBar : (G ⧸ actualCoronaMFResidual G) →* M,
          fBar.comp (QuotientGroup.mk' (actualCoronaMFResidual G)) = f ∧
            fBar (QuotientGroup.mk g) ≠ 1

theorem manuscriptSentence_3a8a0f98943e :
    SeparatingHomKillsRadicalAndDescends := by
  intro G _ _ M _ _ hM f g hfg
  have hmem : f.ker ∈ LiteralMFKernels G (⊥ : Subgroup G) :=
    mem_literalMFKernels.mpr ⟨M, inferInstance, inferInstance, f, hM, bot_le, rfl⟩
  have hle : literalMFClosure G (⊥ : Subgroup G) ≤ f.ker :=
    literalMFClosure_le hmem
  have heq : literalMFClosure G (⊥ : Subgroup G) = actualCoronaMFResidual G :=
    literalMFClosure_bot.trans manuscriptCoronaMFResidual_eq_actualCoronaMFResidual
  have hR : actualCoronaMFResidual G ≤ f.ker := by rw [← heq]; exact hle
  refine ⟨hR, QuotientGroup.lift (actualCoronaMFResidual G) f hR, ?_, ?_⟩
  · exact MonoidHom.ext fun _ ↦ rfl
  · exact hfg

/-! ## Sentence `ed55ca682c3d`

"So `G/R` is residually MF, and MF by Korchagin [Proposition 6]; this also
covers the trivial quotient." -/

/-- The development's reading of "residually MF": every nonidentity element
is separated from `1` by a homomorphism into a countable MF group.  Vacuously
true for the trivial group, which is how "this also covers the trivial
quotient" is realized: no separate case is needed. -/
def IsResiduallyOperatorMF (Q : Type) [Group Q] : Prop :=
  ∀ x : Q, x ≠ 1 → ∃ (M : Type) (_ : Group M) (_ : Countable M),
    IsCDEOperatorMF M ∧ ∃ f : Q →* M, f x ≠ 1

/-- **`G ⧸ Rad_MF(G)` is residually MF.**  Combines `895c79044a40` and
`3a8a0f98943e`: for `x ≠ 1`, choose a representative `g`, extract the
separating homomorphism to a countable MF group, and descend it. -/
theorem actualCoronaMFQuotient_isResiduallyOperatorMF
    (G : Type) [Group G] [Countable G] :
    IsResiduallyOperatorMF (G ⧸ actualCoronaMFResidual G) := by
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨-, M, instM, instC, hM, f, hfg⟩ :=
    manuscriptSentence_895c79044a40 G (QuotientGroup.mk g) g hx rfl
  obtain ⟨hR, fBar, -, hfBar⟩ :=
    manuscriptSentence_3a8a0f98943e G M hM f g hfg
  exact ⟨M, instM, instC, hM, fBar, hfBar⟩

/-- **LITERATURE INPUT (sorry): Korchagin, Proposition 6.**  A countable
residually-MF group is MF.  The printed proof of `prop:mf-residual-calculus`
cites this fact rather than re-proving it.  The tree's existing unconditional
proof that `G ⧸ Rad_MF(G)` is MF
(`ActualCoronaMFRadical.actualCoronaMFQuotient_isCDEOperatorMF`) is a
different argument (direct diagonalization of a marked almost-representation)
and is deliberately not substituted here, so that this file's dependency
graph matches the printed proof's own. -/
-- LITERATURE INPUT (sorry): Korchagin, Proposition 6
theorem isCDEOperatorMF_of_isResiduallyOperatorMF
    (Q : Type) [Group Q] [Countable Q] (hQ : IsResiduallyOperatorMF Q) :
    IsCDEOperatorMF Q := by
  sorry

/-- **Sentence `ed55ca682c3d`, both clauses.** -/
def RadicalQuotientResiduallyMFAndMF : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    IsResiduallyOperatorMF (G ⧸ actualCoronaMFResidual G) ∧
      IsCDEOperatorMF (G ⧸ actualCoronaMFResidual G)

theorem manuscriptSentence_ed55ca682c3d : RadicalQuotientResiduallyMFAndMF := by
  intro G _ _
  have hres := actualCoronaMFQuotient_isResiduallyOperatorMF G
  exact ⟨hres, isCDEOperatorMF_of_isResiduallyOperatorMF _ hres⟩

/-! ## Sentence `248778b8c409`

"Finally, a corona embedding gives `Rad_MF(G) = 1` when `G` is MF, and the
quotient result gives the converse." -/

/-- `IsCDEOperatorMF` transports along a group isomorphism.  Not already in
the tree; built from `CommensurabilityInvariance.isOperatorMF_of_mulEquiv`
and `isCDEOperatorMF_iff_isOperatorMF`. -/
theorem isCDEOperatorMF_of_mulEquiv {G H : Type} [Group G] [Group H]
    [Countable G] [Countable H] (e : G ≃* H) (hG : IsCDEOperatorMF G) :
    IsCDEOperatorMF H :=
  (isCDEOperatorMF_iff_isOperatorMF H).mpr
    (CommensurabilityInvariance.isOperatorMF_of_mulEquiv e
      ((isCDEOperatorMF_iff_isOperatorMF G).mp hG))

/-- **Sentence `248778b8c409`.**  Forward direction:
`isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot`'s forward half — a corona
embedding of `G` gives a trivial radical.  Backward direction: "the quotient
result", i.e. `ed55ca682c3d` specialized at `R = ⊥` and transported across
`QuotientGroup.quotientBot : G ⧸ ⊥ ≃* G`. -/
def PrintedRadicalTrivialIffMF : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    (IsCDEOperatorMF G → actualCoronaMFResidual G = ⊥) ∧
      (actualCoronaMFResidual G = ⊥ → IsCDEOperatorMF G)

theorem manuscriptSentence_248778b8c409 : PrintedRadicalTrivialIffMF := by
  intro G _ _
  refine ⟨fun hG ↦ isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hG, ?_⟩
  intro hbot
  have hMFquot : IsCDEOperatorMF (G ⧸ actualCoronaMFResidual G) :=
    (manuscriptSentence_ed55ca682c3d G).2
  have hinj : Function.Injective (QuotientGroup.mk' (actualCoronaMFResidual G)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hbot
  have hbij : Function.Bijective (QuotientGroup.mk' (actualCoronaMFResidual G)) :=
    ⟨hinj, QuotientGroup.mk'_surjective _⟩
  exact isCDEOperatorMF_of_mulEquiv (MulEquiv.ofBijective _ hbij).symm hMFquot

/-! ## The current printed proof, assembled -/

/-- Every sentence of the current printed proof of
`prop:mf-residual-calculus`, in printed order, as one closed proposition. -/
def PrintedResidualCalculusProofCurrent : Prop :=
  (PrintedIntersectionOfKernelsIsNormal ∧ PrintedFullInvarianceThroughComposition) ∧
    RadicalIsFullyInvariant ∧
    SeparatingHomToMFGroupFromNonMembership ∧
    SeparatingHomKillsRadicalAndDescends ∧
    RadicalQuotientResiduallyMFAndMF ∧
    PrintedRadicalTrivialIffMF

theorem manuscriptPrintedResidualCalculusProofCurrent :
    PrintedResidualCalculusProofCurrent :=
  ⟨manuscriptSentence_6b6db6812331, manuscriptSentence_c607d5888749,
    manuscriptSentence_895c79044a40, manuscriptSentence_3a8a0f98943e,
    manuscriptSentence_ed55ca682c3d, manuscriptSentence_248778b8c409⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
