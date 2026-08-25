import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefinitions
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedRemarks
import GroupApproximation.Manuscript.OneSidedMFRadical.LiteralMFClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion

/-!
# Sentence closure for the introductory definitions and calculus

Row-numbered wrappers for the mathematical content of census rows 11--30.
Row 16 is historical terminology/attribution and is intentionally absent.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

universe u

/-- The quotient occurring in sentence 24 is countable because its canonical
projection is surjective. -/
local instance sentence24QuotientCountable
    {G : Type} [Group G] [Countable G]
    (N : Subgroup G) [hN : N.Normal] : Countable (G ⧸ N) :=
  Function.Surjective.countable
    (@QuotientGroup.mk'_surjective G _ N hN)

/-- **Sentence 11.**  The printed MF definition is embedding into a genuine
norm-matrix C-star corona with positive increasing dimensions. -/
theorem manuscriptSentence11_MFDefinition
    (G : Type u) [Group G] [Countable G] :
    IsCDEOperatorMF G ↔
      ∃ d : ℕ → ℕ, ∃ hd : ∀ n, 0 < d n,
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) := fun n ↦
          Fintype.card_pos_iff.mp (by simpa using hd n)
        StrictMono d ∧
          ∃ rho : G →* unitary (NormMatrixCStarCorona
            (fun n ↦ naturalFiniteModel (d n))), Function.Injective rho :=
  Iff.rfl

/-- **Sentences 12--14.**  The norm-matrix corona is the bounded product
modulo exactly the sequences whose coordinate norms tend to zero. -/
theorem manuscriptSentences12_14_corona_and_c0Denominator :
    PrintedCoronaDenominator :=
  manuscriptCoronaDenominator

/-- **Sentence 15.**  The corona-embedding definition is equivalent to the
printed asymptotically multiplicative, separating finite-dimensional unitary
models. -/
theorem manuscriptSentence15_MFUnitaryModels :
    PrintedMFUnitaryModels :=
  manuscriptMFUnitaryModels

/-- **Sentence 17.**  The displayed radical intersection has the literal
universal-corona membership predicate. -/
theorem manuscriptSentence17_MFRadicalDisplay
    {G : Type u} [Group G] (x : G) :
    x ∈ manuscriptCoronaMFResidual G ↔ ManuscriptCoronaMFInvisible x :=
  mem_manuscriptCoronaMFResidual_iff

/-- **Sentence 18.**  A countable group is MF exactly when its printed radical
is trivial. -/
theorem manuscriptSentence18_MF_iff_radical_bot
    (G : Type) [Group G] [Countable G] :
    IsCDEOperatorMF G ↔ manuscriptCoronaMFResidual G = ⊥ :=
  (manuscriptMFResidualCalculusLiteral G).2.2.2

/-- **Sentence 19.**  Full MF radical kills every homomorphism into every
countable MF target. -/
theorem manuscriptSentence19_fullRadical_kills_MFTargets :
    FullRadicalKillsMFTargets :=
  manuscriptFullRadicalKillsMFTargets

/-- **Sentence 20.**  Membership in the printed MF closure is membership in
every MF-target kernel that contains the relation subgroup. -/
theorem manuscriptSentence20_MFClosureDisplay
    {G : Type} [Group G] {N : Subgroup G} {x : G} :
    x ∈ literalMFClosure G N ↔
      ∀ (M : Type) (_ : Group M) (_ : Countable M) (f : G →* M),
        IsCDEOperatorMF M → N ≤ f.ker → f x = 1 :=
  mem_literalMFClosure_iff

/-- **Sentences 21--22.**  Corona images are countable MF groups, and every
MF target embeds in a norm-matrix corona. -/
theorem manuscriptSentences21_22_coronaImages_and_MFTargets :
    PrintedCoronaImagesAndTargets :=
  manuscriptCoronaImagesAndTargets

/-- **Sentence 23.**  The MF radical is the printed closure of the trivial
subgroup. -/
theorem manuscriptSentence23_radical_is_closure_bot :
    LiteralMFRadicalIsClosureOfTrivial :=
  manuscriptMFRadicalIsLiteralClosureOfTrivial

/-- **Sentence 24.**  Quotient MF-ness is exactly fixedness under the printed
MF closure. -/
theorem manuscriptSentence24_quotientMF_iff_closureFixed
    (G : Type) [Group G] [Countable G]
    (N : Subgroup G) [N.Normal] :
    IsCDEOperatorMF (G ⧸ N) ↔ literalMFClosure G N = N :=
  isCDEOperatorMF_quotient_iff_literalMFClosure_eq N

/-- **Sentences 25--28.**  Full invariance, MF-ness of the radical quotient,
the closure criterion, and the trivial-radical criterion. -/
theorem manuscriptSentences25_28_basicResidualCalculus :
    LiteralMFResidualCalculus :=
  manuscriptMFResidualCalculusLiteral

/-- **Sentence 29.**  Arbitrary intersections of kernels are normal. -/
theorem manuscriptSentence29_intersectionOfKernels_normal :
    IntersectionOfKernelsIsNormal :=
  manuscriptIntersectionOfKernelsIsNormal

/-- **Sentence 30.**  Precomposition by an endomorphism preserves universal
corona invisibility, hence the printed radical is fully invariant. -/
theorem manuscriptSentence30_endomorphism_preserves_radical
    (G : Type) [Group G] [Countable G] (alpha : G →* G) :
    (manuscriptCoronaMFResidual G).map alpha ≤
      manuscriptCoronaMFResidual G :=
  map_manuscriptCoronaMFResidual_le alpha

end OneSidedMFRadical
end Manuscript
end GroupApproximation
