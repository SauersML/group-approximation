import GroupApproximation.Higman.BlockComputable
import GroupApproximation.Higman.QuotientPresentation
import GroupApproximation.Sofic.ChiodoBelegradekTheorem

/-!
# Chiodo/Belegradek from three stated inputs

`Sofic.ChiodoBelegradekTheorem` states the theorem as one closed formula,
`ChiodoBelegradek.Statement`, and proves everything about it except finite
presentation.  `Higman.Program` itemizes what finite presentation costs.  This
file composes the itemization with the work of `Higman.CodedAbsorber`,
`Higman.BlockDecomposition`, `Higman.BlockWordProblem` and
`Higman.BlockSearch`, and the result is that the theorem now stands on exactly
three hypotheses, each stated precisely:

1. ~~(B1)~~ --- **no longer a hypothesis.**  `Higman.BlockComputable` proves
   `Primrec₂ Higman.blockCheck` and assembles
   `Higman.recursivePresentationPCDirectSum`, so (B1) is discharged.
   `statement_of_inputs` and `statement_of_inputs'` below keep it as an
   argument for the record; `statement_of_inputs''` is the current state and
   does not.
2. (B2), Chiodo Proposition 3.8: the universal torsion-free quotient of a
   recursively presented group is recursively presented.  By
   `Higman.QuotientPresentation` this is *one* recursive-enumerability
   statement, about membership in the stages of Chiodo's tower, and
   `statement_of_inputs'` below takes it in that sharp form.
3. (A), `Higman.TorsionFreeHigmanEmbedding`: Chiodo's Theorem 2.2, i.e.
   Higman's embedding theorem with the torsion-order clause.  This is the deep
   one, and `Higman.Benign`, `Higman.BenignClosure`, `Higman.BenignAmbient`,
   `Higman.BenignJoin` and `Higman.Pinch` are the beginning of its proof.

Nothing here inhabits any of the three, and `statement_of_inputs` takes all
three as explicit arguments, so the corpus audit keeps reporting them open.

## Why the composition is stated at `PCAbsorber` and not at `ChiodoAbsorber`

`Higman.Program`'s input (B) is stated at `Monsters.ChiodoAbsorber`, whose
index type is not `Primcodable`, so its generating family cannot be written as
a computable formula and (B1) cannot even be started there.  `PCAbsorber` is
the same construction over `PresentationCodes.PresentationCode`, and it absorbs
every finitely presented torsion-free group for the same reason
(`Higman.embeds_pcAbsorber`, from `PresentationCodes.exists_code_mulEquiv`).
Substituting it changes nothing mathematically and makes (B1) reachable.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.Chiodo

/-- **The theorem, from three stated inputs.**

Given the computability of the search matrix, Chiodo's Proposition 3.8, and
Chiodo's Theorem 2.2, there is a finitely presented torsion-free group
containing a copy of every finitely presented torsion-free group. -/
theorem statement_of_inputs
    (hcomp : Computable₂ blockCheck)
    (hB2 : ∀ (A : Type) [Group A],
      RecursivePresentation A → RecursivePresentation (TorsionFreeQuotient A))
    (hA : TorsionFreeHigmanEmbedding) :
    ChiodoBelegradek.Statement := by
  obtain ⟨H⟩ := hA.hull PCAbsorber
    (hB2 PCDirectSum (recursivePresentation_pcDirectSum hcomp))
    pcAbsorber_torsionFree
  exact ChiodoBelegradek.statement_of_embedding_pcAbsorber H.torsionFree H.emb
    H.emb_injective

/-- **The theorem, from the three inputs in their sharpest stated form.**

The difference from `statement_of_inputs` is the second hypothesis: instead of
Chiodo's Proposition 3.8 in general, only the single recursive-enumerability
statement `Higman.QuotientPresentation` reduces it to, at the one group it is
needed for. -/
theorem statement_of_inputs'
    (hcomp : Computable₂ blockCheck)
    (hB2 : REPred fun w : RawWord ↦
      ∃ i : ℕ, evalRaw pcGen w ∈ torsionTower PCDirectSum i)
    (hA : TorsionFreeHigmanEmbedding) :
    ChiodoBelegradek.Statement := by
  obtain ⟨H⟩ := hA.hull PCAbsorber
    (recursivePresentationQuotient (recursivePresentation_pcDirectSum hcomp) hB2)
    pcAbsorber_torsionFree
  exact ChiodoBelegradek.statement_of_embedding_pcAbsorber H.torsionFree H.emb
    H.emb_injective

/-- **The theorem, from the two inputs that are actually still open.**

(B1) is proved (`Higman.recursivePresentationPCDirectSum`), so what remains is
Chiodo's Proposition 3.8 in the sharp form `Higman.QuotientPresentation`
reduces it to, and Chiodo's Theorem 2.2. -/
theorem statement_of_inputs''
    (hB2 : REPred fun w : RawWord ↦
      ∃ i : ℕ, evalRaw pcGen w ∈ torsionTower PCDirectSum i)
    (hA : TorsionFreeHigmanEmbedding) :
    ChiodoBelegradek.Statement := by
  obtain ⟨H⟩ := hA.hull PCAbsorber
    (recursivePresentationQuotient recursivePresentationPCDirectSum hB2)
    pcAbsorber_torsionFree
  exact ChiodoBelegradek.statement_of_embedding_pcAbsorber H.torsionFree H.emb
    H.emb_injective

/-- The same, landing on the packaged citation
`FournierFacioUniversal.UniversalTorsionFreeHost`, which is `KC.21`'s first
input. -/
theorem nonempty_host_of_inputs
    (hcomp : Computable₂ blockCheck)
    (hB2 : ∀ (A : Type) [Group A],
      RecursivePresentation A → RecursivePresentation (TorsionFreeQuotient A))
    (hA : TorsionFreeHigmanEmbedding) :
    Nonempty FournierFacioUniversal.UniversalTorsionFreeHost := by
  obtain ⟨H⟩ := hA.hull PCAbsorber
    (hB2 PCDirectSum (recursivePresentation_pcDirectSum hcomp))
    pcAbsorber_torsionFree
  refine ⟨{ Carrier := H.Carrier
            groupCarrier := H.groupCarrier
            finitelyPresentedCarrier := H.finitelyPresentedCarrier
            torsionFree := H.torsionFree
            universal := ?_ }⟩
  exact universal_of_embedding_pcAbsorber H.emb H.emb_injective

end Higman
end GroupApproximation
