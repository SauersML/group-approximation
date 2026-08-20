import GroupApproximation.Higman.BlockComputable
import GroupApproximation.Higman.QuotientPresentation
import GroupApproximation.Higman.RadicalDirectSum
import GroupApproximation.Higman.TowerBlockSearch
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
2. (B2), Chiodo Proposition 3.8: the universal torsion-free quotient of a
   recursively presented group is recursively presented.  By
   `Higman.QuotientPresentation` this is *one* recursive-enumerability
   statement, about membership in the stages of Chiodo's tower, and
   `statement_of_tower_re` below takes it in that sharp form.
3. (A), `Higman.TorsionFreeHigmanEmbedding`: Chiodo's Theorem 2.2, i.e.
   Higman's embedding theorem with the torsion-order clause.  This is the deep
   one, and `Higman.Benign`, `Higman.BenignClosure`, `Higman.BenignAmbient`,
   `Higman.BenignJoin` and `Higman.Pinch` are the beginning of its proof.

Nothing here inhabits either remaining input, so the corpus audit keeps
reporting them open.

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
open GroupApproximation.PresentationCodes

/-- A torsion-free Higman hull of the computable absorber already contains
every finitely presented torsion-free group. -/
theorem statement_of_pcAbsorber_hull
    (H : ChiodoHost.TorsionFreeHigmanHull PCAbsorber) :
    ChiodoBelegradek.Statement :=
  ChiodoBelegradek.statement_of_host
    { Carrier := H.Carrier
      groupCarrier := H.groupCarrier
      finitelyPresentedCarrier := H.finitelyPresentedCarrier
      torsionFree := H.torsionFree
      universal := universal_of_embedding_pcAbsorber H.emb H.emb_injective }

/-- **The theorem, from the two inputs that are actually still open.**

(B1) is proved (`Higman.recursivePresentationPCDirectSum`), so what remains is
Chiodo's Proposition 3.8 in the sharp form `Higman.QuotientPresentation`
reduces it to, and Chiodo's Theorem 2.2. -/
theorem statement_of_tower_re
    (hB2 : REPred fun w : RawWord ↦
      ∃ i : ℕ, evalRaw pcGen w ∈ torsionTower PCDirectSum i)
    (hA : TorsionFreeHigmanEmbedding) :
    ChiodoBelegradek.Statement := by
  obtain ⟨H⟩ := hA.hull PCAbsorber
    (recursivePresentationQuotient recursivePresentationPCDirectSum hB2)
    pcAbsorber_torsionFree
  exact statement_of_pcAbsorber_hull H

/-- **The theorem, from the two remaining inputs in their sharpest form.**

(B1) is proved.  (B2) has been localized by `Higman.RadicalDirectSum` from a
statement about the infinitely generated `PCDirectSum` to the block-by-block
radical-membership predicate of *finitely presented* coded groups, which is
Chiodo's Proposition 3.8 in the form he states effectively.  (A) is Higman's
embedding theorem with the torsion clause; `Higman.Pinch` and
`Higman.RopeTrick` are the parts of it that are proved. -/
theorem statement_of_block_radical_re
    (hB2 : REPred fun w : RawWord ↦ ∀ c ∈ blockList w,
      evalRaw (fun k ↦ (PresentedGroup.of (letterOf c k) : Carrier c))
        (blockWord w c) ∈ torsionFreeRadical (Carrier c))
    (hA : TorsionFreeHigmanEmbedding) :
    ChiodoBelegradek.Statement := by
  obtain ⟨H⟩ := hA.hull PCAbsorber (recursivePresentationPCAbsorber hB2)
    pcAbsorber_torsionFree
  exact statement_of_pcAbsorber_hull H

/-- **The theorem, from Higman's embedding theorem alone.**

Input (B) of `Higman.Program` --- Chiodo's Proposition 3.8 at the absorber ---
is discharged: (B1) is `Higman.recursivePresentationPCDirectSum` and (B2) is
`Higman.recursivePresentationPCAbsorberFull`.  So the only hypothesis left is
(A), Chiodo's Theorem 2.2, i.e. Higman's embedding theorem with the
torsion-order clause. -/
theorem statement_of_higman (hA : TorsionFreeHigmanEmbedding) :
    ChiodoBelegradek.Statement := by
  obtain ⟨H⟩ := hA.hull PCAbsorber recursivePresentationPCAbsorberFull
    pcAbsorber_torsionFree
  exact statement_of_pcAbsorber_hull H

end Higman
end GroupApproximation
