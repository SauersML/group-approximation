import GroupApproximation.GGT.DGOCorollary427FiniteExtension
import GroupApproximation.GGT.DGOLemma421Statement

/-!
# Moving Hull's long base spelling to one `W`-letter

Hull invokes DGO Corollary 4.27 before Lemma 4.21: the particular group element
he needs is adjoined to the relative base, so it is represented by one base
letter instead of a run of base letters.  This is exactly what repairs (W1).

The theorem below is the formal adapter.  Its depth hypothesis is deliberately
measured in the enlarged relative metric: finite enlargement preserves local
finiteness, but it enlarges relative balls, so depth over the old base would not
be a sound substitute.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- After adjoining `t` and `t⁻¹`, the alternating word `(t h)^n` satisfies
DGO's three conditions (W1)--(W3).  They stay separate in the conclusion,
matching the canonical statement layer in `DGOWWordConditions`. -/
theorem wConditions_blockWord_adjoinPair (D : RelGenSet G Λ) (lam : Λ) {t h : G}
    (htH : t ∉ D.fam lam) {C : ℕ}
    (hh : h ∉ (D.adjoinPair t).relBall lam C) (n : ℕ) :
    WWord.IsWOne (blockWord lam [RelLetter.base t] h n) ∧
      WWord.IsWTwo (D.adjoinPair t) C
        (blockWord lam [RelLetter.base t] h n) ∧
      WWord.IsWThree (D.adjoinPair t)
        (blockWord lam [RelLetter.base t] h n) := by
  exact ⟨isWOne_blockWord_singleBase lam t h n,
    isWTwo_blockWord_singleBase (D.adjoinPair t) lam hh n,
    isWThree_blockWord_singleBase (D.adjoinPair t) lam (by simpa using htH) n⟩

/-- The exact Hull/DGO handoff: Corollary 4.27 transports hyperbolic
embeddedness to the alphabet in which the base element is one letter, while
the same enlarged relative metric supplies (W2). -/
theorem embedded_and_wConditions_blockWord_adjoinPair
    (h427 : DGOCorollary427.{u, w}) (D : RelGenSet G Λ)
    (hemb : D.IsHyperbolicallyEmbedded) (lam : Λ) {t h : G}
    (htH : t ∉ D.fam lam) {C : ℕ}
    (hh : h ∉ (D.adjoinPair t).relBall lam C) (n : ℕ) :
    (D.adjoinPair t).IsHyperbolicallyEmbedded ∧
      WWord.IsWOne (blockWord lam [RelLetter.base t] h n) ∧
      WWord.IsWTwo (D.adjoinPair t) C
        (blockWord lam [RelLetter.base t] h n) ∧
      WWord.IsWThree (D.adjoinPair t)
        (blockWord lam [RelLetter.base t] h n) := by
  exact ⟨RelGenSet.isHyperbolicallyEmbedded_adjoinPair_of_corollary427
      h427 D hemb t,
    wConditions_blockWord_adjoinPair D lam htH hh n⟩

end OsinComponents
end GGT
end GroupApproximation
