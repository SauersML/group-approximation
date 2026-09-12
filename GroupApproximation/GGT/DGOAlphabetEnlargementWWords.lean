import GroupApproximation.GGT.DGOCorollary427Full
import GroupApproximation.GGT.DGOLemma421Consequences

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

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

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
    (D : RelGenSet G Λ) (hemb : D.IsHyperbolicallyEmbedded) (lam : Λ) {t h : G}
    (htH : t ∉ D.fam lam) {C : ℕ}
    (hh : h ∉ (D.adjoinPair t).relBall lam C) (n : ℕ) :
    (D.adjoinPair t).IsHyperbolicallyEmbedded ∧
      WWord.IsWOne (blockWord lam [RelLetter.base t] h n) ∧
      WWord.IsWTwo (D.adjoinPair t) C
        (blockWord lam [RelLetter.base t] h n) ∧
      WWord.IsWThree (D.adjoinPair t)
        (blockWord lam [RelLetter.base t] h n) := by
  exact ⟨(RelGenSet.dgoCorollary427 G Λ D (D.adjoinPair t) rfl
      (RelGenSet.finite_base_symmDiff_adjoinPair D t)).mp hemb,
    wConditions_blockWord_adjoinPair D lam htH hh n⟩

/-- **The completed enlarged-alphabet loxodromy route.**

Corollary 4.27 preserves hyperbolic embeddedness after adjoining `t` and
`t⁻¹`; Lemma 4.21(a), applied where `t` is literally one base letter, then
makes every sufficiently deep `t h` loxodromic.  The depth is necessarily
measured in the enlarged relative metric. -/
theorem exists_threshold_isLoxodromic_mul_adjoinPair
    (h421a : DGOLemma421a.{u, w}) (D : RelGenSet G Λ)
    (hemb : D.IsHyperbolicallyEmbedded)
    (hbase : DGO421BaseSymmetric D)
    (lam : Λ) (t : G) (htH : t ∉ D.fam lam) :
    ∃ C : ℕ, ∀ h ∈ D.fam lam, h ∉ (D.adjoinPair t).relBall lam C →
      IsLoxodromic (t * h) (Cayley.base (D.adjoinPair t).alphabet) := by
  have hemb' : (D.adjoinPair t).IsHyperbolicallyEmbedded :=
    (RelGenSet.dgoCorollary427 G Λ D (D.adjoinPair t) rfl
      (RelGenSet.finite_base_symmDiff_adjoinPair D t)).mp hemb
  have hbase' : DGO421BaseSymmetric (D.adjoinPair t) := by
    intro x hx
    rcases hx with h | h | h
    · exact Or.inl (hbase x h)
    · exact Or.inr (Or.inr (by rw [h]; rfl))
    · exact Or.inr (Or.inl (by rw [h, inv_inv]))
  obtain ⟨C, hC⟩ :=
    exists_threshold_isLoxodromic_mul_of_dgoLemma421a h421a (D.adjoinPair t)
      hemb' hbase'
  refine ⟨C, fun h hh hdeep => ?_⟩
  exact hC lam t (Or.inr (Or.inl rfl)) (by simpa using htH) h
    (by simpa using hh) hdeep

end OsinComponents
end GGT
end GroupApproximation
