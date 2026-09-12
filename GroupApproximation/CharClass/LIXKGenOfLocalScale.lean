import GroupApproximation.CharClass.LIXKGenLocalSplitOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The local computation over a field is invariant under nonzero scalars

Lane `lx-stepcK-local` (LIX strongest swarm, 2026-09-12).

`KGen.KGenLocalNonzeroOf K n k … u` only asks that a linear image of `u` be nonzero near each zero,
so it passes from `u` to every nonzero multiple of `u`.  The consumers need this because over `K`
the Leray–Hirsch coordinate `LerayHirschGraded.gamma k` is the **negative** of the ring Chern class
for `1 ≤ k ≤ r` (`CharClass/ChernGammaBridgeOf.lean`), so the class whose restriction to the base is
`π^* γ_r` can be the negative, or a unit multiple, of the class with unit top coordinate.

## Main declarations

* `KGen.kGenLocalNonzeroOf_smul` — nonzero multiples.
* `KGen.kGenLocalNonzeroOf_neg` — the negative.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-- **The local computation passes to nonzero multiples.** -/
theorem kGenLocalNonzeroOf_smul (K : Type) [Field K] (n k : ℕ) {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    {u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd)}
    (h : KGenLocalNonzeroOf K n k hGc hGu hGe u) {c : K} (hc : c ≠ 0) :
    KGenLocalNonzeroOf K n k hGc hGu hGe (c • u) := by
  intro i
  obtain ⟨B, hB, hne⟩ := h i
  refine ⟨B, hB, ?_⟩
  rw [map_smul, map_smul]
  exact smul_ne_zero hc hne

/-- **The local computation passes to the negative.** -/
theorem kGenLocalNonzeroOf_neg (K : Type) [Field K] (n k : ℕ) {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    {u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd)}
    (h : KGenLocalNonzeroOf K n k hGc hGu hGe u) :
    KGenLocalNonzeroOf K n k hGc hGu hGe (-u) := by
  intro i
  obtain ⟨B, hB, hne⟩ := h i
  refine ⟨B, hB, ?_⟩
  rw [map_neg, map_neg]
  exact neg_ne_zero.mpr hne

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.kGenLocalNonzeroOf_smul
#audit_axioms KGen.kGenLocalNonzeroOf_neg

end GroupApproximation.CharClass
