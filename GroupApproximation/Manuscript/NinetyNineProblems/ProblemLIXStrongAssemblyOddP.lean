import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrongAssemblyTwo
import GroupApproximation.CharClass.LIXStepDGenReal
import GroupApproximation.CharClass.LIXKGenOfStepC
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem LIX, strengthened: the odd primes, and the assembly over every prime

`LemmaTwoHoldsAtPowers n` quantifies over the primes dividing `n`.  `ProblemLIXStrongAssemblyTwo`
handles the prime `2`.  At an odd prime `p` the rank-`n` composition of Lemma 2 is
`CharClass.Gen.lemmaTwoFor_powers_of_stepC_realModP` (`CharClass/LIXStepDGenReal.lean`): the Step D
half from the real mod-`p` data of the mapping torus (`Gen.RealTorusModP`, `Gen.RealBundleModP`) and
a Step C half at the top Chern class in `TotalHOf K N`.  The Step C half over a field is
`CharClass.KGen.stepCHalf_of_kZeroStepCDataOf` (`CharClass/LIXKGenOfStepC.lean`), stated in
`Hmod K (lixN n dd) (2 · lixRank n dd)`.

The two meet at one class read in two places, and this file joins them.

* `stepCHalf_of_eq_zero_imp` — a Step C half transports along any map of classes that reflects
  zero.
* `natCast_sub_one_add_one_ne_zero` — the count's unit: for `p ∤ k`, `((k - 1) + 1 : ZMod p) ≠ 0`
  (every prime divides `0`, so `k ≠ 0` and `(k - 1) + 1 = k`).
* `LemmaTwoPowersModPData n p` — the named input at the prime `p`, over `K = ZMod p`: the torus data
  of every stage, the bundle data of every mapping torus, the top-class link `htop` between the ring
  class and the class of degree `2 · lixRank`, and the open Step C data at every exponent `p` misses.
* `lemmaTwoHoldsForSections_powersSections_of_modPData` — Lemma 2 at `powersSections n k` for every
  exponent `p` misses, from that input.
* `lemmaTwoHoldsAtPowers_of_twoData_of_modPData` — **`LemmaTwoHoldsAtPowers n` from the prime-`2`
  inputs (when `2 ∣ n`) and the mod-`p` input at every odd prime dividing `n`.**
* `lemmaTwoHoldsAtPowers_of_modPData` — the same at an odd rank, where only odd primes occur.

`[Fact p.Prime]` is a binder of the named input because `KZeroStepCDataOf` is a statement over a
field; the prime quantifier of `LemmaTwoHoldsAtPowers` supplies it.
-/

namespace GroupApproximation
namespace NinetyNineProblems

open scoped Matrix
open CategoryTheory

noncomputable section

/-! ## The seam -/

/-- **A Step C half transports along a map of classes that reflects zero.**  If `g W = 0` whenever
`f W = 0` and the class `g` does not vanish on the mapping tori Step C concerns, neither does `f`. -/
theorem stepCHalf_of_eq_zero_imp {n ℓ : ℕ} {dd : Fin ℓ → ℕ}
    {b : CharClass.Gen.baseM n dd → Fin (n + 1) → ℂ} {K₁ K₂ : Type*} [Zero K₁] [Zero K₂]
    {f : (↥CharClass.sphereOne × CharClass.Gen.baseM n dd →
      Matrix (CharClass.Gen.VIdx n dd ⊕ CharClass.Gen.VIdx n dd)
        (CharClass.Gen.VIdx n dd ⊕ CharClass.Gen.VIdx n dd) ℂ) → K₁}
    {g : (↥CharClass.sphereOne × CharClass.Gen.baseM n dd →
      Matrix (CharClass.Gen.VIdx n dd ⊕ CharClass.Gen.VIdx n dd)
        (CharClass.Gen.VIdx n dd ⊕ CharClass.Gen.VIdx n dd) ℂ) → K₂}
    (hfg : ∀ W, f W = 0 → g W = 0) (h : CharClass.Gen.StepCHalf n dd b g) :
    CharClass.Gen.StepCHalf n dd b f :=
  fun G hGc hGu hGe hf => h G hGc hGu hGe (hfg _ hf)

/-- **The count's unit.**  For an exponent `k` the prime `p` does not divide, `k ≠ 0`, so
`(k - 1) + 1 = k`, and `k` is nonzero in `ZMod p`. -/
theorem natCast_sub_one_add_one_ne_zero {p k : ℕ} (hk : ¬ p ∣ k) :
    (((k - 1 + 1 : ℕ)) : ZMod p) ≠ 0 := by
  have hk0 : k ≠ 0 := fun h => hk (h ▸ dvd_zero p)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0), Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  exact hk

/-! ## The named input at an odd prime -/

/-- **The mod-`p` input of Lemma 2 at the powers, over `K = ZMod p`.**  There are:

* spaces `Y j`, `S₁ j`, `Sodd j` with maps from the mapping-torus base `KGen.lixN n (lixDD n j)` and
  sphere classes `σ₁ j`, `σodd j` in degrees `1` and `2n + 1`;
* the torus data `Gen.RealTorusModP` of every stage (the reduced powers on the torus and on `Y`), and
  exponent characteristic `p` on the even part of `H^*(Y j; F_p)`;
* ring-valued Chern classes `γfun j W : ℕ → TotalHOf (ZMod p) (lixN n (lixDD n j))` carrying the
  bundle data `Gen.RealBundleModP` on the mapping torus of every corner unitary;
* the top class `topClass j W` in `H^{2 · lixRank}` with `γfun j W (lixRank) = of (topClass j W)`;
* the open Step C data `KGen.KZeroStepCDataOf` at every exponent `k` with `p ∤ k`, for the
  degree-`k` section, at `gamma := topClass j (mapping torus of G)`.

The intended witnesses are the Künneth projections of `S¹ × S^{2n+1} × baseY`, the reduced powers
`P^i`, and the Chern classes of the mapping-torus bundle over `F_p`.  Producers: lanes `lx-torusP`
(`T`), `lx-bundleP` (the bundle data and `ExpChar`), `lx-kunneth` (the projections), `lx-stepcK-local`
and `lx-stepcK-agree` (the Step C data), `lx-lhK-b` (the top class). -/
def LemmaTwoPowersModPData (n p : ℕ) [Fact p.Prime] : Prop :=
  ∃ (Y S₁ Sodd : ℕ → TopCat.{0})
    (pY : ∀ j, CharClass.KGen.lixN n (LIX.Gen.lixDD n j) ⟶ Y j)
    (q₁ : ∀ j, CharClass.KGen.lixN n (LIX.Gen.lixDD n j) ⟶ S₁ j)
    (qodd : ∀ j, CharClass.KGen.lixN n (LIX.Gen.lixDD n j) ⟶ Sodd j)
    (σ₁ : ∀ j, CharClass.TotalPieceOf (ZMod p) (S₁ j) 1)
    (σodd : ∀ j, CharClass.TotalPieceOf (ZMod p) (Sodd j) (2 * n + 1))
    (T : ∀ j, CharClass.Gen.RealTorusModP n (ZMod p) (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j))
    (_ : ∀ j, ExpChar (CharClass.Gen.evenPart (ZMod p) (Y j)) p)
    (γfun : ∀ j : ℕ, (↥CharClass.sphereOne × CharClass.Gen.baseM n (LIX.Gen.lixDD n j) →
        Matrix (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j) ⊕ CharClass.Gen.VIdx n (LIX.Gen.lixDD n j))
          (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j) ⊕ CharClass.Gen.VIdx n (LIX.Gen.lixDD n j)) ℂ) →
        ℕ → CharClass.TotalHOf (ZMod p) (CharClass.KGen.lixN n (LIX.Gen.lixDD n j)))
    (topClass : ∀ j : ℕ, (↥CharClass.sphereOne × CharClass.Gen.baseM n (LIX.Gen.lixDD n j) →
        Matrix (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j) ⊕ CharClass.Gen.VIdx n (LIX.Gen.lixDD n j))
          (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j) ⊕ CharClass.Gen.VIdx n (LIX.Gen.lixDD n j)) ℂ) →
        CharClass.Hmod (ZMod p) (CharClass.KGen.lixN n (LIX.Gen.lixDD n j))
          (2 * CharClass.KGen.lixRank n (LIX.Gen.lixDD n j))),
    (∀ (j : ℕ) (G : CharClass.Gen.baseM n (LIX.Gen.lixDD n j) →
        Matrix (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j))
          (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ m, CharClass.IsCornerUnitary (CharClass.Gen.Vmat n m) (G m)) →
      Nonempty (CharClass.Gen.RealBundleModP p (LIX.Gen.lixDD n j) (T j)
        (γfun j (CharClass.mappingTorus (CharClass.Gen.Vmat n) G CharClass.circHoriz
          CharClass.circHeight)))) ∧
    (∀ (j : ℕ) W, γfun j W ((∑ i, LIX.Gen.lixDD n j i) + (n + 1))
      = CharClass.TotalHOf.of (ZMod p) (CharClass.KGen.lixN n (LIX.Gen.lixDD n j))
          (2 * CharClass.KGen.lixRank n (LIX.Gen.lixDD n j)) (topClass j W)) ∧
    (∀ k : ℕ, ¬ p ∣ k → ∀ (j : ℕ) (G : CharClass.Gen.baseM n (LIX.Gen.lixDD n j) →
        Matrix (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j))
          (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j)) ℂ)
      (hGc : Continuous G)
      (hGu : ∀ m, CharClass.IsCornerUnitary (CharClass.Gen.Vmat n m) (G m))
      (hGe : ∀ m, G m *ᵥ Sum.elim (CharClass.KGen.aVecK n m) 0
        = Sum.elim (CharClass.KGen.bVecK n (k - 1) m) 0),
      CharClass.KGen.KZeroStepCDataOf (ZMod p) n (k - 1) (LIX.Gen.lixDD n j) hGc hGu hGe
        (topClass j (CharClass.mappingTorus (CharClass.Gen.Vmat n) G CharClass.circHoriz
          CharClass.circHeight)))

/-! ## Assembly -/

/-- **Lemma 2 at the agreed family at a prime `p ∣ n`**, for every exponent `p` misses, from the
mod-`p` input.  Step D is `Gen.lemmaTwoFor_powers_of_stepC_realModP`'s; Step C is
`KGen.stepCHalf_of_kZeroStepCDataOf` at `K = ZMod p`, moved to the ring class along the top-class
link, which reflects zero because `TotalHOf.of` is injective. -/
theorem lemmaTwoHoldsForSections_powersSections_of_modPData (n p : ℕ) [Fact p.Prime]
    (hn : 1 ≤ n) (hpn : p ∣ n) (h : LemmaTwoPowersModPData n p) :
    ∀ k : ℕ, ¬ p ∣ k → LemmaTwoHoldsForSections n (powersSections n k) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨Y, S₁, Sodd, pY, q₁, qodd, σ₁, σodd, T, hexp, γfun, topClass, hdata, htop, hC⟩ := h
  haveI : ∀ j, ExpChar (CharClass.Gen.evenPart (ZMod p) (Y j)) p := hexp
  refine (lemmaTwoHoldsForSections_powersSections_iff_forall n p).mpr ?_
  refine CharClass.Gen.lemmaTwoFor_powers_of_stepC_realModP n p Fact.out hn hpn T γfun
    (fun j G hc hu => Classical.choice (hdata j G hc hu)) ?_
  intro k hk j
  refine stepCHalf_of_eq_zero_imp (g := topClass j) (fun W hW => ?_)
    (CharClass.KGen.stepCHalf_of_kZeroStepCDataOf (ZMod p) n (k - 1)
      (natCast_sub_one_add_one_ne_zero hk) (LIX.Gen.lixDD n j) (LIX.Gen.lixDD_pos n j)
      (topClass j) (hC k hk j))
  rw [htop j W] at hW
  exact (CharClass.TotalHOf.of_eq_zero_iff (ZMod p) _ _ _).mp hW

/-- **`LemmaTwoHoldsAtPowers n` from the inputs at every prime dividing `n`**: the prime-`2` inputs
when `2 ∣ n`, and the mod-`p` input at every odd prime `p ∣ n`. -/
theorem lemmaTwoHoldsAtPowers_of_twoData_of_modPData (n : ℕ) (hn2 : 2 ≤ n)
    (htwo : 2 ∣ n → LemmaTwoPowersTwoLocalData n ∧ LemmaTwoPowersTwoWuData n)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ∣ n → LemmaTwoPowersModPData n p) :
    LemmaTwoHoldsAtPowers n := by
  intro p hp hpn k hk
  by_cases h2 : p = 2
  · subst h2
    obtain ⟨hl, hw⟩ := htwo hpn
    exact lemmaTwoHoldsForSections_powersSections_two n hn2 hpn hl hw k hk
  · haveI : Fact p.Prime := ⟨hp⟩
    exact lemmaTwoHoldsForSections_powersSections_of_modPData n p (by omega) hpn
      (hodd p h2 hpn) k hk

/-- **At an odd rank only odd primes occur**, so the mod-`p` inputs alone give
`LemmaTwoHoldsAtPowers n`. -/
theorem lemmaTwoHoldsAtPowers_of_modPData (n : ℕ) (hn : 1 ≤ n) (hn2 : ¬ 2 ∣ n)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ∣ n → LemmaTwoPowersModPData n p) :
    LemmaTwoHoldsAtPowers n := by
  intro p hp hpn k hk
  have h2 : p ≠ 2 := fun h => hn2 (h ▸ hpn)
  haveI : Fact p.Prime := ⟨hp⟩
  exact lemmaTwoHoldsForSections_powersSections_of_modPData n p hn hpn (hodd p h2 hpn) k hk

end

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms stepCHalf_of_eq_zero_imp
#audit_axioms natCast_sub_one_add_one_ne_zero
#audit_axioms LemmaTwoPowersModPData
#audit_axioms lemmaTwoHoldsForSections_powersSections_of_modPData
#audit_axioms lemmaTwoHoldsAtPowers_of_twoData_of_modPData
#audit_axioms lemmaTwoHoldsAtPowers_of_modPData
