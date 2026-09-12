import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrongAssemblyHalves
import GroupApproximation.CharClass.LIXLemmaTwoGenTwo
import GroupApproximation.CharClass.ParityEvenTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem LIX, strengthened: the prime `2`

`ProblemLIXStrongAssemblyCor4.lean` reduces the stronger theorem to `LemmaTwoHoldsAtPowers n`, a
statement quantified over the primes dividing `n`.  At the prime `2` the rank-`n` composition of
Lemma 2 is `CharClass.Gen.lemmaTwoFor_powers_two_lixChernOf` (`CharClass/LIXLemmaTwoGenTwo.lean`):
one top Chern class mod `2` on both halves, the Step C half from the local data at the zeros of
the degree-`k` section and the Step D half from the mod-`2` Wu data, with the Cartan input already
the theorem `CharClass.Wu.cartanTotal`.

This file names the two inputs that composition still takes and assembles the prime-`2` part of
`LemmaTwoHoldsAtPowers`.

* `LemmaTwoPowersTwoLocalData n` — the binder `hloc`: `KGen.KZeroLocalData` at every odd exponent,
  every stage and every corner unitary carrying the constant section to the degree-`k` section.
  Producer: lane `lx-local2b` (the local square at the `k` zeros).
* `LemmaTwoPowersTwoWuData n` — the spaces `Y`, `S¹`, `S^{2n+1}` of every stage with their
  projections from the mapping-torus base, their sphere classes, and the mod-`2` Step D data
  `Gen.WuStepDData` of the top Chern class of every mapping torus.  Producers: lanes `lx-kunneth`
  (the projections and the Künneth split) and `lx-slice2` (`sq_b`, `split`, `slice`).
* `lemmaTwoHoldsForSections_powersSections_two` — Lemma 2 at `powersSections n k` for every odd
  exponent, at every even rank `n ≥ 2`, from the two inputs.
* `lemmaTwoHoldsAtPowers_two_pow` — at the ranks `n = 2 ^ m` the prime `2` is the only prime
  dividing `n`, so the two inputs give `LemmaTwoHoldsAtPowers (2 ^ m)` outright.

The Wu data is quantified existentially over the spaces and maps and carries each structure as
`Nonempty`: `Gen.WuStepDData` is data, and a `Prop` can only assert that some instance exists.
-/

namespace GroupApproximation
namespace NinetyNineProblems

open scoped Matrix
open CategoryTheory

noncomputable section

/-! ## The two inputs at the prime `2` -/

/-- **The local data of Step C at the prime `2`**, the binder `hloc` of
`CharClass.Gen.lemmaTwoFor_powers_two_lixChernOf`: at every odd exponent `e`, every stage `j` and
every continuous corner unitary `G` of `V` carrying the constant section `(e₀, 0)` to the degree-`e`
section `(KGen.bVecK n (e - 1), 0)`, the Thom class pulled back along the section splits into
nonzero local classes at the `e` zeros (`CharClass.KGen.KZeroLocalData`).

Producer: lane `lx-local2b`. -/
def LemmaTwoPowersTwoLocalData (n : ℕ) : Prop :=
  ∀ (e : ℕ), Odd e → ∀ (j : ℕ)
    (G : CharClass.Gen.baseM n (LIX.Gen.lixDD n j) →
      Matrix (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j))
        (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j)) ℂ)
    (hGc : Continuous G)
    (hGu : ∀ m, CharClass.IsCornerUnitary (CharClass.Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (CharClass.KGen.aVecK n m) 0
      = Sum.elim (CharClass.KGen.bVecK n (e - 1) m) 0),
    CharClass.KGen.KZeroLocalData n (e - 1) (LIX.Gen.lixDD n j) hGc hGu hGe

/-- **The mod-`2` Step D data at every stage**: spaces `Y j`, `S₁ j`, `Sodd j` with maps from the
mapping-torus base `KGen.lixN n (lixDD n j)`, the two sphere factors carrying sphere cohomology in
degrees `1` and `2n + 1` with chosen classes, and, for every continuous corner unitary `G`, an
instance of `CharClass.Gen.WuStepDData` for the top Chern class
`KGen.lixChernOf n (KGen.lixChern n (lixDD n j))` of the mapping torus of `G`.

The intended witnesses are `Y j = baseY (lixDD n j)`, `S₁ j = S¹`, `Sodd j = S^{2n+1}` with the
Künneth projections.  Producers: lanes `lx-kunneth` and `lx-slice2`. -/
def LemmaTwoPowersTwoWuData (n : ℕ) : Prop :=
  ∃ (Y S₁ Sodd : ℕ → TopCat.{0})
    (pY : ∀ j, CharClass.KGen.lixN n (LIX.Gen.lixDD n j) ⟶ Y j)
    (q₁ : ∀ j, CharClass.KGen.lixN n (LIX.Gen.lixDD n j) ⟶ S₁ j)
    (qodd : ∀ j, CharClass.KGen.lixN n (LIX.Gen.lixDD n j) ⟶ Sodd j)
    (_ : ∀ j, CharClass.HasSphereCohomology (S₁ j) 1)
    (_ : ∀ j, CharClass.HasSphereCohomology (Sodd j) (2 * n + 1))
    (σ₁ : ∀ j, CharClass.Hmod2 (S₁ j) 1) (σodd : ∀ j, CharClass.Hmod2 (Sodd j) (2 * n + 1)),
    ∀ (j : ℕ) (G : CharClass.Gen.baseM n (LIX.Gen.lixDD n j) →
        Matrix (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j))
          (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ m, CharClass.IsCornerUnitary (CharClass.Gen.Vmat n m) (G m)) →
      Nonempty (CharClass.Gen.WuStepDData n (LIX.Gen.lixDD n j) (pY j) (q₁ j) (qodd j) (σ₁ j)
        (σodd j)
        (CharClass.KGen.lixChernOf n (CharClass.KGen.lixChern n (LIX.Gen.lixDD n j))
          (CharClass.mappingTorus (CharClass.Gen.Vmat n) G CharClass.circHoriz
            CharClass.circHeight)))

/-! ## Assembly -/

/-- A prime dividing a power of `2` is `2`. -/
theorem eq_two_of_prime_dvd_two_pow {p m : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ m) : p = 2 :=
  (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)

/-- **Lemma 2 at the agreed family for every odd exponent**, at every even rank `n ≥ 2`, from the
local data and the mod-`2` Wu data. -/
theorem lemmaTwoHoldsForSections_powersSections_two (n : ℕ) (hn2 : 2 ≤ n) (hn : 2 ∣ n)
    (hloc : LemmaTwoPowersTwoLocalData n) (hwu : LemmaTwoPowersTwoWuData n) :
    ∀ k : ℕ, ¬ 2 ∣ k → LemmaTwoHoldsForSections n (powersSections n k) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨Y, S₁, Sodd, pY, q₁, qodd, hS₁, hSodd, σ₁, σodd, hdata⟩ := hwu
  exact (lemmaTwoHoldsForSections_powersSections_iff_forall n 2).mpr
    (CharClass.Gen.lemmaTwoFor_powers_two_lixChernOf n (even_iff_two_dvd.mpr hn) hn2 pY q₁ qodd
      CharClass.Wu.cartanTotal hS₁ hSodd σ₁ σodd
      (fun j G hc hu => Classical.choice (hdata j G hc hu)) hloc)

/-- **`LemmaTwoHoldsAtPowers` at the ranks `2 ^ m`**: the only prime dividing `2 ^ m` is `2`,
so the two inputs at the prime `2` are all it needs. -/
theorem lemmaTwoHoldsAtPowers_two_pow (m : ℕ) (hm : 1 ≤ m)
    (hloc : LemmaTwoPowersTwoLocalData (2 ^ m)) (hwu : LemmaTwoPowersTwoWuData (2 ^ m)) :
    LemmaTwoHoldsAtPowers (2 ^ m) := by
  intro p hp hpn k hk
  obtain rfl := eq_two_of_prime_dvd_two_pow hp hpn
  have h2le : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact lemmaTwoHoldsForSections_powersSections_two (2 ^ m) h2le hpn hloc hwu k hk

end

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms LemmaTwoPowersTwoLocalData
#audit_axioms LemmaTwoPowersTwoWuData
#audit_axioms eq_two_of_prime_dvd_two_pow
#audit_axioms lemmaTwoHoldsForSections_powersSections_two
#audit_axioms lemmaTwoHoldsAtPowers_two_pow
