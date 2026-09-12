import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrongAssemblyTwoWu
import GroupApproximation.CharClass.LIXStepDGenBundlePReal
import GroupApproximation.CharClass.LIXStepDGenTorusPLix
import GroupApproximation.CharClass.LIXStepDGenExpChar
import GroupApproximation.CharClass.ChernSplittingOfLix
import GroupApproximation.CharClass.ChernSplittingOfLHBridge
import GroupApproximation.CharClass.ChernClassesEvenHomogOf
import GroupApproximation.CharClass.LIXKGenOfStepCAgree
import GroupApproximation.CharClass.LIXChernSliceValueBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem LIX, strengthened: the odd primes over two inputs

At the prime `2` both inputs are theorems (`ProblemLIXStrongAssemblyTwoLocal`,
`ProblemLIXStrongAssemblyTwoWu`).  At an odd prime `p ∣ n`, `LemmaTwoPowersModPData n p` has three
clauses: the bundle data of Step D, the link from the ring class to the top class, and the Step C data.
This file proves all three at the real objects of the rank-`n` tower from two inputs.

* `ops : CharClass.OddPTotal.EvenReducedPowers p`, the reduced powers on the even part of mod-`p`
  cohomology.  They give the torus data (`Gen.realTorusModP_lixStage`) and the Wu relations of the
  splitting principle (`KGen.hasSplittingPN_lixBundleOf_self`).
* `LixStepCDataOf n p`, which says the following at every exponent `p` misses, every stage and every
  corner unitary with the degree-`k` section.  There is a relative class that is locally nonzero at
  every zero and restricts to `π^*` of the top class.

Everything else is spelled from producers on main:
* the base `baseY (lixDD n j)`, the spheres `S¹` and `S^{2n+1}` and the Künneth projections
  `KnLix.prY`, `prS1`, `prSodd`;
* the sphere top classes over `ZMod p`;
* `Gen.expChar_evenPart_baseY`;
* the generator `cpGenOf` over `VIdx ⊕ VIdx` with compact Leray–Hirsch
  `compactLerayHirschDualOf_cpGen` at the bundle and at the slice;
* `LerayHirschDataEvenOf.chern_eq_of_graded`;
* the ring class `KGen.lixChernDegOf`, whose top degree is the top class by `rfl`;
* `Gen.nonempty_realBundleModP_lixChernDegOf_stages` and `KGen.kZeroStepCDataOf_of_localNonzeroOf`.

The top class is forced.  The same generator appears in the bundle data (clause (i)), in the link
(clause (ii)) and in `LixStepCDataOf` (clause (iii)).
-/

namespace GroupApproximation
namespace NinetyNineProblems

open scoped Matrix

noncomputable section

/-- The degree-two generator over `ZMod p` on the projective space of the tautological bundle at stage
`j` of the rank-`n` tower. -/
abbrev lixTopGen (p : ℕ) [Fact p.Prime] (n j : ℕ) :=
  CharClass.ChernSplittingOf.cpGenOf (ZMod p)
    (1 + CharClass.LH.tautCardOf
      (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j) ⊕ CharClass.Gen.VIdx n (LIX.Gen.lixDD n j)))
    (by omega)

/-- **The Step C input at an odd prime.**  At every exponent `k` with `p ∤ k`, every stage `j`, and
every continuous corner unitary `G` carrying the constant section to the degree-`k` section, there is a
relative class `u` of the bundle pair over `ZMod p` that is locally nonzero at every zero and whose
restriction `jE u` is `π^*` of the top class `lixChernDegOf … (lixRank n dd)` at the generator
`lixTopGen p n j`.

This is the hypothesis `hdata` of `KGen.stepCHalf_of_localNonzeroOf` at `K = ZMod p` and at the
section index `k - 1`, since the agreement of the local classes is a theorem.  The owner is lx-sliceK:
`KGen.lixThomClassTermOf` with `thomJmTotalOf_lixThomClassTermOf_last` and `lixHclassOf_of_eq`, through
`KGen.kGenLocalNonzeroOf_of_top_closed`. -/
def LixStepCDataOf (n p : ℕ) [Fact p.Prime] : Prop :=
  ∀ k : ℕ, ¬ p ∣ k → ∀ (j : ℕ) (G : CharClass.Gen.baseM n (LIX.Gen.lixDD n j) →
      Matrix (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j))
        (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j)) ℂ)
    (hGc : Continuous G)
    (hGu : ∀ m, CharClass.IsCornerUnitary (CharClass.Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (CharClass.KGen.aVecK n m) 0
      = Sum.elim (CharClass.KGen.bVecK n (k - 1) m) 0),
    ∃ u : CharClass.relCohomology (ZMod p) (CharClass.KGen.lixTotalPair n hGc hGu)
        (CharClass.KGen.lixPuncturedInTotal n hGc hGu)
        (2 * CharClass.KGen.lixRank n (LIX.Gen.lixDD n j)),
      CharClass.KGen.KGenLocalNonzeroOf (ZMod p) n (k - 1) hGc hGu hGe u ∧
        (CharClass.KGen.lixJEOf (ZMod p) n hGc hGu
            (2 * CharClass.KGen.lixRank n (LIX.Gen.lixDD n j))).hom u
          = (CharClass.KGen.lixPiStarOf (ZMod p) n hGc hGu
              (2 * CharClass.KGen.lixRank n (LIX.Gen.lixDD n j))).hom
            (CharClass.KGen.lixChernDegOf (ZMod p) n (LIX.Gen.lixDD n j) (lixTopGen p n j)
              (CharClass.mappingTorus (CharClass.Gen.Vmat n) G CharClass.circHoriz
                CharClass.circHeight)
              (CharClass.KGen.lixRank n (LIX.Gen.lixDD n j)))

/-- **The mod-`p` input at an odd prime from the reduced powers and the Step C input.** -/
theorem lemmaTwoPowersModPData_of (n p : ℕ) [Fact p.Prime]
    (ops : CharClass.OddPTotal.EvenReducedPowers p) (hC : LixStepCDataOf n p) :
    LemmaTwoPowersModPData n p := by
  refine ⟨fun j => TopCat.of (CharClass.baseY (LIX.Gen.lixDD n j)),
    fun _ => TopCat.of (ThirdParty.HamSandwich.SphereOddDegree.Sphere 1),
    fun _ => TopCat.of (ThirdParty.HamSandwich.SphereOddDegree.Sphere (2 * n + 1)),
    fun j => CharClass.KnLix.prY n (LIX.Gen.lixDD n j),
    fun j => CharClass.KnLix.prS1 n (LIX.Gen.lixDD n j),
    fun j => CharClass.KnLix.prSodd n (LIX.Gen.lixDD n j),
    fun _ => CharClass.sphereTopClassOf (ZMod p) 1 le_rfl,
    fun _ => CharClass.sphereTopClassOf (ZMod p) (2 * n + 1) (by omega),
    fun j => CharClass.Gen.realTorusModP_lixStage ops n j,
    fun j => CharClass.Gen.expChar_evenPart_baseY p (LIX.Gen.lixDD n j),
    fun j W k => CharClass.TotalHOf.of (ZMod p) (CharClass.KGen.lixN n (LIX.Gen.lixDD n j)) (2 * k)
      (CharClass.KGen.lixChernDegOf (ZMod p) n (LIX.Gen.lixDD n j) (lixTopGen p n j) W k),
    fun j W => CharClass.KGen.lixChernDegOf (ZMod p) n (LIX.Gen.lixDD n j) (lixTopGen p n j) W
      (CharClass.KGen.lixRank n (LIX.Gen.lixDD n j)),
    ?_, ?_, ?_⟩
  · -- (i) the bundle data of Step D at the real mapping torus
    exact CharClass.Gen.nonempty_realBundleModP_lixChernDegOf_stages n p
      (fun j => CharClass.Gen.realTorusModP_lixStage ops n j)
      (fun j => lixTopGen p n j)
      (fun j G hGc hGu =>
        CharClass.ChernSplittingOf.compactLerayHirschDualOf_cpGen (ZMod p) _
          (↥CharClass.sphereOne × CharClass.Gen.baseM n (LIX.Gen.lixDD n j))
          (CharClass.KGen.lixBundle n G hGc hGu) (CharClass.KGen.lixRank n (LIX.Gen.lixDD n j))
          (CharClass.KGen.rank_lixBundle n G hGc hGu) (CharClass.KGen.one_le_lixRank n _))
      (fun _ _ _ _ k => CharClass.LerayHirschDataEvenOf.chern_eq_of_graded _ k)
      (fun j => by
        haveI : Nonempty (CharClass.baseY (LIX.Gen.lixDD n j)) :=
          CharClass.Gen.nonempty_baseY (LIX.Gen.lixDD n j)
        exact CharClass.ChernSplittingOf.compactLerayHirschDualOf_cpGen (ZMod p) _
          (CharClass.baseY (LIX.Gen.lixDD n j)) _ _
          (fun y => (CharClass.LH.rank_pushforward _ _ _ y).trans
            (CharClass.Gen.rank_vBundleY n (LIX.Gen.lixDD n j) y))
          (CharClass.KGen.one_le_lixRank n _))
      (CharClass.KGen.negEZero n) 1 (by simp)
      (fun j G hGc hGu =>
        CharClass.KGen.hasSplittingPN_lixBundleOf_self p n (LIX.Gen.lixDD n j) (lixTopGen p n j)
          (CharClass.ChernSplittingOf.compactLerayHirschDualOf_cpGen (ZMod p) _) ops G hGc hGu)
  · -- (ii) the ring class at the top degree is the top class
    intro j G hGc hGu
    rfl
  · -- (iii) the Step C data over `ZMod p`
    intro k hk j G hGc hGu hGe
    obtain ⟨u, hloc, hcl⟩ := hC k hk j G hGc hGu hGe
    exact CharClass.KGen.kZeroStepCDataOf_of_localNonzeroOf (ZMod p) n (k - 1)
      (LIX.Gen.lixDD n j) hGc hGu hGe u hloc hcl

/-- **`LemmaTwoHoldsAtPowers n` from the inputs at the odd primes alone.**  The prime `2` is closed by
`lemmaTwoPowersTwoLocalData_holds` and `lemmaTwoPowersTwoWuData_holds`. -/
theorem lemmaTwoHoldsAtPowers_of_oddPrimeData (n : ℕ) (hn2 : 2 ≤ n)
    (ops : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ∣ n → CharClass.OddPTotal.EvenReducedPowers p)
    (hC : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ∣ n → LixStepCDataOf n p) :
    LemmaTwoHoldsAtPowers n := by
  haveI : NeZero n := ⟨by omega⟩
  refine lemmaTwoHoldsAtPowers_of_twoData_of_modPData n hn2
    (fun _ => ⟨lemmaTwoPowersTwoLocalData_holds n, lemmaTwoPowersTwoWuData_holds n⟩) ?_
  intro p _ hp2 hpn
  exact lemmaTwoPowersModPData_of n p (ops p hp2 hpn) (hC p hp2 hpn)

/-- **The stronger theorem over the inputs at the odd primes.** -/
theorem exists_isSimpleRing_separable_hasK1InjPowerWitness_of_oddPrimeData (n : ℕ) (hn2 : 2 ≤ n)
    (ops : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ∣ n → CharClass.OddPTotal.EvenReducedPowers p)
    (hC : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ∣ n → LixStepCDataOf n p) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
        HasK1InjPowerWitness A n :=
  exists_isSimpleRing_separable_hasK1InjPowerWitness_of_lemmaTwoHoldsAtPowers n hn2
    (lemmaTwoHoldsAtPowers_of_oddPrimeData n hn2 ops hC)

/-- A prime dividing `6` other than `2` is `3`. -/
theorem eq_three_of_prime_dvd_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp6 : p ∣ 6) : p = 3 := by
  rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 3 from hp6) with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h

/-- **`LemmaTwoHoldsAtPowers 6` over the inputs at the prime `3`.**  This is the rank of the headline
instance: its order is divisible by `6`. -/
theorem lemmaTwoHoldsAtPowers_six_of (ops : CharClass.OddPTotal.EvenReducedPowers 3)
    (hC : LixStepCDataOf 6 3) : LemmaTwoHoldsAtPowers 6 := by
  refine lemmaTwoHoldsAtPowers_of_oddPrimeData 6 (by norm_num) ?_ ?_
  · intro p _ hp2 hp6
    obtain rfl := eq_three_of_prime_dvd_six (Fact.out : p.Prime) hp2 hp6
    exact ops
  · intro p _ hp2 hp6
    obtain rfl := eq_three_of_prime_dvd_six (Fact.out : p.Prime) hp2 hp6
    exact hC

end

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms LixStepCDataOf
#audit_axioms lemmaTwoPowersModPData_of
#audit_axioms lemmaTwoHoldsAtPowers_of_oddPrimeData
#audit_axioms exists_isSimpleRing_separable_hasK1InjPowerWitness_of_oddPrimeData
#audit_axioms eq_three_of_prime_dvd_six
#audit_axioms lemmaTwoHoldsAtPowers_six_of
