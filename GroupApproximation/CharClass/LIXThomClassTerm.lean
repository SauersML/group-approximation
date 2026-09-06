import GroupApproximation.CharClass.LIXThomClassOfTaut
import GroupApproximation.CharClass.ChernTautRestrict

/-!
# The Thom class as a term, unconditionally

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`LIXThomClassOfTaut` produced the Thom class under an existential and over the
input `htaut`.  Both are now removed.

`cc-projective`'s `LH.pull_sInclusion_tautEulerOf` discharges `htaut`, so nothing
about the class is hypothetical any more.  And `cc-lix-odd` needs a **term**, not
an existential: in `lix_topClass_ne_zero_of_named` the class appears in two
hypotheses at once, so a witness obtained under `obtain` closes the first and
makes the second unstatable.  Everything below is therefore a `def` with its
properties beside it.

## What is pinned, and the cost of pinning it

Publishing the class as a definition freezes it under rule 11.  That is the right
trade here, as `cc-lix-odd` argued: a term nobody can name is worse than a term
that might later be superseded, and superseding a definition under a new name is
cheaper than discovering a hypothesis cannot be discharged.

## Main declarations

* `range_comp_linearEquiv`, `injective_thomJm` — the two pieces the existential
  hid.
* `ThomChernDeg.thomJmTotal` — the coordinate map on the vector-bundle pair, as a term.
* `lixThomClassTerm`, `lixThomClassTerm_ne_zero` — **`u` and `hu`, unconditional
  and named.**
-/

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace ThomChernDeg

open LH

set_option linter.unusedSectionVars false

/-! ## 1. The two pieces the existential hid -/

/-- Precomposing with an equivalence does not change a range. -/
theorem range_comp_linearEquiv {A A' N : Type} [AddCommGroup A] [Module (ZMod 2) A]
    [AddCommGroup A'] [Module (ZMod 2) A'] [AddCommGroup N] [Module (ZMod 2) N]
    (φ : A ≃ₗ[ZMod 2] A') (f : A' →ₗ[ZMod 2] N) :
    LinearMap.range (f.comp φ.toLinearMap) = LinearMap.range f := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨φ a, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨φ.symm b, congrArg f (φ.apply_symm_apply b)⟩

/-- The coordinate map out of the relative group is injective as soon as
`relToAbs` is, because reading coefficients is an equivalence. -/
theorem injective_thomJm {X P : TopCat.{0}} {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ (r + 1)) (Z : Set P)
    (hinj0 : Function.Injective (relToAbs (ZMod 2) P Z (2 * r)).hom) :
    Function.Injective (thomJm L Z) :=
  fun _ _ hab => hinj0 ((lhTopEquiv L).symm.injective hab)

/-! ## 2. Leray–Hirsch on the hyperplane, at `cc-projective`'s class -/

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `hyperLH` at the class `cc-projective` publishes.  The two spellings of the
transported class agree definitionally, so this is the same theorem. -/
theorem hyperLH_range [CompactSpace X] [T2Space X] [Nonempty X] (p : Bundle X ι)
    (r : ℕ) (hs : ∀ x, p.rank x = r) (hs1 : 1 ≤ r) :
    LerayHirschGraded (hyperProj p) (tautEulerRange p) r :=
  lerayHirschGraded_of_iso (hyperIso p) (projMapOf p) (hyperProj p)
    (hyperIso_hom_comp p) (tautEulerOf p) (tautEulerRange p) rfl
    (lerayHirschGraded_compact p r hs hs1)

/-! ## 3. The coordinate map on the vector-bundle pair, as a term -/

/-- **The coordinate map on the vector-bundle pair.**  The projectivisation's
coordinate map, precomposed with the Thom bridge. -/
def thomJmTotal [CompactSpace X] [T2Space X] (p : Bundle X ι) {r : ℕ}
    (L : LerayHirschGraded (projMapOf p.plusOne) (tautEulerOf p.plusOne) (r + 1)) :
    ↥(relCohomology (ZMod 2) (TopCat.of (Bundle.Total p))
        ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p)
        (2 * r))
      →ₗ[ZMod 2] ((i : Fin (r + 1)) → Hmod2 (TopCat.of X) (2 * r - 2 * (i : ℕ))) :=
  (thomJm L (Set.range (Bundle.projIncl p))).comp (bridgeTotal p (2 * r)).toLinearMap

/-- Unfolding the composite at a point, so that later steps never leave the
composition to unification.  Both `isDefEq` timeouts in the first probe of this
file were that. -/
theorem thomJmTotal_apply [CompactSpace X] [T2Space X] (p : Bundle X ι) {r : ℕ}
    (L : LerayHirschGraded (projMapOf p.plusOne) (tautEulerOf p.plusOne) (r + 1))
    (a : ↥(relCohomology (ZMod 2) (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p)
      (2 * r))) :
    thomJmTotal p L a
      = thomJm L (Set.range (Bundle.projIncl p)) (bridgeTotal p (2 * r) a) := rfl

/-- It is injective. -/
theorem injective_thomJmTotal [CompactSpace X] [T2Space X] [Nonempty X]
    (p : Bundle X ι) {r : ℕ} (hr : 1 ≤ r) (hs : ∀ x, p.rank x = r)
    (L : LerayHirschGraded (projMapOf p.plusOne) (tautEulerOf p.plusOne) (r + 1)) :
    Function.Injective (thomJmTotal p L) := by
  have hinj0 : Function.Injective
      (relToAbs (ZMod 2) (TopCat.of (Bundle.Proj p.plusOne))
        (Set.range (Bundle.projIncl p)) (2 * r)).hom :=
    relToAbs_injective_of_graded (X := TopCat.of X)
      (P := TopCat.of (Bundle.Proj p.plusOne)) (r := r)
      (Set.range (Bundle.projIncl p))
      (projMapOf p.plusOne) (hyperProj p) rfl (tautEulerOf p.plusOne)
      (tautEulerRange p) (pull_sInclusion_tautEulerOf p) hr L
      (hyperLH_range p r hs hr)
  have hj : Function.Injective (thomJm L (Set.range (Bundle.projIncl p))) :=
    injective_thomJm L (Set.range (Bundle.projIncl p)) hinj0
  intro a b hab
  rw [thomJmTotal_apply, thomJmTotal_apply] at hab
  exact (bridgeTotal p (2 * r)).injective (hj hab)

/-- Its range is the Thom kernel. -/
theorem range_thomJmTotal [CompactSpace X] [T2Space X] [Nonempty X]
    (p : Bundle X ι) {r : ℕ} (hs : ∀ x, p.rank x = r) (hs1 : 1 ≤ r)
    (L : LerayHirschGraded (projMapOf p.plusOne) (tautEulerOf p.plusOne) (r + 1)) :
    LinearMap.range (thomJmTotal p L)
      = LinearMap.ker (ThomDeg.restrictMap (R := ZMod 2)
        (M := fun i : Fin (r + 1) => Hmod2 (TopCat.of X) (2 * r - 2 * (i : ℕ)))
        (fun i => chernMul (hyperLH_range p r hs hs1) i)) := by
  have h1 : LinearMap.range (thomJmTotal p L)
      = LinearMap.range (thomJm L (Set.range (Bundle.projIncl p))) :=
    range_comp_linearEquiv (bridgeTotal p (2 * r))
      (thomJm L (Set.range (Bundle.projIncl p)))
  rw [h1]
  exact range_thomJm_eq_ker_restrictMap (X := TopCat.of X)
    (P := TopCat.of (Bundle.Proj p.plusOne)) (r := r)
    (Set.range (Bundle.projIncl p))
    (projMapOf p.plusOne) (hyperProj p) rfl (tautEulerOf p.plusOne)
    (tautEulerRange p) (pull_sInclusion_tautEulerOf p) L
    (hyperLH_range p r hs hs1)

end ThomChernDeg

/-! ## 4. At the mapping-torus bundle -/

open ThomChernDeg LH

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

set_option linter.unusedSectionVars false

/-- `1 ≤ lixRank dd`, as a term rather than a tactic block.  A `by` block here is
postponed, and a postponed argument leaves a metavariable that blocks the
unification of the two `chernMul` spellings downstream. -/
theorem one_le_lixRank_dd (dd : Fin ℓ → ℕ) : 1 ≤ lixRank dd := by simp [lixRank]

/-- Leray–Hirsch upstairs, at the projectivised sum. -/
theorem lixLHplus (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    LerayHirschGraded (projMapOf (lixBundle G hGc hGu).plusOne)
      (tautEulerOf (lixBundle G hGc hGu).plusOne) (lixRank dd + 1) :=
  lerayHirschGraded_compact (lixBundle G hGc hGu).plusOne (lixRank dd + 1)
    (rank_lixBundle_plusOne G hGc hGu) (Nat.succ_le_succ (Nat.zero_le _))

/-- Leray–Hirsch downstairs, on the hyperplane. -/
theorem lixLHhyper (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    LerayHirschGraded (hyperProj (lixBundle G hGc hGu))
      (tautEulerRange (lixBundle G hGc hGu)) (lixRank dd) :=
  hyperLH_range (lixBundle G hGc hGu) (lixRank dd) (rank_lixBundle G hGc hGu)
    (one_le_lixRank_dd dd)

/-- **The Thom class of the mapping-torus bundle pair, as a term.**  This is the
`u` of `lix_topClass_ne_zero_of_named`, unconditional and nameable, so that
`hclass` can be stated about the same class `hu` is about.

Every argument is spelled exactly as the theorem that discharges it spells it.
That is not style: restating any of them forces a delta on both sides of a
unification and the file then dies at `whnf`, which is how the first three probes
of this file failed. -/
def lixThomClassTerm (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ↥(relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu)
      (2 * lixRank dd)) :=
  lixThomClass (M := fun i : Fin (lixRank dd + 1) =>
      Hmod2 (TopCat.of (↥sphereOne × baseM dd)) (2 * lixRank dd - 2 * (i : ℕ)))
    hGc hGu (2 * lixRank dd) (lixRank dd)
    (fun i => chernMul (hyperLH_range (lixBundle G hGc hGu) (lixRank dd)
      (rank_lixBundle G hGc hGu) (one_le_lixRank_dd dd)) i)
    (thomJmTotal (lixBundle G hGc hGu) (lixLHplus hGc hGu))
    (injective_thomJmTotal (lixBundle G hGc hGu) (one_le_lixRank_dd dd)
      (rank_lixBundle G hGc hGu) (lixLHplus hGc hGu))
    (range_thomJmTotal (lixBundle G hGc hGu) (rank_lixBundle G hGc hGu)
      (one_le_lixRank_dd dd) (lixLHplus hGc hGu))
    (lixTopCoeff dd)

/-- **It is nonzero.**  This is the `hu` of `lix_topClass_ne_zero_of_named`, about
the named class. -/
theorem lixThomClassTerm_ne_zero (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    lixThomClassTerm hGc hGu ≠ 0 :=
  lixThomClass_ne_zero (M := fun i : Fin (lixRank dd + 1) =>
      Hmod2 (TopCat.of (↥sphereOne × baseM dd)) (2 * lixRank dd - 2 * (i : ℕ)))
    hGc hGu (2 * lixRank dd) (lixRank dd)
    (fun i => chernMul (hyperLH_range (lixBundle G hGc hGu) (lixRank dd)
      (rank_lixBundle G hGc hGu) (one_le_lixRank_dd dd)) i)
    (thomJmTotal (lixBundle G hGc hGu) (lixLHplus hGc hGu))
    (injective_thomJmTotal (lixBundle G hGc hGu) (one_le_lixRank_dd dd)
      (rank_lixBundle G hGc hGu) (lixLHplus hGc hGu))
    (range_thomJmTotal (lixBundle G hGc hGu) (rank_lixBundle G hGc hGu)
      (one_le_lixRank_dd dd) (lixLHplus hGc hGu))
    (lixTopCoeff_ne_zero dd)

/-! Printed on every build. -/

#print axioms lixThomClassTerm_ne_zero

end

end GroupApproximation.CharClass
