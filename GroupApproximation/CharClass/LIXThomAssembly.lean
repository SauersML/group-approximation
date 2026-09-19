import GroupApproximation.CharClass.LIXThomLH

/-!
# The degreewise Thom data from the pair sequence

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`LIXThomDatum` takes two hypotheses: the Leray–Hirsch instance, and the
degreewise `ThomDeg` data.  This file builds the second from the first together
with the pair sequence, so that the instance becomes the sole input.

## The three components, and where each comes from

With `E` the coefficient equivalence of `LIXThomLH.lhTopEquiv`:

* **`jm` is `relToAbs` followed by `E` inverted.**  Nothing to prove; it is a
  composition of a morphism with an equivalence.
* **`hinj` is injectivity of `relToAbs`.**  This is *not* free.  Pair-sequence
  exactness gives `ker relToAbs = range relDelta`, so injectivity needs the
  connecting map one degree down to vanish, equivalently the restriction
  `absToSub` to be surjective at degree `2r - 1`.  Under Leray–Hirsch that
  restriction is the coordinate projection, which is surjective — but making that
  identification is exactly the input below.
* **`hrange` is `range relToAbs = ker absToSub`** transported through `E`, which
  is exactness at the absolute group, plus the identification of `absToSub` with
  `ThomDeg.restrictMap g`.

## The single named input

`habs` below says the restriction of the pair, read in Leray–Hirsch coordinates,
**is** the coordinate map of the Chern relation.  That is `cc-projective`'s
tautological restriction composed with
`ThomChernBasis.genPow_dim_eq_neg_basisSum`, and it is the one place the geometry
of the projectivisation enters.  It is stated rather than assumed silently
because folding it into "over the Leray–Hirsch instance" is precisely the
overstatement this lane made twice tonight.

## Main declarations

* `thomJm` — the map out of the relative group, in coordinates.
* `thomData_of_absToSub` — **the `ThomDeg` data**, from the pair sequence and
  `habs`.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.CharClass.LH

namespace GroupApproximation.CharClass

noncomputable section

variable {X P : TopCat.{0}}


/-! ## The injectivity, from a surjectivity one degree down -/

/-- **`relToAbs` is injective once the restriction is surjective one degree down.**

Exactness gives `ker relToAbs = range relDelta`, and the composite
`absToSub ≫ relDelta` vanishes, so a surjective `absToSub` forces `relDelta` to be
zero and the kernel with it.  This is the shape `cc-cohom-api`'s
`absToSub_surjective_of_graded` discharges by one application: their statement is
about the coefficient description below the top degree, this lemma is the pair
algebra that consumes it. -/
theorem relToAbs_injective_of_absToSub_surjective (R : Type) [CommRing R]
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (hsurj : Function.Surjective (absToSub R A n).hom) :
    Function.Injective (relToAbs R X A (n + 1)).hom := by
  intro a b hab
  have hzero : (relToAbs R X A (n + 1)).hom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨w, hw⟩ := relLES_exact_rel R X A n (a - b) hzero
  obtain ⟨c, rfl⟩ := hsurj w
  have hcomp := absToSub_comp_relDelta R X A n
  have hgo : (relDelta R X A n).hom ((absToSub R A n).hom c) = 0 := by
    have := congrArg (fun f : (cochainCx R X).homology n ⟶ _ => f.hom c) hcomp
    simpa using this
  rw [hgo] at hw
  exact sub_eq_zero.mp hw.symm

/-- The map out of the relative group in Leray–Hirsch coordinates: restrict to
the absolute group, then read coefficients. -/
def thomJm {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ (r + 1)) (Z : Set P) :
    ↥(relCohomology (ZMod 2) P Z (2 * r))
      →ₗ[ZMod 2] ((i : Fin (r + 1)) → lhCoeffTop X r i) :=
  (lhTopEquiv L).symm.toLinearMap.comp (relToAbs (ZMod 2) P Z (2 * r)).hom

@[simp] theorem thomJm_apply {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ (r + 1)) (Z : Set P)
    (z : ↥(relCohomology (ZMod 2) P Z (2 * r))) :
    thomJm L Z z = (lhTopEquiv L).symm ((relToAbs (ZMod 2) P Z (2 * r)).hom z) := rfl

/-- **The degreewise Thom data, from the pair sequence.**

`hinj0` is injectivity of `relToAbs`, which pair-sequence exactness reduces to
the vanishing of the connecting map one degree down; `habs` identifies the
restriction of the pair, in coordinates, with the coordinate map of the Chern
relation.  Given those, `jm`, `hinj` and `hrange` come out, and `LIXThomDatum`'s
second hypothesis is discharged. -/
theorem thomData_of_absToSub {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ (r + 1)) (Z : Set P)
    {M : Fin (r + 1) → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 2) (M i)]
    (g : ∀ i : Fin r, M (Fin.last r) →ₗ[ZMod 2] M i.castSucc)
    (coeff : ((i : Fin (r + 1)) → lhCoeffTop X r i) ≃ₗ[ZMod 2] (∀ i, M i))
    (hinj0 : Function.Injective (relToAbs (ZMod 2) P Z (2 * r)).hom)
    (habs : LinearMap.range
        ((coeff.toLinearMap.comp (thomJm L Z)))
      = LinearMap.ker (ThomDeg.restrictMap g)) :
    ∃ (jm : ↥(relCohomology (ZMod 2) P Z (2 * r)) →ₗ[ZMod 2] (∀ i, M i))
      (_ : Function.Injective jm),
      LinearMap.range jm = LinearMap.ker (ThomDeg.restrictMap g) := by
  refine ⟨coeff.toLinearMap.comp (thomJm L Z), ?_, habs⟩
  intro a b hab
  refine hinj0 ?_
  have h1 : (lhTopEquiv L).symm ((relToAbs (ZMod 2) P Z (2 * r)).hom a)
      = (lhTopEquiv L).symm ((relToAbs (ZMod 2) P Z (2 * r)).hom b) :=
    coeff.injective hab
  exact (lhTopEquiv L).symm.injective h1

/-! Printed on every build. -/

#print axioms thomData_of_absToSub

end

end GroupApproximation.CharClass
