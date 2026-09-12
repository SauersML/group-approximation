import GroupApproximation.CharClass.ChernSliceNaturality
import GroupApproximation.CharClass.ChernEulerPushforwardSize
import GroupApproximation.CharClass.BundleInvariance

/-!
# The mod-2 Chern classes see only the isomorphism class

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

`CharClass/ChernSliceNaturality.lean` reduces naturality of the Chern classes to a
square of rings.  Invariance is the same reduction with the identity ring map: a
`BundleIso` gives a homeomorphism of projectivisations over the base, and carries
the tautological line to the tautological line, so the square commutes and the
generators correspond.

The one place work is needed is the generator.  `tautEulerOf` pushes the
tautological line into a `Fin` whose size is read off the index type, and two
isomorphic bundles with index types of different cardinalities push into
*different* `Fin`s.  `CPn.eulerOfBundle_pushforward_iso` is exactly that gap, and
`tautEulerOf_eq_of_bundleIso` is its application.

## Main declarations

* `tautEulerOf_eq_of_bundleIso` — the tautological class transports.
* `chernOf_eq_of_bundleIso` — **the degreewise Chern classes are an isomorphism
  invariant**, across index types of different sizes.
* `chernOf_pushforward` — hence they do not change under a pushforward along any
  injection.
* `chernOf_congr` — and pointwise-equal bundles have equal classes.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LHCast

noncomputable section

set_option linter.unusedSectionVars false

variable {X : Type} [TopologicalSpace X]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The map of projective bundles induced by a bundle isomorphism, in the direction
the square of rings wants: pullback along it goes from `P(p)` to `P(q)`. -/
def projMapOfIso {p : Bundle X ι} {q : Bundle X κ} (e : BundleIso p q) :
    C(Proj q, Proj p) :=
  ⟨e.symm.toProjHomeo, e.symm.toProjHomeo.continuous⟩

/-- It lies over the base. -/
theorem projMapOfIso_square {p : Bundle X ι} {q : Bundle X κ} (e : BundleIso p q) :
    cmap (projMapOfIso e) ≫ projMapOf p = projMapOf q := by
  apply TopCat.Hom.ext
  exact ContinuousMap.ext fun _ => rfl

/-- **The tautological class transports along a bundle isomorphism.**

The two sides push their tautological lines into `Fin`s of different sizes, one
read off `ι` and one off `κ`, so this is not an instance of the fixed-size
independence lemmas; it is `CPn.eulerOfBundle_pushforward_iso`, whose whole point
is that the size is free. -/
theorem tautEulerOf_eq_of_bundleIso {p : Bundle X ι} {q : Bundle X κ}
    (e : BundleIso p q) :
    pull (cmap (projMapOfIso e)) 2 (tautEulerOf p) = tautEulerOf q := by
  have hcomap := eulerOfBundle_comap (show 1 ≤ 1 + tautCardOf ι by omega)
    (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) (tautLine p))
    (CPn.trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) (tautLine p)
      (trace_tautLine p))
    (projMapOfIso e)
  refine hcomap.symm.trans ?_
  exact CPn.eulerOfBundle_pushforward_iso (1 + tautCardOf ι) (1 + tautCardOf κ)
    (by omega) (by omega)
    (comap (projMapOfIso e) (tautLine p)) (tautLine q)
    (fun z => trace_tautLine p _) (trace_tautLine q)
    (BundleIso.symm (BundleIso.toTautIso e.symm))
    (tautEmbOf_injective ι) (tautEmbOf_injective κ)

/-- **The degreewise mod-2 Chern classes are an isomorphism invariant.**

The index types are unrelated and may have different cardinalities; only the rank
has to agree, and it does because an isomorphism preserves it pointwise. -/
theorem chernOf_eq_of_bundleIso [CompactSpace X] [Nonempty X]
    {p : Bundle X ι} {q : Bundle X κ} (e : BundleIso p q) (s : ℕ)
    (hsp : ∀ x, p.rank x = s) (hsq : ∀ x, q.rank x = s) (hs1 : 1 ≤ s) (k : ℕ) :
    chernOf p s hsp hs1 k = chernOf q s hsq hs1 k := by
  haveI : Nonempty (TopCat.of X) := ‹Nonempty X›
  have hsquare : ∀ a : TotalH (TopCat.of X),
      TotalH.map (cmap (projMapOfIso e)) (TotalH.map (projMapOf p) a)
        = TotalH.map (projMapOf q) (RingHom.id (TotalH (TopCat.of X)) a) := by
    intro a
    rw [← Wu.totalH_map_comp, projMapOfIso_square e]
    rfl
  have hgen : TotalH.map (cmap (projMapOfIso e))
      (TotalH.of (TopCat.of (Proj p)) 2 (tautEulerOf p))
      = TotalH.of (TopCat.of (Proj q)) 2 (tautEulerOf q) := by
    rw [TotalH.map_of, tautEulerOf_eq_of_bundleIso e]
  have hchern := chern_map_of_square
    (lerayHirschData_of_graded (lerayHirschGraded_compact p s hsp hs1))
    (lerayHirschData_of_graded (lerayHirschGraded_compact q s hsq hs1))
    (RingHom.id (TotalH (TopCat.of X)))
    (TotalH.map (cmap (projMapOfIso e))) hsquare hgen rfl k
  exact congrArg (TotalH.component (TopCat.of X) (2 * k)) hchern.symm

/-- **Pushing along an injection does not change the classes.**  The rank-one case
is the statement that the Euler class of a line does not depend on the size of the
index it is presented in. -/
theorem chernOf_pushforward [CompactSpace X] [Nonempty X] (ϕ : ι → κ)
    (hϕ : Function.Injective ϕ) (p : Bundle X ι) (s : ℕ)
    (hsp : ∀ x, p.rank x = s) (hsq : ∀ x, (pushforward ϕ hϕ p).rank x = s)
    (hs1 : 1 ≤ s) (k : ℕ) :
    chernOf (pushforward ϕ hϕ p) s hsq hs1 k = chernOf p s hsp hs1 k :=
  (chernOf_eq_of_bundleIso (pushforwardIso ϕ hϕ p) s hsp hsq hs1 k).symm

/-- **Pointwise-equal bundles have equal classes.**  The rank proofs move with the
bundle, so they are transported rather than reused. -/
theorem chernOf_congr [CompactSpace X] [Nonempty X] {p q : Bundle X ι}
    (h : ∀ x, p x = q x) (s : ℕ) (hsp : ∀ x, p.rank x = s) (hsq : ∀ x, q.rank x = s)
    (hs1 : 1 ≤ s) (k : ℕ) :
    chernOf p s hsp hs1 k = chernOf q s hsq hs1 k := by
  have hpq : p = q := DFunLike.ext _ _ h
  subst hpq
  rfl

end

end LH
end CharClass
end GroupApproximation
