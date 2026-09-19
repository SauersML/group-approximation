import GroupApproximation.CharClass.LerayHirschCompact
import GroupApproximation.CharClass.CohomologyLHRingData
import GroupApproximation.CharClass.CohomologyTotalNontrivial
import GroupApproximation.CharClass.CohomologyParitySlice

/-!
# Naturality of the mod-2 Chern classes, and the slice

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

The mod-2 Chern classes of `CharClass/ChernClasses.lean` are read off the unique
monic relation satisfied by the tautological class of a projectivised bundle.
Naturality is therefore *not* a statement about bundles at all: it is the
statement that a square of rings carrying one power basis to another carries the
relation to the relation, and uniqueness of the relation does the rest.  That is
`chern_map_of_square`, and it mentions no topology.

The topological input is then exactly three facts, each of which is definitional
in `cc-bundle`'s projection model:

* `projComap_square` — the projective bundles form a commuting square over a base
  change, because `P(f^*E)` *is* the fibre product in this model;
* `tautEulerOf_comap` — the tautological line of `f^*E` is the pullback of the
  tautological line of `E`, so its Euler class is the pullback Euler class;
* the base change of a constant-rank bundle has the same constant rank.

`chern_comap` assembles them.  Its instance is `chernSliceNatural_chernOf`, which
is `cc-steenrod`'s `KnTwo.ChernSliceNatural` for the slice `y ↦ ((y, p₅), p₁)` of
the mapping-torus base, at any bundle of constant rank over that base.

## Manuscript status

Machinery.  Supplies the first of the two facts about the Chern class that the
slice identification of Lemma 2 consumes; the second is `KnTwo.ChernSliceValue`.
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

/-! ## 1. Naturality is a square of algebras -/

section Algebraic

variable {X P X' P' : TopCat.{0}}

/-- **Naturality of the mod-2 Chern classes, at the level of the algebra.**

`f` is the map of base rings and `g` the map of total rings.  The three
hypotheses say that `g` covers `f` over the two projections, that `g` carries the
tautological class to the tautological class, and that the ranks agree.  Nothing
else is used: the Chern classes are the coefficients of the unique monic relation
of the given degree satisfied by the generator, so the image of the relation is a
relation of the right degree for the new generator, and uniqueness identifies it
with the new relation. -/
theorem chern_map_of_square [Nonempty X] [Nonempty X']
    (D : LerayHirschData X P) (D' : LerayHirschData X' P')
    (f : TotalH X →+* TotalH X') (g : TotalH P →+* TotalH P')
    (hsq : ∀ a : TotalH X, g (TotalH.map D.proj a) = TotalH.map D'.proj (f a))
    (hgen : g (TotalH.of P 2 D.taut) = TotalH.of P' 2 D'.taut)
    (hdim : D'.rank = D.rank) (k : ℕ) :
    D'.chern k = f (D.chern k) := by
  letI := D.algebra
  letI := D'.algebra
  have hsquare : (algebraMap (TotalH X') (TotalH P')).comp f
      = g.comp (algebraMap (TotalH X) (TotalH P)) := RingHom.ext fun a => (hsq a).symm
  have hz : Polynomial.aeval (TotalH.of P 2 D.taut) D.chernPolynomial = 0 :=
    D.aeval_taut_chernPolynomial
  refine chernClass_map D.powerBasis D'.powerBasis f hdim ?_ k
  have hmap := Polynomial.map_aeval_eq_aeval_map hsquare D.chernPolynomial
    (TotalH.of P 2 D.taut)
  rw [hz, map_zero, hgen] at hmap
  exact hmap.symm

end Algebraic

/-! ## 2. The square a base change produces -/

section Comap

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The projective bundles commute with a base change.**  In the projection
model `P(f^*E)` is literally the set of pairs `(y, ρ)` with `ρ` under `E (f y)`,
so both composites send `(y, ρ)` to `f y`. -/
theorem projComap_square (f : C(Y, X)) (q : Bundle X ι) :
    cmap (projComap f q) ≫ projMapOf q = projMapOf (comap f q) ≫ cmap f := by
  apply TopCat.Hom.ext
  ext z
  rfl

/-- **The tautological class is natural.**  The tautological line of `f^*E` is the
pullback of the tautological line of `E` along the map of projective bundles --
in this model the two are the same function of the point -- so `cc-projective`'s
Euler class of the one is the pullback of the Euler class of the other. -/
theorem tautEulerOf_comap (f : C(Y, X)) (q : Bundle X ι) :
    pull (cmap (projComap f q)) 2 (tautEulerOf q) = tautEulerOf (comap f q) :=
  (eulerOfBundle_comap (show 1 ≤ 1 + tautCardOf ι by omega)
    (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) (tautLine q))
    (CPn.trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) (tautLine q)
      (trace_tautLine q))
    (projComap f q)).symm

/-- **Naturality of the mod-2 Chern classes.**  Over compact non-empty bases, the
Chern classes of the base change are the pullbacks of the Chern classes. -/
theorem chern_comap [CompactSpace X] [Nonempty X] [CompactSpace Y] [Nonempty Y]
    (f : C(Y, X)) (q : Bundle X ι) (s : ℕ) (hs : ∀ x, q.rank x = s) (hs1 : 1 ≤ s)
    (k : ℕ) :
    (lerayHirschData_of_graded
        (lerayHirschGraded_compact (comap f q) s (fun y => hs (f y)) hs1)).chern k
      = TotalH.map (cmap f)
          ((lerayHirschData_of_graded
            (lerayHirschGraded_compact q s hs hs1)).chern k) := by
  haveI : Nonempty (TopCat.of X) := ‹Nonempty X›
  haveI : Nonempty (TopCat.of Y) := ‹Nonempty Y›
  refine chern_map_of_square _ _ (TotalH.map (cmap f))
    (TotalH.map (cmap (projComap f q))) (fun a => ?_) ?_ rfl k
  · show TotalH.map (cmap (projComap f q)) (TotalH.map (projMapOf q) a)
      = TotalH.map (projMapOf (comap f q)) (TotalH.map (cmap f) a)
    rw [← Wu.totalH_map_comp, ← Wu.totalH_map_comp, projComap_square]
  · show TotalH.map (cmap (projComap f q))
        (TotalH.of (TopCat.of (Proj q)) 2 (tautEulerOf q))
      = TotalH.of (TopCat.of (Proj (comap f q))) 2 (tautEulerOf (comap f q))
    rw [TotalH.map_of, tautEulerOf_comap]

end Comap

/-! ## 3. The degreewise classes -/

section Degreewise

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The mod-2 Chern classes in their own degrees**, for a bundle of constant
rank `s ≥ 1` over a compact non-empty base. -/
def chernOf (q : Bundle X ι) (s : ℕ) (hs : ∀ x, q.rank x = s) (hs1 : 1 ≤ s)
    (k : ℕ) : Hmod2 (TopCat.of X) (2 * k) :=
  TotalH.component (TopCat.of X) (2 * k)
    ((lerayHirschData_of_graded (lerayHirschGraded_compact q s hs hs1)).chern k)

end Degreewise

/-! ## 4. The slice -/

section Slice

/-- The concrete sphere model is non-empty; the unit sphere of a non-trivial
normed space always is. -/
instance nonemptySphere (n : ℕ) :
    Nonempty (ThirdParty.HamSandwich.SphereOddDegree.Sphere n) :=
  (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype

/-- **The slice** `y ↦ ((y, p₅), p₁)` as a continuous map of the concrete bases,
the shape `Bundle.comap` consumes. -/
def nSliceMap (Y : Type) [TopologicalSpace Y]
    (p5 : ThirdParty.HamSandwich.SphereOddDegree.Sphere 5)
    (p1 : ThirdParty.HamSandwich.SphereOddDegree.Sphere 1) :
    C(Y, KnTwo.torusBase Y) :=
  ContinuousMap.prodMk
    (ContinuousMap.prodMk (ContinuousMap.id Y) (ContinuousMap.const Y p5))
    (ContinuousMap.const Y p1)

/-- It is `cc-steenrod`'s slice. -/
theorem cmap_nSliceMap (Y : Type) [TopologicalSpace Y]
    (p5 : ThirdParty.HamSandwich.SphereOddDegree.Sphere 5)
    (p1 : ThirdParty.HamSandwich.SphereOddDegree.Sphere 1) :
    cmap (nSliceMap Y p5 p1) = KnTwo.nSlice Y p5 p1 := by
  apply TopCat.Hom.ext
  exact ContinuousMap.ext fun _ => rfl

/-- **`ChernSliceNatural` for the mod-2 Chern classes.**  For any bundle of
constant rank `s ≥ 1` over the mapping-torus base, the classes restricted to the
slice are the classes of the restricted bundle.  This is the first of the two
facts the slice identification of Lemma 2 consumes. -/
theorem chernSliceNatural_chernOf (Y : Type) [TopologicalSpace Y] [CompactSpace Y]
    [Nonempty Y] (p5 : ThirdParty.HamSandwich.SphereOddDegree.Sphere 5)
    (p1 : ThirdParty.HamSandwich.SphereOddDegree.Sphere 1)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : Bundle (KnTwo.torusBase Y) ι) (s : ℕ) (hs : ∀ x, q.rank x = s)
    (hs1 : 1 ≤ s) :
    KnTwo.ChernSliceNatural Y p5 p1 (chernOf q s hs hs1)
      (chernOf (comap (nSliceMap Y p5 p1) q) s
        (fun y => hs (nSliceMap Y p5 p1 y)) hs1) := by
  intro k
  have hcomap := chern_comap (nSliceMap Y p5 p1) q s hs hs1 k
  simp only [chernOf]
  rw [hcomap, Wu.totalH_component_map, cmap_nSliceMap Y p5 p1]

end Slice

end

end LH
end CharClass
end GroupApproximation
