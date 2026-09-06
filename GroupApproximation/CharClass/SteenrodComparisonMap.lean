import GroupApproximation.CharClass.SteenrodChainMapNat
import GroupApproximation.CharClass.CartanTargetComplex

/-!
# `Φ : src ⟶ tgt`

Everything the acyclic-models comparison asks of Steenrod's diagonal is already
proved; this file only assembles it into the shape the theorem consumes.

* degreewise a map of `Λ`-modules — `PhiHom`, which is `Λ`-linear by
  construction, since the source is free over `Λ` and the extension from a basis
  is the whole of `Λ`-linearity;
* a chain map — `dTgt_PhiHom`;
* natural in the space — `PhiHom_naturality`.

The two lanes' pushforwards on the target agree definitionally
(`pairIdxMap f` and `pairIdxPush f k` are the same term), so nothing is
transported across the seam.
-/

open CategoryTheory

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- **Steenrod's diagonal on one space**, as a map of complexes over the group
ring. -/
noncomputable def PhiCx (X : TopCat.{0}) :
    srcComplex singularBoundary X ⟶ tgtCx X where
  f k := ModuleCat.ofHom (PhiHom X k)
  comm' := by
    rintro i j (rfl : j + 1 = i)
    rw [srcComplex_d, tgtCx_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    show dTgt X (ZMod 2) j (PhiHom X (j + 1) y)
        = PhiHom X j (wDiff singularBoundary X j y)
    exact dTgt_PhiHom X j y

@[simp] theorem PhiCx_f (X : TopCat.{0}) (k : ℕ) :
    (PhiCx X).f k = ModuleCat.ofHom (PhiHom X k) := rfl

/-- **Steenrod's equivariant diagonal, as a natural transformation.**  This is
the `Φ` the Cartan comparison consumes. -/
noncomputable def PhiNat : src singularBoundary ⟶ tgt where
  app X := PhiCx X
  naturality {X Y} f := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    show PhiHom Y k (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k) y)
        = pairMapLambda f k (PhiHom X k y)
    exact (PhiHom_naturality f k y).symm

@[simp] theorem PhiNat_app (X : TopCat.{0}) : PhiNat.app X = PhiCx X := rfl

end

end Steenrod
end CharClass
end GroupApproximation
