import GroupApproximation.PropertyTT.RankFourRelativeTT

/-!
# Rank-four root rigidity for finite characteristic-two quotients

A surjective map from a free `ZMod 2`-algebra on a finite type transports the
internally proved free-algebra rank-four root estimate to its quotient.
The downstream rank-four theorem uses index permutations to supply all six
roots meeting the last coordinate.
-/

namespace GroupApproximation
namespace FiniteTypeRankFourRelativeTT

universe v

noncomputable section

variable {R : Type} [Ring R]

abbrev E4 := elementaryGroup (Fin 4) R

abbrev X03 : Subgroup (E4 (R := R)) :=
  elementaryRootSubgroup (0 : Fin 4) 3 (by decide)

/-- Relative `(TT)/T` for one rank-four root descends through every
surjective finite-free characteristic-two presentation. -/
theorem hasRelativeTTmodT_X03 (X : Type) [Fintype X]
    (f : FreeAlgebra (ZMod 2) X →+* R) (hf : Function.Surjective f) :
    HasRelativeTTmodT.{_, v} (E4 (R := R)) (X03 (R := R)) := by
  let q : elementaryGroup (Fin 4) (FreeAlgebra (ZMod 2) X) →*
      E4 (R := R) :=
    elementaryGroupMap (ι := Fin 4) f
  have hq : Function.Surjective q :=
    elementaryGroupMap_surjective_of_surjective f hf
  have hqRoot (i j : Fin 4) (hij : i ≠ j)
      (a : FreeAlgebra (ZMod 2) X) :
      q (elementaryRoot i j hij a) = elementaryRoot i j hij (f a) := by
    apply Subtype.ext
    exact elementaryMatrixUnitMap_elementaryUnit f i j hij a
  apply HasRelativeTTmodT.of_surjective q hq
    (RankFourColumnGeometry.X03 X) (X03 (R := R))
  · intro g hg
    obtain ⟨a, rfl⟩ := hg
    obtain ⟨c, rfl⟩ := hf a
    exact ⟨elementaryRoot (0 : Fin 4) 3 (by decide) c,
      ⟨c, rfl⟩, hqRoot 0 3 (by decide) c⟩
  · exact RankFourRelativeTT.hasRelativeTTmodT_X03 X

end
end FiniteTypeRankFourRelativeTT
end GroupApproximation
