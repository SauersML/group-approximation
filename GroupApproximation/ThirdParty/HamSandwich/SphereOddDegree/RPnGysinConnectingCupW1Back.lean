import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGysinConnectingCupW1Lift

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AlexanderWhitney

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

theorem w1Cochain_backSimplex (n k : ℕ)
    (ρ : singularSimplices (TopCat.of (Sphere n)) (k + 1)) :
    cochainEval 1 (w1Cochain n) (backSimplex (TopCat.of (RP n)) k 1 (sProj n (k + 1) ρ))
      = sheetParity n (sChart n (k + 1) ρ (stdSimplex.vertex (Fin.castSucc (Fin.last k))))
        + sheetParity n (sChart n (k + 1) ρ (stdSimplex.vertex (Fin.last (k + 1)))) := by
  convert w1Value_of_lift n (backSimplex _ _ _ _) _ _ using 1;
  convert w1Cochain_eval n _ using 1;
  rotate_left;
  exact ( sChart n ( k + 1 ) ρ ).comp ( ContinuousMap.mk ( stdSimplex.map ( backFace k 1 |> SimplexCategory.Hom.toOrderHom ) ) ( by continuity ) );
  · intro x
    calc
      _ = rpChart n (k + 1) (sProj n (k + 1) ρ)
          (stdSimplex.map (backFace k 1 |> SimplexCategory.Hom.toOrderHom) x) :=
        (rpChart_sProj n (k + 1) ρ _).symm
      _ = rpChart n 1 (backSimplex (TopCat.of (RP n)) k 1
          (sProj n (k + 1) ρ)) x := rfl
  · congr! 2;
    · simp +decide [ stdSimplex.vertex, backFace ];
      congr;
    · simp +decide [ backFace, stdSimplex.map_vertex ];
      congr! 2;
      exact Fin.ext ( by simp +decide [ add_comm ] )


end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
