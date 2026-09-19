import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGysinConnectingCupLift

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AlexanderWhitney

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## 2. Face/vertex combinatorics of the charts -/

/-
**Faces commute with projection.**
-/
theorem sProj_faceSimplex (n k : ℕ) (i : Fin (k + 2))
    (ρ : singularSimplices (TopCat.of (Sphere n)) (k + 1)) :
    sProj n k (faceSimplex (TopCat.of (Sphere n)) k i ρ)
      = faceSimplex (TopCat.of (RP n)) k i (sProj n (k + 1) ρ) := by
  congr! 1

/-
**Vertex of a face.** The `j`-th vertex chart-value of the `i`-th boundary
face of `ρ` is the `(i.succAbove j)`-th vertex chart-value of `ρ`.
-/
theorem sChart_faceSimplex_vertex (n k : ℕ) (i : Fin (k + 2)) (j : Fin (k + 1))
    (ρ : singularSimplices (TopCat.of (Sphere n)) (k + 1)) :
    sChart n k (faceSimplex (TopCat.of (Sphere n)) k i ρ) (stdSimplex.vertex j)
      = sChart n (k + 1) ρ (stdSimplex.vertex (i.succAbove j)) := by
  unfold sChart; simp +decide [ faceSimplex ] ;
  simp +decide [ TopCat.toSSetObjEquiv, TopCat.toSSet ];
  simp +decide [ Homeomorph.ulift, ConcreteCategory.homEquiv ];
  simp +decide [ Homeomorph.continuousMapCongr, TopCat.uliftFunctor ];
  simp +decide [ Equiv.ulift, stdSimplex.map_vertex, SimplexCategory.δ ];
  congr

/-- **Last-vertex sheet of a face**, in terms of the vertices of `ρ`. -/
theorem gLastSheet_faceSimplex (n k : ℕ) (i : Fin (k + 2))
    (ρ : singularSimplices (TopCat.of (Sphere n)) (k + 1)) :
    gLastSheet n k (faceSimplex (TopCat.of (Sphere n)) k i ρ)
      = sheetParity n (sChart n (k + 1) ρ (stdSimplex.vertex (i.succAbove (Fin.last k)))) := by
  unfold gLastSheet
  rw [sChart_faceSimplex_vertex]

/-
**The front `k`-face is the last boundary face.**
-/
theorem frontSimplex_eq_lastFace (n k : ℕ) (σ' : singularSimplices (TopCat.of (RP n)) (k + 1)) :
    frontSimplex (TopCat.of (RP n)) k 1 σ'
      = faceSimplex (TopCat.of (RP n)) k (Fin.last (k + 1)) σ' := by
  simp +decide [ frontSimplex, faceSimplex ];
  convert rfl;
  ext i;
  simp +decide [ SimplexCategory.δ, frontFace ]



end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
