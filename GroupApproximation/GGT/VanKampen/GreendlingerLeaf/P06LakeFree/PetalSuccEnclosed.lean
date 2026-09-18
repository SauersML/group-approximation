import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSuccInv
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSuccReach
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Def
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: the side of a successor walk on `∂K` (lane gl-p06-17)

Infrastructure for `P06LakeFree.cellPocketLakeFreePetalSucc_of_petalTurn`
(`P06LakeFree/PetalSuccStatement.lean`).  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## Truth check and proof

Let `K` be a lake-free cell pocket face set, `W₀ ≠ []` a walk turning to its successors
(`SuccTurn X W₀`), and `L = invDarts X W₀` with a rotation `L.rotate m` a sublist of `∂K`.  Put
`S = sideFaces L`.  Then `EnclosedFaceSetSucc X S W₀` and `S ⊆ K.faces`.

1. *Boundary.*  Every `e ∈ L` is a boundary dart of `K` (`BoundaryCycle.cycle_mem_iff`).
2. *No repeats.*  `L` is a sublist of the duplicate-free `∂K` (after rotating), so `W₀ = invDarts L`
   has no repeats.
3. *No bridges.*  If `d, α d ∈ W₀` then `α d, d ∈ L`, so `faceOf d ∈ K` and `faceOf d ∉ K`.
4. *Noncrossing.*  `succTurn_isNoncrossingClosedWalk_invDarts`, so the boundary darts of `S` are
   exactly the darts of `L` (`IsNoncrossingClosedWalk.isBoundaryDart_sideFaces_iff`), all boundary
   darts of `K`.
5. *Lake freeness.*  Every face `f ∉ K` lies in the exterior piece of `K`, so
   `outerFace ∈ S ↔ f ∈ S` (`petalSucc_mem_iff_of_mem_component`).
6. *Outer face.*  Pick `d ∈ W₀`.  Then `α d ∈ L`, so `faceOf d ∉ K` (item 1) and `faceOf d ∉ S`
   (item 4).  By item 5, `outerFace ∉ S`.
7. *Inside `K`.*  A face `f ∈ S` off `K` would put `outerFace ∈ S` by item 5.
8. *Membership.*  `d ∈ W₀ ↔ α d ∈ L ↔ faceOf (α d) ∈ S ∧ faceOf d ∉ S`.  Conversely, with
   `faceOf d ∉ S` and `α d ∈ W₀`, the dart `d ∈ L` is a boundary dart of `S`, so `faceOf d ∈ S`:
   impossible, so only the first case occurs.
9. *Walk fields.*  Chain, closing and turning from `PetalSuccWalk.lean`; `turn_next` is `SuccTurn`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7(b); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc

open Embedded SimpleClosedWalkSides

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
  {K : CellPocketFaceSet D eps X i j} {W₀ : List X.toCombMap.Dart} {m : ℕ}

/-- Darts of a walk on `∂K` are boundary darts of `K`. -/
theorem petalSucc_boundary_of_sublist
    (hsl : ((invDarts X W₀).rotate m).Sublist K.boundary.cycle) {e : X.toCombMap.Dart}
    (he : e ∈ invDarts X W₀) :
    X.toCombMap.faceOf e ∈ K.faces ∧ X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ K.faces :=
  (K.boundary.cycle_mem_iff e).mp (hsl.subset (List.mem_rotate.mpr he))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.petalSucc_boundary_of_sublist

/-- A walk whose inverse lies on `∂K` has no repeats. -/
theorem petalSucc_nodup (hsl : ((invDarts X W₀).rotate m).Sublist K.boundary.cycle) :
    W₀.Nodup := by
  have hL : (invDarts X W₀).Nodup := List.nodup_rotate.mp (hsl.nodup K.boundary.cycle_nodup)
  rw [← Petal.petal_invDarts_invDarts X W₀]
  exact List.Nodup.map X.toCombMap.alpha.injective (List.nodup_reverse.mpr hL)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.petalSucc_nodup

/-- A walk whose inverse lies on `∂K` has no bridges. -/
theorem petalSucc_no_bridge (hsl : ((invDarts X W₀).rotate m).Sublist K.boundary.cycle) :
    ∀ d ∈ W₀, X.toCombMap.alpha d ∉ W₀ := by
  intro d hd had
  have h1 : d ∈ invDarts X W₀ := (Petal.petal_mem_invDarts_iff X).mpr had
  have h2 : X.toCombMap.alpha d ∈ invDarts X W₀ := by
    rw [Petal.petal_mem_invDarts_iff X, X.toCombMap.alpha_involutive d]
    exact hd
  exact (petalSucc_boundary_of_sublist hsl h1).2 (petalSucc_boundary_of_sublist hsl h2).1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.petalSucc_no_bridge

/-- **The side of a walk on the boundary of a lake-free face set** avoids the outer face and lies
inside the face set. -/
theorem petalSucc_outer_subset (hfree : CellPocketLakeFree K) (hne : W₀ ≠ [])
    (hL : IsNoncrossingClosedWalk X.toCombMap (invDarts X W₀))
    (hsl : ((invDarts X W₀).rotate m).Sublist K.boundary.cycle) :
    X.outerFace ∉ sideFaces X.toCombMap (invDarts X W₀) ∧
      sideFaces X.toCombMap (invDarts X W₀) ⊆ K.faces := by
  have hbdS : ∀ x ∈ invDarts X W₀,
      X.toCombMap.faceOf x ∈ sideFaces X.toCombMap (invDarts X W₀) ∧
        X.toCombMap.faceOf (X.toCombMap.alpha x) ∉ sideFaces X.toCombMap (invDarts X W₀) :=
    fun x hx => (hL.isBoundaryDart_sideFaces_iff X.planar x).mpr hx
  have hkey : ∀ f, f ∉ K.faces → (X.outerFace ∈ sideFaces X.toCombMap (invDarts X W₀) ↔
      f ∈ sideFaces X.toCombMap (invDarts X W₀)) := fun f hf =>
    petalSucc_mem_iff_of_mem_component (S := sideFaces X.toCombMap (invDarts X W₀))
      (T := K.faces) (fun x hx => petalSucc_boundary_of_sublist hsl
        ((hL.isBoundaryDart_sideFaces_iff X.planar x).mp hx)) (hfree f hf)
  have hout : X.outerFace ∉ sideFaces X.toCombMap (invDarts X W₀) := by
    intro ho
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil W₀ hne
    have hαd : X.toCombMap.alpha d ∈ invDarts X W₀ := by
      rw [Petal.petal_mem_invDarts_iff X, X.toCombMap.alpha_involutive d]
      exact hd
    have hK := (petalSucc_boundary_of_sublist hsl hαd).2
    have hS := (hbdS _ hαd).2
    rw [X.toCombMap.alpha_involutive d] at hK hS
    exact hS ((hkey _ hK).mp ho)
  refine ⟨hout, fun f hf => ?_⟩
  by_contra hfK
  exact hout ((hkey f hfK).mpr hf)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.petalSucc_outer_subset

/-- **Membership in a successor walk** through the side of its noncrossing inverse. -/
theorem petalSucc_mem_iff (hL : IsNoncrossingClosedWalk X.toCombMap (invDarts X W₀))
    (d : X.toCombMap.Dart) :
    d ∈ W₀ ↔ X.toCombMap.faceOf d ∉ sideFaces X.toCombMap (invDarts X W₀) ∧
      (X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap (invDarts X W₀) ∨
        X.toCombMap.alpha d ∈ W₀) := by
  have hbd : ∀ x, x ∈ invDarts X W₀ ↔
      X.toCombMap.faceOf x ∈ sideFaces X.toCombMap (invDarts X W₀) ∧
        X.toCombMap.faceOf (X.toCombMap.alpha x) ∉ sideFaces X.toCombMap (invDarts X W₀) :=
    fun x => (hL.isBoundaryDart_sideFaces_iff X.planar x).symm
  have hαd : X.toCombMap.alpha d ∈ invDarts X W₀ ↔ d ∈ W₀ := by
    rw [Petal.petal_mem_invDarts_iff X, X.toCombMap.alpha_involutive d]
  constructor
  · intro hd
    obtain ⟨h1, h2⟩ := (hbd (X.toCombMap.alpha d)).mp (hαd.mpr hd)
    rw [X.toCombMap.alpha_involutive d] at h2
    exact ⟨h2, Or.inl h1⟩
  · rintro ⟨hnot, h | h⟩
    · refine hαd.mp ((hbd (X.toCombMap.alpha d)).mpr ⟨h, ?_⟩)
      rw [X.toCombMap.alpha_involutive d]
      exact hnot
    · exact (hnot ((hbd d).mp ((Petal.petal_mem_invDarts_iff X).mpr h)).1).elim

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.petalSucc_mem_iff

/-- **A successor walk on `∂K` encloses its side**, which lies inside `K`. -/
theorem petalSucc_enclosedFaceSetSucc (hfree : CellPocketLakeFree K) (hne : W₀ ≠ [])
    (hT : SuccTurn X W₀) (hsl : ((invDarts X W₀).rotate m).Sublist K.boundary.cycle) :
    EnclosedFaceSetSucc X (sideFaces X.toCombMap (invDarts X W₀)) W₀ ∧
      sideFaces X.toCombMap (invDarts X W₀) ⊆ K.faces := by
  have hnd := petalSucc_nodup hsl
  have hL := succTurn_isNoncrossingClosedWalk_invDarts hne hnd hT (petalSucc_no_bridge hsl)
  obtain ⟨hout, hsub⟩ := petalSucc_outer_subset hfree hne hL hsl
  exact ⟨⟨⟨hout, hne, hnd, succTurn_chain hT, succTurn_closes hT hne, petalSucc_mem_iff hL,
    succTurn_turn_mem hT⟩, hT⟩, hsub⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.petalSucc_enclosedFaceSetSucc

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc
