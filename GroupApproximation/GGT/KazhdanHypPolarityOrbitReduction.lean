import GroupApproximation.GGT.KazhdanHypSymplecticPolarity
import GroupApproximation.GGT.KazhdanHypGQLinkIdentification

/-!
# Cyclic reductions for the polarity-fixed `W(8)` table

The generator `gamma` below is the chosen cyclic subgroup generator on the
point set.  Its triangle permutation `tau` and `TriangleEquivariant` witness
state invariance under that generator, so the existing cyclic-orbit covers
transport every girth-eight clause from stored representatives.  The SDP
theorem fixes the point-to-line map to the certified Tits polarity, so a
polarity-fixed table supplies only representative rows and representative
link checks.

The interface is action-parametric because the current development has not
yet introduced concrete Suzuki-group matrices.  A supplied order-seven or
order-thirteen Suzuki element instantiates `gamma` directly, and a later
full-group reduction can use the same transfer theorem for each generating
action.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace GroupApproximation
namespace KazhdanHyp

open scoped BigOperators

namespace SymplecticQuadrangle

open TitsPolarity

/-! ## The polarity action on signed link vertices -/

/-- Conjugating a point action by the Tits polarity gives its induced line
action, so a polarity automorphism acts on both parts of the incidence link. -/
noncomputable def polarityLinePerm (gamma : Equiv.Perm Point) : Line ≃ Line :=
  titsPolarity.symm.trans (gamma.trans titsPolarity)

/-- The induced action on the bipartite point/line vertices used by the
quadrangle association scheme. -/
noncomputable def polarityVertexPerm (gamma : Equiv.Perm Point) :
    Equiv.Perm (Point ⊕ Line) where
  toFun v := match v with
    | Sum.inl p => Sum.inl (gamma p)
    | Sum.inr l => Sum.inr (polarityLinePerm gamma l)
  invFun v := match v with
    | Sum.inl p => Sum.inl (gamma.symm p)
    | Sum.inr l => Sum.inr ((polarityLinePerm gamma).symm l)
  left_inv := by
    intro v
    cases v with
    | inl p => simp
    | inr l => simp
  right_inv := by
    intro v
    cases v with
    | inl p => simp
    | inr l => simp

theorem signedVertexEquiv_polarity_intertwines
    (gamma : Equiv.Perm Point) (u : Point × Bool) :
    signedVertexEquiv titsPolarity (signedPerm gamma u) =
      polarityVertexPerm gamma (signedVertexEquiv titsPolarity u) := by
  rcases u with ⟨p, s⟩
  cases s <;>
    simp [signedVertexEquiv, signedPerm, polarityVertexPerm, polarityLinePerm]

/-- The only link-side datum needed for a polarity orbit reduction is
invariance of the rational quadrangle adjacency table under the induced
vertex action, so the intertwining identity is supplied by the preceding
lemma. -/
structure PolarityLinkEquivariance
    (gamma : Equiv.Perm Point)
    (Q : QuadrangleLinkData (Point ⊕ Line)) where
  adj_invariant : ∀ x y,
    Q.adj (polarityVertexPerm gamma x) (polarityVertexPerm gamma y) =
      Q.adj x y

noncomputable def PolarityLinkEquivariance.toSingerLinkEquivariance
    {gamma : Equiv.Perm Point}
    {Q : QuadrangleLinkData (Point ⊕ Line)}
    (S : PolarityLinkEquivariance gamma Q) :
    SingerLinkEquivariance gamma Q (signedVertexEquiv titsPolarity) where
  rho := polarityVertexPerm gamma
  intertwines := signedVertexEquiv_polarity_intertwines gamma
  adj_invariant := S.adj_invariant

/-! ## Girth-eight reduction -/

/-- A cyclic polarity action reduces `GirthEightChecks` to its orbit roots,
so the five root clauses imply the global check. -/
theorem girthEightChecks_of_polarity_orbits
    {TriangleIndex TriangleRep VertexRep PairRep : Type}
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    [Fintype TriangleRep] [Fintype VertexRep] [Fintype PairRep]
    (gamma : Equiv.Perm Point) (tau : Equiv.Perm TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Point) (d : ℕ)
    (hT : TriangleEquivariant gamma tau T)
    (triangleCover : CyclicOrbitCover tau TriangleRep)
    (vertexCover : CyclicOrbitCover (signedPerm gamma) VertexRep)
    (pairCover : CyclicOrbitCover (signedPairPerm gamma) PairRep)
    (hpositive : ∀ r k, (T (triangleCover.root r) k).2 = true)
    (hregular : ∀ r, TriangularHodgeLayer.degree T (vertexCover.root r) = d)
    (hsimple : ∀ r, let p := pairCover.root r
      TriangularHodgeLayer.adjacencyCount T p.1 p.2 ≤ 1)
    (hfour : ∀ r, let p := pairCover.root r
      p.1 ≠ p.2 → linkTwoStep T p.1 p.2 ≤ 1)
    (hsix : ∀ r, let p := pairCover.root r
      TriangularHodgeLayer.adjacencyCount T p.1 p.2 = 0 →
        linkThreeStep T p.1 p.2 ≤ 1) :
    GirthEightChecks T d := by
  exact girthEightChecks_of_singer_orbits gamma tau T d hT triangleCover
    vertexCover pairCover hpositive hregular hsimple hfour hsix

/-! ## Polarity-fixed certificate transfer -/

/-- A polarity-fixed cyclic table needs only its `27` representative rows and
the three orbit-root link clauses, so the existing W(8) transfer then gives
the rational `5/9` Gram certificate for the literal table. -/
theorem girthEightSDPChecks_of_polarityOrbitRows
    {TriangleIndex TriangleRep VertexRep PairRep : Type}
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    [Fintype TriangleRep] [Fintype VertexRep] [Fintype PairRep]
    {T : TriangleIndex →
      TriangularHodgeLayer.Triangle Point}
    (gamma : Equiv.Perm Point) (tau : Equiv.Perm TriangleIndex)
    (hT : TriangleEquivariant gamma tau T)
    (triangleCover : CyclicOrbitCover tau TriangleRep)
    (vertexCover : CyclicOrbitCover (signedPerm gamma) VertexRep)
    (pairCover : CyclicOrbitCover (signedPairPerm gamma) PairRep)
    (hrows : Fintype.card TriangleRep = 27 ∧
      ∀ r k, (T (triangleCover.root r) k).2 = true)
    (hregular : ∀ r, TriangularHodgeLayer.degree T (vertexCover.root r) = 9)
    (hsimple : ∀ r, let p := pairCover.root r
      TriangularHodgeLayer.adjacencyCount T p.1 p.2 ≤ 1)
    (hfour : ∀ r, let p := pairCover.root r
      p.1 ≠ p.2 → linkTwoStep T p.1 p.2 ≤ 1)
    (hsix : ∀ r, let p := pairCover.root r
      TriangularHodgeLayer.adjacencyCount T p.1 p.2 = 0 →
        linkThreeStep T p.1 p.2 ≤ 1)
    (S : PolarityLinkEquivariance gamma wEightQuadrangleLinkData)
    (hroot : ∀ r,
      (TriangularHodgeLayer.adjacencyCount T
        (pairCover.root r).1 (pairCover.root r).2 : ℚ) =
      wEightQuadrangleLinkData.adj
        (signedVertexEquiv titsPolarity (pairCover.root r).1)
        (signedVertexEquiv titsPolarity (pairCover.root r).2)) :
    GirthEightSDPChecks T 9 (5 / 9)
      (QuadrangleLinkData.reindex
        wEightQuadrangleLinkData
        (signedVertexEquiv titsPolarity)).gramRow := by
  have hgeom := girthEightChecks_of_polarity_orbits gamma tau T 9 hT
    triangleCover vertexCover pairCover hrows.2 hregular hsimple hfour hsix
  have hdeg : (9 : ℚ) = wEightQuadrangleLinkData.deg := by
    exact wEightQuadrangleLinkData_parameters.1.symm
  have hgap : wEightQuadrangleLinkData.gapValue = 5 / 9 := by
    exact wEightQuadrangleLinkData_parameters.2
  have hcert := SingerLinkEquivariance.girthEightSDPChecks_of_singerPairRoots
    gamma wEightQuadrangleLinkData (signedVertexEquiv titsPolarity)
    tau T hgeom hT S.toSingerLinkEquivariance pairCover hroot hdeg
  simpa [QuadrangleLinkData.reindex_gapValue, hgap] using hcert

end SymplecticQuadrangle
end KazhdanHyp
end GroupApproximation
