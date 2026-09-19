import GroupApproximation.GGT.VanKampen.RelativeGreendlinger

/-!
# Exterior-arc conversion at a supplied boundary word

The original fixed-relator statement is retained for the counterexample in
`VanKampen/ExteriorArcCounterexample`.  The repaired statement permits the
cyclic rotation needed to make the source arc a prefix.
-/

namespace GroupApproximation.HullSC

open GroupApproximation.GGT.VanKampen

universe u w

/-- **The arc-conversion residue, at a supplied letterwise spelling.**  The
planar outer word is `outer`, the algebraic boundary word is `boundaryWord`,
and `outer.map GGT.RelLetter.val = boundaryWord` matches them letter by letter,
so an arc of one is an arc of the other.  Apart from that the statement is
`RelativeExteriorArcConversionStatement`: one planar exterior region, one
algebraic boundary contiguity, an exterior arc no shorter than the planar
source arc. -/
def RelativeExteriorArcConversionAtWordStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, 0} W) (boundaryWord : List G)
    (outer : List (GGT.RelLetter G Lambda)),
    Delta.boundaryWord = outer →
    outer.map GGT.RelLetter.val = boundaryWord →
      ∀ (j : Fin Delta.rCellCount)
        (Gamma : EmbeddedBoundaryContiguity D eps Delta j)
        (relator : List (GGT.RelLetter G Lambda)),
        (GGT.VanKampen.Embedded.cell Delta j).word = relator →
          ∃ C : RelativeBoundaryContiguity D eps boundaryWord relator,
            Gamma.region.sourceArc.length ≤ C.exterior.length

/-- A cyclic source arc becomes a prefix of a rotated relator.  The boundary
rotation is already stored in `RelativeBoundaryContiguity`; this additional
rotation records the independent choice of basepoint on the source cell. -/
def RelativeExteriorArcConversionAtWordRotatedStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, 0} W) (boundaryWord : List G)
    (outer : List (GGT.RelLetter G Lambda)),
    Delta.boundaryWord = outer →
    outer.map GGT.RelLetter.val = boundaryWord →
      ∀ (j : Fin Delta.rCellCount)
        (Gamma : EmbeddedBoundaryContiguity D eps Delta j)
        (relator : List (GGT.RelLetter G Lambda)),
        (GGT.VanKampen.Embedded.cell Delta j).word = relator →
          ∃ n : ℕ, ∃ C : RelativeBoundaryContiguity D eps boundaryWord (relator.rotate n),
            Gamma.region.sourceArc.length ≤ C.exterior.length

end GroupApproximation.HullSC
