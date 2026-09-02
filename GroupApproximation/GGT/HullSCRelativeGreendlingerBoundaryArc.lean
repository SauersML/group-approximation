import GroupApproximation.GGT.HullSCRelativeGreendlingerPowerBoundary

/-!
# Linearizing the outer boundary arc

`RelativeBoundaryContiguity.boundary_decomposition` asks for a **linear**
decomposition

```lean
  boundaryWord = boundaryBefore ++ boundaryArc ++ boundaryAfter
```

of the designated boundary word, while the planar side supplies a **cyclic**
arc: with `Gamma.target = none`,
`GGT.VanKampen.Embedded.targetBoundaryDarts Delta none Gamma.targetArc` is
`Gamma.targetArc.darts`, a `CyclicArc` of `outerDarts Delta`, and
`CyclicArc.darts` is `rotated.take length` with
`rotated = cycle.drop start ++ cycle.take start`.

The two agree exactly when the arc does not wrap the cut, which is
`arc.start + arc.length ≤ cycle.length`.  This module proves that case
outright, transports it through `dartWord` and `GGT.RelLetter.val` to the
`List G` boundary word, and names the wrap-freeness as the one residual
clause.

Weakening the certificate instead is not available: unlike
`cellLabel_eq`, which no consumer reads and which therefore became
`cellLabel_rotate`, `RelativeDiagramCertificate.boundaryWord_eq` **is** read,
at `HullSCLemma44CertificateInjectivity`, `HullSCLemma44WeightedArea`,
`HullSCLemma44PrefixCutRatio`, `HullSCLemma44NormalPolygon`,
`HullSCLemma44RelativeBoundary`, `HullSCLemma44RelativeDehn` and
`HullSCLemma49FromRelativeGreendlinger`.  And a cyclic boundary decomposition
would change `boundaryArc.prod` by a conjugation, which
`RelativeBoundaryContiguity.exterior_value` reads directly.

Every declaration below is a complete proof or a named proposition; no
placeholder of any kind is introduced here.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT.VanKampen

universe u w

/-! ## Wrap-free cyclic arcs -/

/-- **A cyclic arc that does not wrap the cut.**  The start position plus the
length stays inside the cycle. -/
def Embedded.CyclicArc.IsLinear {Dart : Type} {cycle : List Dart}
    (arc : Embedded.CyclicArc cycle) : Prop :=
  arc.start.1 + arc.length ≤ cycle.length

/-- A wrap-free arc reads a genuine contiguous block of its cycle. -/
theorem Embedded.CyclicArc.darts_eq_take_drop_of_isLinear
    {Dart : Type} {cycle : List Dart}
    (arc : Embedded.CyclicArc cycle) (h : arc.IsLinear) :
    arc.darts = (cycle.drop arc.start.1).take arc.length := by
  have hlen : arc.length ≤ (cycle.drop arc.start.1).length := by
    rw [List.length_drop]
    omega
  rw [Embedded.CyclicArc.darts, Embedded.CyclicArc.rotated]
  exact List.take_append_of_le_length hlen

/-- **The linear decomposition of a cycle at a wrap-free arc.** -/
theorem Embedded.CyclicArc.cycle_decomposition_of_isLinear
    {Dart : Type} {cycle : List Dart}
    (arc : Embedded.CyclicArc cycle) (h : arc.IsLinear) :
    cycle =
      cycle.take arc.start.1 ++ arc.darts ++
        cycle.drop (arc.start.1 + arc.length) := by
  rw [arc.darts_eq_take_drop_of_isLinear h]
  rw [List.append_assoc]
  rw [← List.drop_drop]
  rw [List.take_append_drop, List.take_append_drop]

/-! ## Transport to the designated boundary word -/

/-- **The designated boundary word decomposes at a wrap-free outer arc.**

The planar cycle is `outerDarts Delta`, whose dart word is
`Delta.boundaryWord` by `GGT.VanKampen.Embedded.dartWord_outerDarts`, and the
designated boundary word is that word's letter values.  So a wrap-free arc of
the planar cycle gives exactly the three `List G` blocks that
`RelativeBoundaryContiguity.boundary_decomposition` asks for. -/
theorem boundaryWord_decomposition_of_isLinear
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, 0} W}
    (arc : Embedded.CyclicArc (Embedded.outerDarts Delta))
    (harc : arc.IsLinear)
    (boundaryWord : List G)
    (hword : Delta.boundaryWord.map GGT.RelLetter.val = boundaryWord) :
    boundaryWord =
      ((Embedded.dartWord Delta
          ((Embedded.outerDarts Delta).take arc.start.1)).map
            GGT.RelLetter.val) ++
      ((Embedded.dartWord Delta arc.darts).map GGT.RelLetter.val) ++
      ((Embedded.dartWord Delta
          ((Embedded.outerDarts Delta).drop
            (arc.start.1 + arc.length))).map GGT.RelLetter.val) := by
  have hcycle := arc.cycle_decomposition_of_isLinear harc
  have hdart : Embedded.dartWord Delta (Embedded.outerDarts Delta) =
      Delta.boundaryWord := Embedded.dartWord_outerDarts Delta
  calc boundaryWord
      = (Embedded.dartWord Delta (Embedded.outerDarts Delta)).map
          GGT.RelLetter.val := by rw [hdart, hword]
    _ = _ := by
        conv_lhs => rw [hcycle]
        simp only [Embedded.dartWord, List.map_append]

/-- The arc block of that decomposition has the arc's length. -/
theorem boundaryArc_length_eq_of_isLinear
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, 0} W}
    (arc : Embedded.CyclicArc (Embedded.outerDarts Delta)) :
    ((Embedded.dartWord Delta arc.darts).map GGT.RelLetter.val).length
      = arc.length := by
  simp only [List.length_map, Embedded.dartWord]
  exact arc.darts_length

/-! ## The residual clause -/

/-- **The one clause the boundary linearization still needs.**

Every exterior region selected by the estimating construction may be taken
with a wrap-free outer arc.  Geometrically this is a choice of where the outer
boundary cycle is cut, and the planar construction is free to make it: the cut
is `GGT.VanKampen.DiscDiagram.faceBoundary Delta.outerFace`'s starting dart,
which no clause of `DiscDiagram` pins.

Given it, `boundaryWord_decomposition_of_isLinear` supplies
`RelativeBoundaryContiguity.boundary_decomposition` outright, and
`boundaryArc_length_eq_of_isLinear` supplies the length bookkeeping.  Together
with `Contiguity.arcs_value_of_pasting` for `exterior_value` and
`exists_admissible_sides_of_contiguity` for the two sides, the only remaining
input of the exterior-arc conversion is the pasting homotopy itself. -/
def ContiguityBoundaryArcLinearStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, 0} W)
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Embedded.Contiguity D eps Delta faces)
    (htarget : Gamma.target = none),
    ∃ arc : Embedded.CyclicArc (Embedded.outerDarts Delta),
      arc.IsLinear ∧
        Embedded.dartWord Delta arc.darts =
          Embedded.dartWord Delta
            (Embedded.targetBoundaryDarts Delta Gamma.target Gamma.targetArc)

/-! ## Model checks -/

/-- An arc based at the start of its cycle is wrap-free. -/
theorem Embedded.CyclicArc.isLinear_of_start_zero
    {Dart : Type} {cycle : List Dart}
    (arc : Embedded.CyclicArc cycle) (h : arc.start.1 = 0) :
    arc.IsLinear := by
  rw [Embedded.CyclicArc.IsLinear, h, Nat.zero_add]
  exact arc.length_le

/-- An arc of length zero is wrap-free, whatever its base point. -/
theorem Embedded.CyclicArc.isLinear_of_length_zero
    {Dart : Type} {cycle : List Dart}
    (arc : Embedded.CyclicArc cycle) (h : arc.length = 0) :
    arc.IsLinear := by
  rw [Embedded.CyclicArc.IsLinear, h, Nat.add_zero]
  omega

end HullSC
end GroupApproximation
