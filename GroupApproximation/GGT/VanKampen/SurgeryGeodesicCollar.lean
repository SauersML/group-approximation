import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegion
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.Meta.AxiomGuard

/-!
# A geodesic collar along a side of a pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, whose four sections must be `(λ, c)`-quasi-geodesic.  The side `s_j`
is a side of a contiguity subdiagram, so it is short, but it need not be quasi-geodesic: a spur
`x x⁻¹` has length 2 and distance 0, and `c = 0` is allowed.  So the side is replaced by a
G-face collar.  Pass to an O-equivalent diagram in which a path labelled by a word `g_j` of the
same value as `s_j` runs from the start of `s_j` to its end, and the faces between `s_j` and the
path join the pocket.  The side of the pocket then reads `g_j`, which can be taken geodesic
(`exists_geodesicWord_isLambdaCQuasiGeodesicWord`).

* `GeodesicCollarOutput`: an O-equivalent diagram with a pocket region whose inverse complement
  cycle reads a given word, followed by the image of the rest of the old cycle.
* `GeodesicCollarStatement`: the collar insertion along one side of a pocket region.  It keeps
  its own hypotheses, so it applies again to the other side after the complement cycle is
  restarted with `PocketRegion.withOuter`.
* `geodesicCollarOutput_nil`: an empty side needs no collar.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **The output of a collar insertion.**  For a pocket region `P` of `Δ`, a list `rest` of darts
of `Δ` and a word `g`: an O-equivalent diagram `Δ''` with a pocket region `P''` whose face set
and complement follow their boundary walks, and a path `collar` reading `g`, such that the
inverse complement cycle of `P''` is `collar` followed by the image of `rest`.  The darts of
`Δ` embed into `Δ''` compatibly with `alpha` and the labels, and the labels of `Δ''` are
letters of `D`.  Relator cells outside `P` keep their boundary darts, and every relator cell
stays on its side of the pocket. -/
def GeodesicCollarOutput {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (D : RelGenSet G Lambda)
    {Delta : DiscDiagram.{u, w, v} W} (P : PocketRegion Delta)
    (rest : List Delta.toCombMap.Dart) (g : List (RelLetter G Lambda)) : Prop :=
  ∃ (Delta'' : DiscDiagram.{u, w, v} W) (E : OEquivalentDiscDiagram Delta Delta'')
    (P'' : PocketRegion Delta'') (collar : List Delta''.toCombMap.Dart)
    (ι : Delta.toCombMap.Dart ↪ Delta''.toCombMap.Dart),
    (∀ d, D.IsLetter (Delta''.label d)) ∧
    P''.inner.FollowsBoundary ∧ P''.outer.FollowsBoundary ∧
    Embedded.invDarts Delta'' P''.outer.cycle = collar ++ rest.map ι ∧
    Embedded.dartWord Delta'' collar = g ∧
    (∀ d, Delta''.toCombMap.alpha (ι d) = ι (Delta.toCombMap.alpha d)) ∧
    (∀ d, Delta''.label (ι d) = Delta.label d) ∧
    (∀ i : Fin Delta.rCellCount, (Embedded.cell Delta i).face ∈ P.outside →
      Embedded.cellDarts Delta'' (E.cellIndex i) = (Embedded.cellDarts Delta i).map ι) ∧
    (∀ i : Fin Delta.rCellCount,
      (Embedded.cell Delta'' (E.cellIndex i)).face ∈ P''.faces ↔
        (Embedded.cell Delta i).face ∈ P.faces)

/-- **A geodesic collar along a side of a pocket** (W1 (a), collar insertion).  Let the labels
of `Δ` be letters of `D`, with `D.base` closed under inverses, and let `P` be a pocket region
of `Δ` whose face set and complement follow their boundary walks.  Split the inverse complement
cycle as `s ++ rest`, and take a word `g` in the letters of `D` with the value of the side `s`.
The word is empty if `s` is, and `g` and `rest` are not both empty.  Then the collar output
exists: an O-equivalent diagram whose pocket reads `g` in place of `s`. -/
def GeodesicCollarStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda), (∀ x ∈ D.base, x⁻¹ ∈ D.base) →
    ∀ (Delta : DiscDiagram.{u, w, v} W), (∀ d, D.IsLetter (Delta.label d)) →
    ∀ (P : PocketRegion Delta), P.inner.FollowsBoundary → P.outer.FollowsBoundary →
    ∀ (s rest : List Delta.toCombMap.Dart),
      Embedded.invDarts Delta P.outer.cycle = s ++ rest →
    ∀ (g : List (RelLetter G Lambda)), (∀ letter ∈ g, D.IsLetter letter) →
      RelLetter.listVal g = RelLetter.listVal (Embedded.dartWord Delta s) →
      (s = [] → g = []) → (g ≠ [] ∨ rest ≠ []) →
      GeodesicCollarOutput D P rest g

/-- **An empty side needs no collar**: keep the diagram, the pocket and the darts. -/
theorem geodesicCollarOutput_nil {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (D : RelGenSet G Lambda)
    {Delta : DiscDiagram.{u, w, v} W} (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (P : PocketRegion Delta) (hin : P.inner.FollowsBoundary) (hout : P.outer.FollowsBoundary)
    {rest : List Delta.toCombMap.Dart}
    (hdecomposition : Embedded.invDarts Delta P.outer.cycle = [] ++ rest) :
    GeodesicCollarOutput D P rest [] := by
  refine ⟨Delta, OEquivalentDiscDiagram.refl Delta, P, [], Function.Embedding.refl _, hlabel,
    hin, hout, ?_, rfl, fun _ => rfl, fun _ => rfl, ?_, fun _ => Iff.rfl⟩
  · rw [hdecomposition]
    exact congrArg (fun l => [] ++ l) (List.map_id rest).symm
  · intro i _
    exact (List.map_id _).symm

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.geodesicCollarOutput_nil
