import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarInsert
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionVertexSimple
import GroupApproximation.Meta.AxiomGuard

/-!
# The collar insertion from the strip stage

The insertion and the join stages of a collar insertion are proved (`insertStatement`,
`joinStatement`), so the strip stage (`StripStatement`) gives the whole collar insertion.  Let
the boundary darts of a face set form a simple closed walk `s ++ rest`.  An empty side needs no
transport.  Otherwise pass to a strip along `s`: a nonempty word goes in through the strip, and
the empty word of a side of value one joins the side across the strip
(`GeodesicCollar.walkOutput_of_strip`).  The inverse complement cycle of a pocket region
enumerates the boundary darts of its face set, so a simple one gives the collar output
(`GeodesicCollar.geodesicCollarOutput_of_strip_of_simple`), and it is simple once both cycles of
the pocket region follow their boundary walks (`GeodesicCollar.geodesicCollarStatement_of_strip`).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Surgery.MapCollapse SimpleClosedWalkSides

universe u w v

namespace GeodesicCollar

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- A transport keeps the word read on a list of darts. -/
theorem Transport.dartWord_map {D : RelGenSet G Lambda} {Delta Delta' : DiscDiagram.{u, w, v} W}
    {S : Finset Delta.toCombMap.Face} {S' : Finset Delta'.toCombMap.Face}
    (T : Transport D S Delta' S') (l : List Delta.toCombMap.Dart) :
    Embedded.dartWord Delta' (l.map T.embedding) = Embedded.dartWord Delta l := by
  show (l.map T.embedding).map Delta'.label = l.map Delta.label
  refine List.map_map.trans ?_
  exact List.map_congr_left fun d _ => T.label_embedding d

/-- **The collar walk from the strip stage.**  Let the labels of `Δ` be letters of `D`, with
`D.base` closed under inverses, and let the boundary darts of a face set `S` avoiding the exterior
form a simple closed walk `s ++ rest`.  A word `g` in the letters of `D` with the value of `s`,
empty if `s` is, with `g` and `rest` not both empty, gives a collar walk reading `g`. -/
theorem walkOutput_of_strip (hstrip : StripStatement.{u, w, v}) (D : RelGenSet G Lambda)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (Delta : DiscDiagram.{u, w, v} W)
    (hlabel : ∀ d, D.IsLetter (Delta.label d)) (S : Finset Delta.toCombMap.Face)
    (s rest : List Delta.toCombMap.Dart) (hw : IsSimpleClosedWalk Delta.toCombMap (s ++ rest))
    (hboundary : ∀ d, IsBoundaryDart Delta.toCombMap S d ↔ d ∈ s ++ rest)
    (hout : Delta.outerFace ∉ S) (g : List (RelLetter G Lambda))
    (hword : ∀ letter ∈ g, D.IsLetter letter)
    (hval : RelLetter.listVal g = RelLetter.listVal (Embedded.dartWord Delta s))
    (hnil : s = [] → g = []) (hne : g ≠ [] ∨ rest ≠ []) :
    WalkOutput D S rest g := by
  by_cases hs : s = []
  · subst hs
    obtain rfl := hnil rfl
    have hmap : rest.map (Transport.refl D hlabel S).embedding = rest := List.map_id rest
    refine ⟨Delta, S, Transport.refl D hlabel S, [], hout, ?_, ?_, rfl⟩
    · rw [hmap]
      exact hw
    · rw [hmap]
      exact hboundary
  obtain ⟨Delta', S', T, ⟨X⟩⟩ := hstrip D hsymm Delta hlabel S s rest hs hw hboundary hout
  refine WalkOutput.of_transport T ?_
  have hmapval : RelLetter.listVal (Embedded.dartWord Delta' (s.map T.embedding)) =
      RelLetter.listVal (Embedded.dartWord Delta s) :=
    congrArg RelLetter.listVal (T.dartWord_map s)
  by_cases hg : g = []
  · subst hg
    have hr : rest ≠ [] := hne.resolve_left fun h => h rfl
    refine joinStatement D Delta' T.label_isLetter S' _ _ X ?_ ?_
    · exact fun h => hr (List.map_eq_nil_iff.mp h)
    · exact hmapval.trans (hval.symm.trans RelLetter.listVal_nil)
  · exact insertStatement D hsymm Delta' T.label_isLetter S' _ _ X g hg hword
      (hval.trans hmapval.symm)

/-- The inverse complement cycle of a pocket region enumerates the boundary darts of its face
set: it is a cyclic permutation of the pocket's cycle. -/
theorem isBoundaryDart_faces_iff_mem_invDarts_outer {Delta : DiscDiagram.{u, w, v} W}
    (P : PocketRegion Delta) (d : Delta.toCombMap.Dart) :
    IsBoundaryDart Delta.toCombMap P.faces d ↔ d ∈ Embedded.invDarts Delta P.outer.cycle := by
  obtain ⟨k, hk⟩ := P.invDarts_outer_rotate
  rw [hk, List.mem_rotate]
  exact (P.inner.cycle_mem_iff d).symm

/-- **The collar output from the strip stage, over a simple complement walk.**  The hypotheses of
`GeodesicCollarStatement`, with the two `FollowsBoundary` hypotheses replaced by the simplicity of
the inverse complement cycle, give the collar output. -/
theorem geodesicCollarOutput_of_strip_of_simple (hstrip : StripStatement.{u, w, v})
    (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (P : PocketRegion Delta)
    (hw : IsSimpleClosedWalk Delta.toCombMap (Embedded.invDarts Delta P.outer.cycle))
    (s rest : List Delta.toCombMap.Dart)
    (hdecomposition : Embedded.invDarts Delta P.outer.cycle = s ++ rest)
    (g : List (RelLetter G Lambda)) (hword : ∀ letter ∈ g, D.IsLetter letter)
    (hval : RelLetter.listVal g = RelLetter.listVal (Embedded.dartWord Delta s))
    (hnil : s = [] → g = []) (hne : g ≠ [] ∨ rest ≠ []) :
    GeodesicCollarOutput D P rest g := by
  refine geodesicCollarOutput_of_walkOutput D P
    (walkOutput_of_strip hstrip D hsymm Delta hlabel P.faces s rest ?_ ?_ P.outerFace_not_mem g
      hword hval hnil hne)
  · rw [← hdecomposition]
    exact hw
  · intro d
    rw [← hdecomposition]
    exact isBoundaryDart_faces_iff_mem_invDarts_outer P d

/-- **The collar insertion from the strip stage.**  The two `FollowsBoundary` hypotheses make the
inverse complement cycle simple (`PocketRegion.isSimpleClosedWalk_invDarts_outer`). -/
theorem geodesicCollarStatement_of_strip (hstrip : StripStatement.{u, w, v}) :
    GeodesicCollarStatement.{u, w, v} := by
  intro G _ Lambda W D hsymm Delta hlabel P hin hout s rest hdecomposition g hword hval hnil hne
  exact geodesicCollarOutput_of_strip_of_simple hstrip D hsymm Delta hlabel P
    (P.isSimpleClosedWalk_invDarts_outer hin hout) s rest hdecomposition g hword hval hnil hne

end GeodesicCollar

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Transport.dartWord_map
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.walkOutput_of_strip
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.isBoundaryDart_faces_iff_mem_invDarts_outer
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.geodesicCollarOutput_of_strip_of_simple
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.geodesicCollarStatement_of_strip
