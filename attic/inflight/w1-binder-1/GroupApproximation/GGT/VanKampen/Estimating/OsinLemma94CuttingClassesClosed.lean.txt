import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingClasses
import GroupApproximation.GGT.VanKampen.CombMapSameFaceForest
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4, (38): the cutting sides and cutting classes, closed

Osin (math/0411039v3, §9), proof of Lemma 9.4, (38): "`k_i ≤ 4 n_i`", for the cutting sides and
the cutting classes.  The only planarity input of the count, `SameFaceDartForestStatement`, is
proved as `sameFaceDartForest`.  Plugging it in leaves only the ordinary hypotheses of the
count: a dart-minimal family and maximal sides.

* `OsinLemma94RealizedPolygons.card_cuttingSides_le_of_dartMinimal`: per polygon,
  `#cutting sides ≤ 4 · #entries + 1`.
* `OsinLemma94ClassPolygons.card_cuttingClasses_le_of_dartMinimal`: per polygon and any class
  polygons, `#cutting classes ≤ 4 · #other classes + 1`.
* `osinLemma94CuttingSides_closed`, `osinLemma94CuttingClasses_closed`: the named Props, closed.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, through Osin's Lemma 9.4 inside
the proof of Lemma 4.4).  It pays the cutting classes of `OsinLemma94ClassPolygons.ClassBudget`;
it certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

namespace OsinLemma94RealizedPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **(38), the cutting half.**  For a dart-minimal family with maximal sides, polygon `k` has
at most `4 e + 1` cutting sides, where `e` counts its entries. -/
theorem card_cuttingSides_le_of_dartMinimal (hS : S.DartMinimal)
    (P : OsinLemma94RealizedPolygons S) (hmax : P.Maximal) (k : Fin P.count) :
    (P.cuttingSides k).card ≤ 4 * (P.cuttingEntries k).card + 1 :=
  P.card_cuttingSides_le sameFaceDartForest hS hmax k

end OsinLemma94RealizedPolygons

namespace OsinLemma94ClassPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **(38), the cutting classes.**  For a dart-minimal family with maximal sides and any class
polygons, polygon `k` has at most `4 m + 1` cutting classes, where `m` counts its other
classes. -/
theorem card_cuttingClasses_le_of_dartMinimal (hS : S.DartMinimal) (hmax : P.Maximal)
    (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    (Q.cuttingClasses k).card ≤ 4 * (Q.otherClasses k).card + 1 :=
  Q.card_cuttingClasses_le_otherClasses sameFaceDartForest hS hmax k

end OsinLemma94ClassPolygons

/-- **(38), the cutting half, closed.** -/
theorem osinLemma94CuttingSides_closed : OsinLemma94CuttingSidesStatement.{u, w, v} :=
  osinLemma94CuttingSides_of_forest sameFaceDartForest

/-- **(38), the cutting classes, closed.** -/
theorem osinLemma94CuttingClasses_closed : OsinLemma94CuttingClassesStatement.{u, w, v} :=
  osinLemma94CuttingClasses_of_forest sameFaceDartForest

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.card_cuttingSides_le_of_dartMinimal
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.card_cuttingClasses_le_of_dartMinimal
#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94CuttingSides_closed
#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94CuttingClasses_closed
