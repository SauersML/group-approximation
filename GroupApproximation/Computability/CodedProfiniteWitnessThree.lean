import GroupApproximation.Computability.CodedProfiniteWitness
import GroupApproximation.Computability.BenignComapThreeCode

/-!
# Three-mark coded profinite witnesses

TransportStar's internal operation tree uses six marks, but its final split
preimage deliberately retains only three.  This is the exact finite contract
consumed by `MikhailovaRopeCode.rankThreeData`; it avoids padding dead marks
back into the six-mark operation model.
-/

namespace GroupApproximation
namespace CodedProfiniteWitness

noncomputable section

open PresentationCodes BenignInfCode
open BenignInfCodeSemantics BenignInfCodeSubgroupSemantics

abbrev MarkCountThree := Fin 3

/-- A three-mark finite-presentation model of a strengthened benign witness. -/
structure ModelThree {G : Type} [Group G] (mark : MarkCountThree → G)
    (H : Subgroup G) where
  data : Higman.ProfiniteBenignWitness H
  coded : PresentationCode × (List BenignInfCode.Raw ×
    (BenignInfCode.Raw × BenignInfCode.Raw × BenignInfCode.Raw))
  ambientEquiv : Carrier coded.1 ≃* data.witness.K
  cutter_eq :
    (wordSubgroup coded.1 coded.2.1).map ambientEquiv.toMonoidHom =
      data.witness.L
  marked_eq :
    ambientEquiv (evalWord coded.1 coded.2.2.1) = data.witness.emb (mark 0) ∧
    ambientEquiv (evalWord coded.1 coded.2.2.2.1) = data.witness.emb (mark 1) ∧
    ambientEquiv (evalWord coded.1 coded.2.2.2.2) = data.witness.emb (mark 2)

/-- A three-mark coded profinitely full overgroup. -/
structure OvergroupModelThree {G : Type} [Group G]
    (mark : MarkCountThree → G) (u : Higman.ProfiniteFPOvergroup G) where
  code : PresentationCode
  marks : BenignInfCode.Raw × BenignInfCode.Raw × BenignInfCode.Raw
  ambientEquiv : Carrier code ≃* u.overgroup.K
  marked_eq :
    ambientEquiv (evalWord code marks.1) = u.overgroup.emb (mark 0) ∧
    ambientEquiv (evalWord code marks.2.1) = u.overgroup.emb (mark 1) ∧
    ambientEquiv (evalWord code marks.2.2) = u.overgroup.emb (mark 2)

namespace ModelThree

variable {G N : Type} [Group G] [Group N]
variable {mark : MarkCountThree → G} {H : Subgroup N}

private def marksList
    (w : BenignInfCode.Raw × BenignInfCode.Raw × BenignInfCode.Raw) :
    List BenignInfCode.Raw := [w.1, w.2.1, w.2.2]

/-- Exact code-level preimage constructor for the final three TransportStar
marks.  Its syntax is literally `BenignComapThreeCode.transform`. -/
def comap (u : Higman.ProfiniteFPOvergroup G) (phi : G →* N)
    (A : OvergroupModelThree mark u)
    (C : ModelThree (fun i ↦ phi (mark i)) H) :
    ModelThree mark (H.comap phi) where
  data := Higman.ProfiniteBenignWitness.comap u phi C.data
  coded :=
    let out := BenignComapThreeCode.transform
      ((A.code, ([], marksList A.marks)),
        (C.coded.1, (C.coded.2.1,
          [C.coded.2.2.1, C.coded.2.2.2.1, C.coded.2.2.2.2])))
    (out.1, (out.2.1,
      (out.2.2.getD 0 [], out.2.2.getD 1 [], out.2.2.getD 2 [])))
  ambientEquiv := by
    change Carrier (DirectProductCode.productCode A.code C.coded.1) ≃*
      (u.overgroup.K × C.data.witness.K)
    exact
      (DirectProductCodeSemantics.productCodeEquiv A.code C.coded.1).trans
        (Model.prodEquiv A.ambientEquiv C.ambientEquiv)
  cutter_eq := by
    let x : BenignInfCode.Input :=
      ((A.code, ([], marksList A.marks)),
        (C.coded.1, (C.coded.2.1,
          [C.coded.2.2.1, C.coded.2.2.2.1, C.coded.2.2.2.2])))
    change
      (wordSubgroup (BenignComapThreeCode.transform x).1
        (BenignComapThreeCode.transform x).2.1).map
          ((Model.prodEquiv A.ambientEquiv C.ambientEquiv).toMonoidHom.comp
            (DirectProductCodeSemantics.productCodeEquiv
              A.code C.coded.1).toMonoidHom) =
        (⊤ : Subgroup u.overgroup.K).prod C.data.witness.L
    rw [← Subgroup.map_map]
    calc
      ((wordSubgroup (BenignComapThreeCode.transform x).1
          (BenignComapThreeCode.transform x).2.1).map
          (DirectProductCodeSemantics.productCodeEquiv
            A.code C.coded.1).toMonoidHom).map
            (Model.prodEquiv A.ambientEquiv C.ambientEquiv).toMonoidHom =
        ((⊤ : Subgroup (Carrier A.code)).prod
          (wordSubgroup C.coded.1 C.coded.2.1)).map
            (Model.prodEquiv A.ambientEquiv C.ambientEquiv).toMonoidHom := by
          exact congrArg
            (fun S ↦ S.map
              (Model.prodEquiv A.ambientEquiv C.ambientEquiv).toMonoidHom)
            (Model.map_wordSubgroup_comap_cutting x)
      _ = _ := by
        rw [Model.map_prodEquiv,
          Subgroup.map_top_of_surjective _ A.ambientEquiv.surjective,
          C.cutter_eq]
  marked_eq := by
    let x : BenignInfCode.Input :=
      ((A.code, ([], marksList A.marks)),
        (C.coded.1, (C.coded.2.1,
          [C.coded.2.2.1, C.coded.2.2.2.1, C.coded.2.2.2.2])))
    have hmark (i : Fin 3) :
        (Model.prodEquiv A.ambientEquiv C.ambientEquiv)
          (DirectProductCodeSemantics.productCodeEquiv A.code C.coded.1
            (evalWord (BenignComapThreeCode.transform x).1
              ((BenignComapThreeCode.diagonalMarks x).getD i []))) =
          ((Higman.ProfiniteBenignWitness.comap u phi C.data).witness.emb
            (mark i)) := by
      have hdiag :=
        BenignComapCodeSemantics.productCodeEquiv_threeMark x i
      have hword :
          (BenignComapThreeCode.diagonalMarks x).getD i [] =
            BenignInfCode.diagonalAt x i := by
        fin_cases i <;> rfl
      rw [hword]
      change
        (Model.prodEquiv A.ambientEquiv C.ambientEquiv)
          (DirectProductCodeSemantics.productCodeEquiv
            (BenignInfCode.leftCode x) (BenignInfCode.rightCode x)
            (evalWord (BenignComapThreeCode.transform x).1
              (BenignInfCode.diagonalAt x i))) = _
      rw [hdiag]
      change
        (A.ambientEquiv (evalWord A.code ((marksList A.marks).getD i [])),
          C.ambientEquiv
            (evalWord C.coded.1
              ([C.coded.2.2.1, C.coded.2.2.2.1,
                C.coded.2.2.2.2].getD i []))) = _
      fin_cases i
      · exact Prod.ext A.marked_eq.1 C.marked_eq.1
      · exact Prod.ext A.marked_eq.2.1 C.marked_eq.2.1
      · exact Prod.ext A.marked_eq.2.2 C.marked_eq.2.2
    exact ⟨hmark 0, hmark 1, hmark 2⟩

end ModelThree

end

end CodedProfiniteWitness
end GroupApproximation
