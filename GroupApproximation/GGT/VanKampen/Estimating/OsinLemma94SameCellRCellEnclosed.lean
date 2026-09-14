import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellRCellAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# The relator-cell branch of the one-cell pairs of Lemma 9.4, Case 1, split on spurs first

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, for a backwards connector pair whose source and
target sides lie across one relator cell `Π` (`OsinLemma94CaseOneSameCellStatement`).  Some
rotation of the face walk reads `X q⁻¹ Y p⁻¹`, some rotation of the carrier of `Π` reads `q B p A`,
and in the relator-cell branch (`OsinLemma94CaseOneRCellStatement`) neither `X B` nor `Y A` reads
`1`.  The pocket walks are `invDarts X ++ invDarts B` and `invDarts Y ++ invDarts A`.

* `osinLemma94CaseOneRCell_of_noSpurPockets`: split on a spur first.  With a spur on a pocket walk,
  the spur branch (`OsinLemma94CaseOneRCellSpurStatement`) refutes the pair.  Without one, both walks
  are noncrossing (`SameCellPocketNoncrossing.pocketInputs_X` and `_Y`), the exterior face is off one
  side (`SameCellPocketSides.not_mem_sideFaces_or`), and the spur-free X- or Y-pocket statement
  refutes the pair.
* `osinLemma94CaseOneSameCell_of_noSpurPockets`: binder 3, `OsinLemma94CaseOneSameCellStatement`,
  through the value-one kills of `osinLemma94CaseOneSameCell_of_rCell`.
* `osinLemma94CaseOneSpur_of_rCellSpur`: the spur shape of the X-pocket
  (`OsinLemma94CaseOneSpurStatement`) from the spur branch, through the value-one kill when `Y A`
  reads `1`.
* `SameCellRCellEnclosed.listVal_invDarts_append_ne_one`: the reversed complement spelling of a
  pocket walk reads an element other than `1`.

Residual statements of `osinLemma94CaseOneSameCell_of_noSpurPockets`: the spur-free X- and Y-pocket
statements (ms-intro-1, over the enclosed loop cut) and the spur branch (this lane).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

namespace SameCellRCellEnclosed

/-- **The reversed complement spelling reads an element other than `1`**, when the pocket spelling
does, in either order of its two parts. -/
theorem listVal_invDarts_append_ne_one {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
    {l₁ l₂ : List Delta.toCombMap.Dart}
    (h : RelLetter.listVal (dartWord Delta (l₁ ++ l₂)) ≠ 1) :
    RelLetter.listVal (dartWord Delta (invDarts Delta (l₂ ++ l₁))) ≠ 1 := by
  have happ : ∀ m₁ m₂ : List Delta.toCombMap.Dart,
      RelLetter.listVal (dartWord Delta (m₁ ++ m₂)) =
        RelLetter.listVal (dartWord Delta m₁) * RelLetter.listVal (dartWord Delta m₂) := by
    intro m₁ m₂
    simp [Embedded.dartWord, RelLetter.listVal]
  rw [listVal_dartWord_invDarts, happ]
  intro hone
  apply h
  rw [happ]
  exact mul_eq_one_comm.mp (inv_eq_one.mp hone)

end SameCellRCellEnclosed

open SameCellRCellAssembly in
/-- **The relator-cell branch, split on spurs first.**  With a spur on a pocket walk the spur
branch refutes the pair.  Without one, both pocket walks are noncrossing, the exterior face is off
the side of one of them, and the spur-free pocket statement of that side refutes the pair. -/
theorem osinLemma94CaseOneRCell_of_noSpurPockets
    (hx : OsinLemma94CaseOneXPocketStatementOf.{u, w, v}
      (fun Delta x b => ¬ PocketWalkSpurShape Delta x b))
    (hy : OsinLemma94CaseOneYPocketStatementOf.{u, w, v}
      (fun Delta x b => ¬ PocketWalkSpurShape Delta x b))
    (hspur : OsinLemma94CaseOneRCellSpurStatement.{u, w, v}) :
    OsinLemma94CaseOneRCellStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e1, he1⟩ := hx D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e2, he2⟩ := hy D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e3, he3⟩ := hspur D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨max e1 (max e2 e3), fun eps heps => ?_⟩
  obtain ⟨r1, hr1, h1⟩ := he1 eps (by omega)
  obtain ⟨r2, hr2, h2⟩ := he2 eps (by omega)
  obtain ⟨r3, hr3, h3⟩ := he3 eps (by omega)
  refine ⟨max r1 (max r2 r3), by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut hkind j sourceArc
    targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB hYA
  by_cases hsp : (∃ d ∈ invDarts S.diagram X ++ invDarts S.diagram B,
        S.diagram.toCombMap.alpha d ∈ invDarts S.diagram X ++ invDarts S.diagram B) ∨
      ∃ d ∈ invDarts S.diagram Y ++ invDarts S.diagram A,
        S.diagram.toCombMap.alpha d ∈ invDarts S.diagram Y ++ invDarts S.diagram A
  · exact h3 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
      hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB hYA hsp
  have hsp₁ : ∀ d ∈ invDarts S.diagram X ++ invDarts S.diagram B,
      S.diagram.toCombMap.alpha d ∉ invDarts S.diagram X ++ invDarts S.diagram B :=
    fun d hd had => hsp (Or.inl ⟨d, hd, had⟩)
  have hsp₂ : ∀ d ∈ invDarts S.diagram Y ++ invDarts S.diagram A,
      S.diagram.toCombMap.alpha d ∉ invDarts S.diagram Y ++ invDarts S.diagram A :=
    fun d hd had => hsp (Or.inr ⟨d, hd, had⟩)
  obtain ⟨hw₁, -, -⟩ := SameCellPocketNoncrossing.pocketInputs_X (P.face_not_cell k j) sourceArc
    targetArc htrav hPi hs ht (append_ne_nil_of_listVal_ne_one hXB) hsp₁
  obtain ⟨hw₂, -, -⟩ := SameCellPocketNoncrossing.pocketInputs_Y (P.face_not_cell k j) sourceArc
    targetArc htrav hPi hs ht (append_ne_nil_of_listVal_ne_one hYA) hsp₂
  rcases SameCellPocketSides.not_mem_sideFaces_or (P.face_not_cell k j) sourceArc targetArc htrav
      hPi hs hw₁ hw₂ S.diagram.outerFace with hout | hout
  · exact h1 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
      hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB hout
      fun ⟨d, hd, had⟩ => hsp₁ d hd had
  · exact h2 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
      hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hYA hout
      fun ⟨d, hd, had⟩ => hsp₂ d hd had

/-- **Binder 3, split on spurs first**: the spur-free pockets and the spur branch. -/
theorem osinLemma94CaseOneSameCell_of_noSpurPockets
    (hx : OsinLemma94CaseOneXPocketStatementOf.{u, w, v}
      (fun Delta x b => ¬ PocketWalkSpurShape Delta x b))
    (hy : OsinLemma94CaseOneYPocketStatementOf.{u, w, v}
      (fun Delta x b => ¬ PocketWalkSpurShape Delta x b))
    (hspur : OsinLemma94CaseOneRCellSpurStatement.{u, w, v}) :
    OsinLemma94CaseOneSameCellStatement.{u, w, v} :=
  osinLemma94CaseOneSameCell_of_rCell (osinLemma94CaseOneRCell_of_noSpurPockets hx hy hspur)

/-- **The spur shape of the X-pocket from the spur branch.**  If `Y A` reads `1` the value-one kill
refutes the pair; otherwise the spur branch does. -/
theorem osinLemma94CaseOneSpur_of_rCellSpur
    (hrspur : OsinLemma94CaseOneRCellSpurStatement.{u, w, v}) :
    OsinLemma94CaseOneSpurStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨kappa, hmorse, eps1, heps1⟩ :=
    exists_morse_threshold_of_fourPoint D hhyper lambda c hlambda
  obtain ⟨eps2, heps2⟩ := hrspur D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨max eps1 eps2, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps2 eps (le_of_max_le_right heps)
  refine ⟨rho0, hrho0, fun rho hrho' => ?_⟩
  intro W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut hkind j sourceArc
    targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB _hout hsp
  by_cases hYA : RelLetter.listVal (dartWord S.diagram (Y ++ A)) = 1
  · obtain ⟨T, hT⟩ := CaseOneSameCell.exists_arc_darts_eq_rotate_four hPi
    exact false_of_sameCell_value_one_Y hW hlambda.le hmorse (heps1 eps (le_of_max_le_left heps))
      P k C sourceArc targetArc htrav hsource htarget hX T hT hYA
  · exact hrho rho hrho' W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
      hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB hYA
      (Or.inl hsp)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SameCellRCellEnclosed.listVal_invDarts_append_ne_one
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneRCell_of_noSpurPockets
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneSameCell_of_noSpurPockets
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneSpur_of_rCellSpur
