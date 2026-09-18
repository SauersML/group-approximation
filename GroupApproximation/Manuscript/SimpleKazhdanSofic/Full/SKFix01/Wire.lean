import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKFix01.CohnK2
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVWire.Chain
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVWire.CohnStatement
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVWire.LeavittStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Every `LVWire` row from the degree-zero residual (lane sk-fix-01)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  The `LVWire` rows
(`Full/LVWire/{Chain,CohnStatement,LeavittStatement}.lean`) take the single hypothesis
`hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit`.  Here each row is instantiated at
`hD := skFix01_cohnLimit_stableK2Trivial h`
(`= LVCohnColimit.skCohnLimK2_stableK2Trivial_of_degreeZeroSurj h`), so every row depends only
on `h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement`.

Rows (13; the two `hD`-free bridges `skLVWire_cohnRel_eq`, `skLVWire_stableK2Trivial_ringQuot_congr`
of `CohnStatement.lean` are unconditional and need no rewiring):
Chain #2-#9, the whole sentence and its first clause; CohnStatement #2 for `CohnTwo (ZMod 2)` and
its registered form; LeavittStatement #3 registered form.

Truth of `h`: see `SKFix01/CohnK2.lean` (true; LOUD: equivalent to stable `K₂(C_2(𝔽₂)) = 0`).
This module is wiring only.
-/

namespace GroupApproximation.Full.SKFix01

/-- **Row #2**: stable `K₂(C_2(𝔽₂)) = 0`, from `h` (ABC 2009, Thm 3.6; tex l.733-735). -/
theorem skFix01_wire_cohnStableK2 (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    LVH2GL3.StableK2Trivial LVCohnRelK1.CohnTwoF2 :=
  LVWire.skLVWire_cohnStableK2_of_cohnLimit (skFix01_cohnLimit_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_wire_cohnStableK2

/-- **Row #3**: stable `K₂(L_{𝔽₂}(1,2)) = 0`, from `h` (tex l.733-735). -/
theorem skFix01_wire_leavittStableK2 (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    LVH2GL3.StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :=
  LVWire.skLVWire_leavittStableK2_of_cohnLimit (skFix01_cohnLimit_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_wire_leavittStableK2

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- **Row #4**: `L_{𝔽₂}(1,2)ˣ` is superperfect, from `h` (Khanh, Thm 2.2; tex l.733-735). -/
theorem skFix01_wire_unitsSuperperfect (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement :=
  LVWire.skLVWire_unitsSuperperfect_of_cohnLimit (skFix01_cohnLimit_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_wire_unitsSuperperfect

/-- **Row #5**: `K₂(4, L_{𝔽₂}(1,2)) = ⊥`, from `h` (Khanh, Thm 5.1; tex l.733-735). -/
theorem skFix01_wire_rankFourInjective (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement :=
  LVWire.skLVWire_rankFourInjective_of_cohnLimit (skFix01_cohnLimit_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_wire_rankFourInjective

/-- **Row #6**: `K₂(5, L_{𝔽₂}(1,2)) = ⊥`, from `h` (Khanh, Thm 5.4; tex l.733-735). -/
theorem skFix01_wire_steinbergInjective
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergInjectiveStatement :=
  LVWire.skLVWire_steinbergInjective_of_cohnLimit (skFix01_cohnLimit_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_wire_steinbergInjective

open GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan in
/-- **Row #7**: `EL_5(L_{𝔽₂}(1,2))` is finitely presented, from `h` (Khanh, Thm 5.4 and
Lemma 5.3; tex l.733-735). -/
theorem skFix01_wire_elementaryFP (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    BinaryLeavittElementaryFinitelyPresentedStatement :=
  LVWire.skLVWire_elementaryFP_of_cohnLimit (skFix01_cohnLimit_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_wire_elementaryFP

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- **Row #8**: the padding `St_3(L) → St_4(L)` kills `K₂(3, L)`, from `h` (Khanh, Thm 2.2;
tex l.733-735). -/
theorem skFix01_wire_stabKernelThreeTrivial
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement :=
  LVWire.skLVWire_stabKernelThreeTrivial_of_cohnLimit (skFix01_cohnLimit_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_wire_stabKernelThreeTrivial

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- **Row #9**: the interface `#8 → #5`, from `h` (tex l.733-735). -/
theorem skFix01_wire_rankFourOfStabKernelThree
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement :=
  LVWire.skLVWire_rankFourOfStabKernelThree_of_cohnLimit (skFix01_cohnLimit_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_wire_rankFourOfStabKernelThree

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- **CohnStatement row**: stable `K₂(LeavittK2.CohnTwo (ZMod 2)) = 0`, from `h`
(ABC 2009, Thm 3.6; tex l.733-735). -/
theorem skFix01_wire_cohnTwoStableK2 (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    LVH2GL3.StableK2Trivial (CohnTwo (ZMod 2)) :=
  LVWire.skLVWire_cohnTwoStableK2_of_cohnLimit (skFix01_cohnLimit_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_wire_cohnTwoStableK2

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- **CohnStatement row, registered form**: `LeavittK2.BinaryCohnStableK2TrivialStatement`,
from `h` (tex l.733-735). -/
theorem skFix01_wire_binaryCohnStatement
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    BinaryCohnStableK2TrivialStatement :=
  LVWire.skLVWire_binaryCohnStatement_of_cohnLimit (skFix01_cohnLimit_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_wire_binaryCohnStatement

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- **LeavittStatement row, registered form**: `LeavittK2.BinaryLeavittStableK2TrivialStatement`,
from `h` (ABC 2009; tex l.733-735). -/
theorem skFix01_wire_binaryLeavittStatement
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    BinaryLeavittStableK2TrivialStatement :=
  LVWire.skLVWire_binaryLeavittStatement_of_cohnLimit (skFix01_cohnLimit_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_wire_binaryLeavittStatement

end GroupApproximation.Full.SKFix01
