import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralDecidable.PrimrecWords
import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralDecidable.Backward
import Mathlib.Computability.Reduce

/-!
# The literal predicate reduces to real polynomial systems (lane NN02c)

Manuscript: `thm:mf-radical-arithmetic` (non_mf_group_notes.tex), sentence
"This is decidable over the real closed field" (Tarski 1951, Seidenberg 1954).

The translation `literalSystem` of `z = ((c, v), n, d)` into a neutral integer polynomial
system is primitive recursive (`primrec_literalSystem`), and the system has a real solution
iff `D(P,v,n,d)` holds (`literalSystem_holds_iff`). Together these give the computable
many-one reduction `LiteralD ≤₀ PolySystem.Holds` (`literalD_manyOneReducible`).
-/

namespace GroupApproximation.Full.NN02c

/-- Codes `((c, v), n, d)` of instances of the literal predicate. -/
abbrev LitCode : Type := ((ℕ × List (List (ℕ × Bool))) × List (ℕ × Bool)) × ℕ × ℕ

theorem primrec_encodeC : Primrec encodeC := by
  show Primrec fun z : LitCode =>
    ((unitaryCons (z.1.1.1 + 1) z.2.2 ++
        (z.1.1.2.flatMap (relatorCons (z.1.1.1 + 1) z.2.2 (scale z.2.1)) ++
          vCons (z.1.1.1 + 1) z.2.2 z.1.2),
      [vNonneg z.2.2]) : CSystem)
  have hG : Primrec fun z : LitCode => z.1.1.1 + 1 :=
    Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 1)
  have hD : Primrec fun z : LitCode => z.2.2 := Primrec.snd.comp Primrec.snd
  have hS : Primrec fun z : LitCode => scale z.2.1 :=
    primrec_scale.comp (Primrec.fst.comp Primrec.snd)
  have hc : Primrec fun z : LitCode => z.1.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hv : Primrec fun z : LitCode => z.1.2 := Primrec.snd.comp Primrec.fst
  have hrel : Primrec₂ fun (z : LitCode) (r : List (ℕ × Bool)) =>
      relatorCons (z.1.1.1 + 1) z.2.2 (scale z.2.1) r :=
    primrec_relatorCons (hG.comp Primrec.fst) (hD.comp Primrec.fst) (hS.comp Primrec.fst)
      Primrec.snd
  exact Primrec.pair
    (Primrec.list_append.comp (primrec_unitaryCons hG hD)
      (Primrec.list_append.comp (Primrec.list_flatMap hc hrel) (primrec_vCons hG hD hv)))
    (Primrec.list_cons.comp (primrec_vNonneg hD) (Primrec.const []))

/-- The polynomial system of the literal predicate is a primitive recursive function of
the code `((c, v), n, d)`. -/
theorem primrec_literalSystem : Primrec literalSystem := by
  show Primrec fun z : LitCode => compileSystem (encodeC z)
  exact primrec_compileSystem primrec_encodeC

/-- **`D(P,v,n,d)` many-one reduces to real solvability of polynomial systems**
(`thm:mf-radical-arithmetic`, "This is decidable over the real closed field"). -/
theorem literalD_manyOneReducible :
    (fun z : (PresentationCodes.PresentationCode × List (ℕ × Bool)) × ℕ × ℕ =>
      NN02b.LiteralD z.1.1 z.1.2 z.2.1 z.2.2) ≤₀ PolySystem.Holds :=
  ⟨literalSystem, primrec_literalSystem.to_comp, fun z => (literalSystem_holds_iff z).symm⟩

end GroupApproximation.Full.NN02c
