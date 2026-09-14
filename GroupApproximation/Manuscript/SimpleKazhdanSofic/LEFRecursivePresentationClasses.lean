import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterization
import GroupApproximation.Higman.RecursivePresentationBridge
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Computability.PartrecCode
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# There are countably many recursive presentations

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602, proof of `cor:host` (tex l.435–436):

> There are countably many recursive presentations.

A recursively presented group is presented by the kernel of its evaluation map
(`Higman.presentedGroupEquiv`). Membership of a reduced word in that kernel is recursively
enumerable, so it is the domain of some program `c`. The group is therefore isomorphic to
`CodeGroup c`, the group presented by the reduced words on which `c` halts, and there are countably
many programs.

* `codeRels c` and `CodeGroup c`: the relators and the group coded by a program.
* `exists_code_dom_iff`: an r.e. predicate on raw words is the domain of a program.
* `recursivePresentationClassesStatement : RecursivePresentationClassesStatement`: the piece consumed
  by `printedRecursivelyPresentedLEFHost_of_pieces`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-- The relators coded by a program `c`: the reduced words on which `c` halts. -/
def codeRels (c : Nat.Partrec.Code) : Set (FreeGroup ℕ) :=
  {x | (Nat.Partrec.Code.eval c (Encodable.encode (FreeGroup.toWord x))).Dom}

/-- The group presented by the relators coded by `c`. -/
abbrev CodeGroup (c : Nat.Partrec.Code) : Type :=
  PresentedGroup (codeRels c)

theorem freeEval_toWord (x : FreeGroup ℕ) : Higman.freeEval (FreeGroup.toWord x) = x := by
  rw [Higman.freeEval_eq]
  have h : (FreeGroup.toWord x).map (fun p : ℕ × Bool => (p.1, p.2)) = FreeGroup.toWord x := by
    simp
  rw [h, FreeGroup.mk_toWord]

/-- **An r.e. predicate on raw words is the domain of a program.** -/
theorem exists_code_dom_iff {p : Higman.RawWord → Prop} (hp : REPred p) :
    ∃ c : Nat.Partrec.Code,
      ∀ w : Higman.RawWord, (Nat.Partrec.Code.eval c (Encodable.encode w)).Dom ↔ p w := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp
  refine ⟨c, fun w => ?_⟩
  rw [hc]
  simp [Part.assert, Encodable.encodek]

/-- **There are countably many recursive presentations** (tex l.435–436): every recursively
presented group is isomorphic to one of the countably many groups `CodeGroup c`. -/
theorem recursivePresentationClassesStatement : RecursivePresentationClassesStatement := by
  refine ⟨Nat.Partrec.Code, inferInstance, CodeGroup, fun c => inferInstance, ?_⟩
  intro Γ _ _ hP
  obtain ⟨P⟩ := hP
  obtain ⟨c, hc⟩ := exists_code_dom_iff P.re
  have hset : Higman.relatorSetOf P.gen = codeRels c := by
    ext x
    have h1 : x ∈ Higman.relatorSetOf P.gen ↔ Higman.evalRaw P.gen (FreeGroup.toWord x) = 1 := by
      have h := Higman.mem_relatorSetOf P.gen (FreeGroup.toWord x)
      rwa [freeEval_toWord] at h
    exact h1.trans (hc (FreeGroup.toWord x)).symm
  exact ⟨c, ⟨(Higman.presentedGroupEquiv P.spans).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (congrArg Subgroup.normalClosure hset))⟩⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.exists_code_dom_iff
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.recursivePresentationClassesStatement

end SimpleKazhdanSofic
end GroupApproximation
