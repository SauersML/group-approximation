import GroupApproximation.Manuscript.SimpleKazhdanSofic.BooneHigman.Kuznetsov
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SolvableWordProblemRecursivePresentation
import GroupApproximation.Higman.EmbeddingTheorem
import GroupApproximation.Higman.OmegaSharedProof
import GroupApproximation.Higman.BridgeWordProblem
import GroupApproximation.Higman.RelabelPresentation
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.Fintype.Order
import Mathlib.GroupTheory.Finiteness

/-!
# Higman's embedding step for groups with solvable word problem

`simple_kazhdan_sofic_group.tex`, tex l.449–451:

> embeds in a simple subgroup of a finitely presented group~\cite{BooneHigman}, in Thompson's
> form, where the simple group is finitely generated and has solvable word problem

## Proof route

* `rePred_evalRaw_natGen_eq_one`: the raw words trivial in the family `natGen s` form an r.e. set
  when the word problem of `s` is decidable (the argument of
  `nonempty_recursivePresentation_of_hasSolvableWordProblem`, kept as a statement about `natGen s`).
* `nonempty_fgRecursive_of_hasSolvableWordProblem`: the generators `s i` have codes `≤ N`, so the
  free group on `N + 1` letters `j ↦ natGen s j` maps onto the group, and its kernel is r.e.
  after relabelling letters mod `N + 1` (`Higman.BridgeWP.lift_rawToFree`).
* `nonempty_fpOvergroup_of_hasSolvableWordProblem`: Higman's embedding theorem
  (`Higman.fpOvergroup_of_fgRecursive`, `Higman.OmegaSharedProof.reBenign`).
* `hasSolvableWordProblem_of_bijective`: transport along a bijective homomorphism, and
  `embedsInThompsonSimpleSubgroup_of_embedsInFGSimpleSolvable`: the image of a finitely generated
  simple group with solvable word problem in its finitely presented overgroup is a subgroup as in
  Thompson's form.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace BooneHigman

open Encodable Higman

section Presentation

variable {Γ : Type} [Group Γ]

/-- Triviality of raw words in the family `natGen s` is r.e. when the word problem of `s` is
decidable. -/
theorem rePred_evalRaw_natGen_eq_one {ι : Type} [Primcodable ι] (s : ι → Γ)
    (hpart : Partrec (wordProblemOracle s)) :
    REPred fun w : RawWord => evalRaw (natGen s) w = 1 := by
  classical
  let o : ℕ → ℕ := fun n => (wordProblemOracle s n).get trivial
  have ho : Computable o := Partrec.of_eq hpart fun _ => rfl
  have hval : ∀ v : List (ι × Bool), o (encode v) = 1 ↔ wordValue s v = 1 := by
    intro v
    simp [o, wordProblemOracle, Encodable.encodek]
  have hc : Computable fun w : RawWord => o (encode (rawToFamily (ι := ι) w)) :=
    ho.comp (Primrec.encode.comp primrec_rawToFamily).to_comp
  obtain ⟨inst, hprim⟩ := (Primrec.eq : PrimrecRel (@Eq ℕ))
  have hdec : Computable fun w : RawWord =>
      @decide
        ((o (encode (rawToFamily (ι := ι) w)), 1).1 = (o (encode (rawToFamily (ι := ι) w)), 1).2)
        (inst (o (encode (rawToFamily (ι := ι) w)), 1)) :=
    hprim.to_comp.comp (Computable.pair hc (Computable.const 1))
  have hp : ComputablePred fun w : RawWord => o (encode (rawToFamily (ι := ι) w)) = 1 :=
    ⟨inferInstance, Computable.of_eq hdec fun _ => decide_eq_decide.mpr Iff.rfl⟩
  exact (hp.of_eq fun w => by rw [hval, evalRaw_natGen]).to_re

/-- The generators `j ↦ natGen s j`, `j ≤ N`, generate once every code of a generator is `≤ N`. -/
theorem surjective_lift_natGen {ι : Type} [Primcodable ι] {s : ι → Γ}
    (hs : Subgroup.closure (Set.range s) = ⊤) {N : ℕ} (hN : ∀ i, encode i ≤ N) :
    Function.Surjective (FreeGroup.lift fun j : Fin (N + 1) => natGen s (j : ℕ)) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hs, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  refine MonoidHom.mem_range.mpr ⟨FreeGroup.of ⟨encode i, by have := hN i; omega⟩, ?_⟩
  rw [FreeGroup.lift_apply_of]
  simp [natGen, Encodable.encodek]

/-- **A group with solvable word problem has a finite-rank recursive presentation.** -/
theorem nonempty_fgRecursive_of_hasSolvableWordProblem (h : HasSolvableWordProblem Γ) :
    Nonempty (FGRecursive Γ) := by
  obtain ⟨ι, _, _, s, hs, hpart⟩ := h
  obtain ⟨N, hN⟩ := Finite.exists_le fun i : ι => encode i
  have hmod : ∀ v : RawWord,
      (FreeGroup.lift fun j : Fin (N + 1) => natGen s (j : ℕ)) (rawToFree N v) =
        evalRaw (natGen s) (relabel (fun k => k % (N + 1)) v) := fun v =>
    (BridgeWP.lift_rawToFree N (fun j : Fin (N + 1) => natGen s (j : ℕ)) v).trans
      (evalRaw_relabel (natGen s) (fun k => k % (N + 1)) v).symm
  have hσ : Primrec fun k : ℕ => k % (N + 1) :=
    Primrec.nat_mod.comp Primrec.id (Primrec.const (N + 1))
  have hcomp : Computable fun v : RawWord => relabel (fun k => k % (N + 1)) v :=
    (primrec_relabel hσ).to_comp
  have hre : REPred fun v : RawWord =>
      (FreeGroup.lift fun j : Fin (N + 1) => natGen s (j : ℕ)) (rawToFree N v) = 1 :=
    (rePred_comp (rePred_evalRaw_natGen_eq_one s hpart) hcomp).of_eq fun v => by rw [hmod]
  exact ⟨{ rank := N, π := FreeGroup.lift fun j : Fin (N + 1) => natGen s (j : ℕ),
    π_surjective := surjective_lift_natGen hs hN, re := hre }⟩

/-- **Higman.** A group with solvable word problem embeds in a finitely presented group. -/
theorem nonempty_fpOvergroup_of_hasSolvableWordProblem (h : HasSolvableWordProblem Γ) :
    Nonempty (FPOvergroup Γ) := by
  obtain ⟨p⟩ := nonempty_fgRecursive_of_hasSolvableWordProblem h
  exact fpOvergroup_of_fgRecursive Higman.OmegaSharedProof.reBenign p

end Presentation

/-! ## Transport along isomorphisms -/

/-- Solvable word problem transfers along a bijective homomorphism. -/
theorem hasSolvableWordProblem_of_bijective {Γ Δ : Type} [Group Γ] [Group Δ] (f : Γ →* Δ)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f)
    (h : HasSolvableWordProblem Γ) : HasSolvableWordProblem Δ := by
  obtain ⟨ι, _, _, s, hs, hpart⟩ := h
  refine ⟨ι, inferInstance, inferInstance, f ∘ s, ?_, ?_⟩
  · rw [Set.range_comp, ← MonoidHom.map_closure, hs]
    exact Subgroup.map_top_of_surjective f hsurj
  · rw [wordProblemOracle_comp_injective s f hinj]
    exact hpart

/-! ## Thompson's form from an embedding in a finitely generated simple group -/

/-- The image of a finitely generated simple group with solvable word problem in a finitely
presented overgroup is a subgroup as in Thompson's form. -/
theorem embedsInThompsonSimpleSubgroup_of_embedsInFGSimpleSolvable {G : Type} [Group G]
    (h : EmbedsInFGSimpleSolvable G) : EmbedsInThompsonSimpleSubgroup G := by
  obtain ⟨E, _, hsimple, hfg, hwp, f, hf⟩ := h
  obtain ⟨u⟩ := nonempty_fpOvergroup_of_hasSolvableWordProblem hwp
  have hinj : Function.Injective u.emb.rangeRestrict :=
    MonoidHom.rangeRestrict_injective_iff.mpr u.emb_injective
  have hsurj : Function.Surjective u.emb.rangeRestrict := MonoidHom.rangeRestrict_surjective u.emb
  refine ⟨u.K, inferInstance, inferInstance, u.emb.range, ?_, ?_, ?_,
    u.emb.rangeRestrict.comp f, ?_⟩
  · exact (MonoidHom.ofInjective u.emb_injective).symm.isSimpleGroup
  · exact Group.fg_of_surjective hsurj
  · exact hasSolvableWordProblem_of_bijective u.emb.rangeRestrict hinj hsurj hwp
  · exact hinj.comp hf

#audit_axioms GroupApproximation.SimpleKazhdanSofic.BooneHigman.rePred_evalRaw_natGen_eq_one
#audit_axioms GroupApproximation.SimpleKazhdanSofic.BooneHigman.nonempty_fgRecursive_of_hasSolvableWordProblem
#audit_axioms GroupApproximation.SimpleKazhdanSofic.BooneHigman.nonempty_fpOvergroup_of_hasSolvableWordProblem
#audit_axioms GroupApproximation.SimpleKazhdanSofic.BooneHigman.hasSolvableWordProblem_of_bijective
#audit_axioms GroupApproximation.SimpleKazhdanSofic.BooneHigman.embedsInThompsonSimpleSubgroup_of_embedsInFGSimpleSolvable

end BooneHigman
end SimpleKazhdanSofic
end GroupApproximation
