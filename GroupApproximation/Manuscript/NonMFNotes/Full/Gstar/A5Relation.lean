import GroupApproximation.Manuscript.NonMFNotes.Full.Gstar.Approximation
import GroupApproximation.Algebra.WreathSplitQuotient
import GroupApproximation.Sofic.FinitePerfectLampExactRadical
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Meta.AxiomGuard

/-!
# One relation changes the MF property

Manuscript `non_mf_group_notes.tex`, `cor:notes-a5-relation` (tex lines 2052--2073):

> Take `K = A₅` and let `r` be the one-site lamp with value `(12)(34)`.  Then
> `Rad_MF(W_{A₅}) = A₅^(X) = ⟨⟨r⟩⟩_{W_{A₅}}` and `W_{A₅}/⟨⟨r⟩⟩ ≅ G_*`.
> Thus `W_{A₅}` is sofic and non-MF, while the quotient is residually finite and MF, although
> every homomorphism from `W_{A₅}` to a norm matrix corona already maps `r` to `1`.

Here `W_{A₅}` is the repository's wreath product
`AlternatingLampLiteral.WA = A₅^(X) ⋊ V(Γ̄, conjD)` over the coset space
`X = V/ι(Γ̄)`, `r = AlternatingLampLiteral.rA` is the lamp `(0 1)(2 3)` (the printed `(12)(34)`
with `Fin 5` labels) at one site, `A₅^(X)` is the lamp subgroup
`FinitePerfectLamp.lampSub A₅`, and `Rad_MF` is the literal genuine-corona radical
`actualCoronaMFResidual`.  The quotient is identified with the literal ascending HNN extension
`Gstar` via `gstarEquivVertical`; `Full/Gstar/WreathStar.lean` identifies `W_{A₅}` itself with
the wreath product `A₅^(G_*/Γ_*) ⋊ G_*` over the literal HNN extension.

Main declaration:

* `notesA5Relation` — the corollary, all clauses.
-/

namespace GroupApproximation.Full.NN05

open MarkedCompression ExplicitLinearModel
open AlternatingLampLiteral (WA qA rA)

/-- The kernel of the split projection `W_{A₅} → V` is the lamp subgroup `A₅^(X)`. -/
theorem qA_ker_eq_lampSub :
    qA.ker = FinitePerfectLamp.lampSub (alternatingGroup (Fin 5)) :=
  ker_rightHom_eq_lampRange

/-- **`cor:notes-a5-relation`.**  For `W_{A₅}` and the one-site lamp `r = (12)(34)`:

1. `Rad_MF(W_{A₅}) = A₅^(X)`;
2. `A₅^(X) = ⟨⟨r⟩⟩`;
3. `W_{A₅}/⟨⟨r⟩⟩ ≅ G_*` (the literal ascending HNN extension);
4. `W_{A₅}` is sofic;
5. `W_{A₅}` is not MF;
6. `G_*` is residually finite;
7. `G_*` is MF;
8. every homomorphism from `W_{A₅}` to the unitary group of a norm matrix corona
   `∏ M_{k(n)} / ⊕ M_{k(n)}` maps `r` to `1`. -/
theorem notesA5Relation :
    actualCoronaMFResidual WA = FinitePerfectLamp.lampSub (alternatingGroup (Fin 5)) ∧
      FinitePerfectLamp.lampSub (alternatingGroup (Fin 5)) = Subgroup.normalClosure {rA} ∧
      Nonempty (WA ⧸ Subgroup.normalClosure {rA} ≃* Gstar) ∧
      IsSofic WA ∧ ¬ IsOperatorMF WA ∧
      IsResiduallyFinite Gstar ∧ IsOperatorMF Gstar ∧
      (∀ (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)),
        letI : ∀ n, Nonempty (X n) :=
          fun n ↦ Fintype.card_pos_iff.mp (hX n)
        ∀ rho : WA →* unitary (NormMatrixCStarCorona (fun n ↦ X n)), rho rA = 1) := by
  have hpkg := SpectralPaper.oneInvisibleRelationPackage
  have hrad : actualCoronaMFResidual WA =
      FinitePerfectLamp.lampSub (alternatingGroup (Fin 5)) :=
    hpkg.2.2.2.2.2.2.2.2.2.2.2.2.1.trans qA_ker_eq_lampSub
  have hnc : FinitePerfectLamp.lampSub (alternatingGroup (Fin 5)) =
      Subgroup.normalClosure {rA} :=
    qA_ker_eq_lampSub.symm.trans hpkg.1
  have hmem : rA ∈ actualCoronaMFResidual WA := by
    rw [hrad, hnc]
    exact Subgroup.subset_normalClosure (Set.mem_singleton rA)
  refine ⟨hrad, hnc, ⟨?_⟩, hpkg.2.2.2.2.1, AlternatingLampLiteral.not_isOperatorMF_WA,
    gstar_residuallyFinite, gstar_isOperatorMF,
    fun X hX => (mem_actualCoronaMFResidual_iff.mp hmem) X hX⟩
  exact (QuotientGroup.quotientMulEquivOfEq hpkg.1.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective qA SemidirectProduct.rightHom_surjective).trans
      gstarEquivVertical.symm)

#audit_axioms qA_ker_eq_lampSub
#audit_axioms notesA5Relation

end GroupApproximation.Full.NN05
