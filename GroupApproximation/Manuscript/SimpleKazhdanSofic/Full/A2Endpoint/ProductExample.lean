import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Finiteness
import GroupApproximation.Kazhdan.SemidirectProductKazhdan
import GroupApproximation.GroupTheory.AlgebraicUltraproductLEF
import GroupApproximation.Sofic.ThreeRadicalsCoincide
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ToeplitzAnswer
import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import GroupApproximation.Meta.AxiomGuard

/-!
# A non-simple, finitely generated, Kazhdan, LEF group that is not residually finite (row A2)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–60 (table row A2):

> Thom constructed a finitely generated Kazhdan group that is locally embeddable into finite
> groups but not residually finite, and so lacks the factorization property~\cite{Thom}, but his
> example is not simple.

The group-theoretic content of the sentence is the existence of a finitely generated Kazhdan LEF
group that is not residually finite and not simple.  Thom's own group (GGD 4 (2010), §2.1) is built
in `Full/A2Endpoint/ThomGroup.lean`, where its non-simplicity is proved; its Kazhdan, LEF and
non-residually-finite clauses rest on Suslin's `EL_3 = SL_3` and Shalom's theorem.  This file gives
an unconditional witness of all group-theoretic clauses from the closed Theorem `thm:main`:

Let `E = G_X = EL_3(R_X)` at the Toeplitz subshift.  `thm:main` (`printedSimpleKazhdanSoficMain`)
says `E` is infinite, finitely generated, simple, Kazhdan and LEF.  Put `Γ = E × E`.

* `Γ` is finitely generated (`Prod.instGroupFG`).
* `Γ` is Kazhdan: `E ⋊[1] E` is Kazhdan (`HasKazhdanPropertyT.semidirectProduct`), and it is
  `E × E` (`SemidirectProduct.mulEquivProd`).
* `Γ` is LEF: textbook-LEF passes to products (`isTextbookLEF_prod`, `isLEF_iff_textbook`).
* `Γ` is not residually finite: `x ↦ (x, 1)` embeds `E`, residual finiteness passes to subgroups
  (`IsResiduallyFinite.of_injective`), and an infinite simple group is not residually finite.
* `Γ` is not simple: `ker snd = E × 1` is normal, contains `(a, 1)` for `a ≠ 1`, misses `(1, a)`.

Endpoints: `prodSelf_kazhdanLEFNotResiduallyFiniteNotSimple`,
`exists_fg_kazhdan_lef_not_residuallyFinite_not_simple`.
-/

namespace GroupApproximation.Full.A2Endpoint

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

/-- For a nontrivial, finitely generated, Kazhdan, LEF group `E` that is not residually finite,
the square `E × E` is finitely generated, Kazhdan and LEF, not residually finite, and not simple. -/
theorem prodSelf_kazhdanLEFNotResiduallyFiniteNotSimple {E : Type} [Group E]
    (hnt : Nontrivial E) (hfg : Group.FG E) (hT : HasKazhdanPropertyT.{0, 0} E) (hlef : IsLEF E)
    (hnrf : ¬ IsResiduallyFinite E) :
    Group.FG (E × E) ∧ HasKazhdanPropertyT.{0, 0} (E × E) ∧ IsLEF (E × E) ∧
      ¬ IsResiduallyFinite (E × E) ∧ ¬ IsSimpleGroup (E × E) := by
  haveI : Group.FG E := hfg
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · exact HasKazhdanPropertyT.of_mulEquiv (SemidirectProduct.mulEquivProd (N := E) (G := E)).symm
      (HasKazhdanPropertyT.semidirectProduct (φ := 1) hT hT)
  · exact (isLEF_iff_textbook (E × E)).2
      (isTextbookLEF_prod ((isLEF_iff_textbook E).1 hlef) ((isLEF_iff_textbook E).1 hlef))
  · intro hrf
    refine hnrf (IsResiduallyFinite.of_injective (MonoidHom.inl E E) ?_ hrf)
    intro x y hxy
    exact congrArg Prod.fst hxy
  · intro hs
    obtain ⟨a, ha⟩ := @exists_ne E hnt 1
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (E × E) _ hs (MonoidHom.snd E E).ker
        inferInstance with hbot | htop
    · have hmem : ((a, 1) : E × E) ∈ (MonoidHom.snd E E).ker := MonoidHom.mem_ker.2 rfl
      rw [hbot, Subgroup.mem_bot] at hmem
      exact ha (congrArg Prod.fst hmem)
    · have hmem : ((1, a) : E × E) ∈ (MonoidHom.snd E E).ker := by
        rw [htop]
        exact Subgroup.mem_top _
      exact ha (MonoidHom.mem_ker.1 hmem)

/-- **tex l.57–60**, group-theoretic clauses: there is a finitely generated Kazhdan LEF group that
is not residually finite and not simple (witness `G_X × G_X` at the Toeplitz subshift). -/
theorem exists_fg_kazhdan_lef_not_residuallyFinite_not_simple :
    ∃ (E : Type) (_ : Group E), Group.FG E ∧ HasKazhdanPropertyT.{0, 0} E ∧ IsLEF E ∧
      ¬ IsResiduallyFinite E ∧ ¬ IsSimpleGroup E := by
  obtain ⟨hinf, hfg, hsimple, hT, -, hlef, -, -⟩ :=
    printedSimpleKazhdanSoficMain Bool toeplitzSubshift toeplitzSubshift_infinite
      toeplitzSubshift_isMinimal 3 le_rfl
  have hnrf : ¬ IsResiduallyFinite (G toeplitzSubshift) :=
    @GroupApproximation.NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite
      (G toeplitzSubshift) _ hsimple hinf
  obtain ⟨hfg2, hT2, hlef2, hnrf2, hns2⟩ :=
    prodSelf_kazhdanLEFNotResiduallyFiniteNotSimple (@IsSimpleGroup.toNontrivial _ _ hsimple)
      hfg hT hlef hnrf
  exact ⟨G toeplitzSubshift × G toeplitzSubshift, inferInstance, hfg2, hT2, hlef2, hnrf2, hns2⟩

#audit_axioms GroupApproximation.Full.A2Endpoint.prodSelf_kazhdanLEFNotResiduallyFiniteNotSimple
#audit_axioms GroupApproximation.Full.A2Endpoint.exists_fg_kazhdan_lef_not_residuallyFinite_not_simple

end GroupApproximation.Full.A2Endpoint
