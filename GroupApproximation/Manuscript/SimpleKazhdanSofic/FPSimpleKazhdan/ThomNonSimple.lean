import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Finiteness
import GroupApproximation.Kazhdan.SemidirectProductKazhdan
import GroupApproximation.GroupTheory.AlgebraicUltraproductLEF
import GroupApproximation.Sofic.ThreeRadicalsCoincide
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ToeplitzAnswer
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ThomFactorizationSentence
import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import GroupApproximation.Meta.AxiomGuard

/-!
# `simple_kazhdan_sofic_group.tex`, Thom's non-simple example (tex l.57–60)

> l.57–60: Thom constructed a finitely generated Kazhdan group that is locally embeddable into
> finite groups but not residually finite, and so lacks the factorization property~\cite{Thom},
> but his example is not simple.

The citation is A. Thom, *Examples of hyperlinear groups without factorization property*, Groups
Geom. Dyn. 4 (2010), 195–208.  The tex describes no construction, so the sentence is formalized as
its mathematical content: the inference "Kazhdan and not residually finite, so no factorization
property" (Kirchberg), together with a finitely generated Kazhdan LEF group that is not residually
finite, lacks the factorization property, and is **not simple**.  The group is built here from the
library; it is not Thom's specific group, which the tex does not identify.

## The mathematics

Let `E = G_X` be the elementary group `EL_3(R_X)` at the Toeplitz subshift.  The closed Theorem
`thm:main` (`printedSimpleKazhdanSoficMain`) gives that `E` is infinite, finitely generated, simple,
Kazhdan and LEF.  Put `Γ = E × E`.

* `Γ` is finitely generated: a product of finitely generated groups is (`Prod.instGroupFG`).
* `Γ` is Kazhdan: `E ⋊[1] E` is Kazhdan (`HasKazhdanPropertyT.semidirectProduct`, any action), and
  for the trivial action it is `E × E` (`SemidirectProduct.mulEquivProd`).
* `Γ` is LEF: textbook-LEF passes to products (`isTextbookLEF_prod`), and `isLEF_iff_textbook`.
* `Γ` is not residually finite: `E` embeds by `x ↦ (x, 1)`, residual finiteness passes to
  subgroups (`IsResiduallyFinite.of_injective`), and an infinite simple group is not residually
  finite.
* `Γ` lacks the factorization property: it is Kazhdan and not residually finite
  (`printedKazhdanNotResiduallyFiniteLacksFactorizationProperty`, Kirchberg's theorem).
* `Γ` is not simple: `ker(snd) = E × 1` is normal; it is not trivial since `(a, 1)` lies in it for
  `a ≠ 1`, and it is not everything since `(1, a)` does not.

The general product step is `prodSelf_kazhdanLEFNotResiduallyFiniteNotSimple`; the endpoint is
`manuscriptSentence_thomKazhdanLEFNotResiduallyFiniteNotSimple`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan

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
    have h1 := congrArg Prod.fst hxy
    exact h1
  · intro hs
    obtain ⟨a, ha⟩ := @exists_ne E hnt 1
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (E × E) _ hs (MonoidHom.snd E E).ker
        inferInstance with hbot | htop
    · have hmem : ((a, 1) : E × E) ∈ (MonoidHom.snd E E).ker := MonoidHom.mem_ker.2 rfl
      rw [hbot, Subgroup.mem_bot] at hmem
      have h1 := congrArg Prod.fst hmem
      exact ha h1
    · have hmem : ((1, a) : E × E) ∈ (MonoidHom.snd E E).ker := by
        rw [htop]
        exact Subgroup.mem_top _
      exact ha (MonoidHom.mem_ker.1 hmem)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan.prodSelf_kazhdanLEFNotResiduallyFiniteNotSimple

/-- **tex l.57–60**: a Kazhdan group that is not residually finite lacks the factorization property,
and there is a finitely generated Kazhdan LEF group that is not residually finite, lacks the
factorization property, and is not simple (witness `G_X × G_X` at the Toeplitz subshift). -/
theorem manuscriptSentence_thomKazhdanLEFNotResiduallyFiniteNotSimple :
    (∀ (E : Type) [Group E], HasKazhdanPropertyT.{0, 0} E → ¬ IsResiduallyFinite E →
        ¬ GroupApproximation.NinetyNineProblems.HasFactorizationProperty E) ∧
      ∃ (E : Type) (_ : Group E), Group.FG E ∧ HasKazhdanPropertyT.{0, 0} E ∧ IsLEF E ∧
        ¬ IsResiduallyFinite E ∧
        ¬ GroupApproximation.NinetyNineProblems.HasFactorizationProperty E ∧
        ¬ IsSimpleGroup E := by
  obtain ⟨hinf, hfg, hsimple, hT, -, hlef, -, -⟩ :=
    printedSimpleKazhdanSoficMain Bool toeplitzSubshift toeplitzSubshift_infinite
      toeplitzSubshift_isMinimal 3 le_rfl
  have hnrf : ¬ IsResiduallyFinite (G toeplitzSubshift) :=
    @GroupApproximation.NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite
      (G toeplitzSubshift) _ hsimple hinf
  obtain ⟨hfg2, hT2, hlef2, hnrf2, hns2⟩ :=
    prodSelf_kazhdanLEFNotResiduallyFiniteNotSimple (@IsSimpleGroup.toNontrivial _ _ hsimple)
      hfg hT hlef hnrf
  exact ⟨fun E _ => printedKazhdanNotResiduallyFiniteLacksFactorizationProperty.{0} E,
    G toeplitzSubshift × G toeplitzSubshift, inferInstance, hfg2, hT2, hlef2, hnrf2,
    printedKazhdanNotResiduallyFiniteLacksFactorizationProperty.{0}
      (G toeplitzSubshift × G toeplitzSubshift) hT2 hnrf2, hns2⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan.manuscriptSentence_thomKazhdanLEFNotResiduallyFiniteNotSimple

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan
