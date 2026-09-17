import GroupApproximation.Manuscript.NonMF.AuditClifford2.LampWindows
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Meta.AxiomGuard

/-!
# Residual finiteness of the finite windows `C_Y ⋊ Γ_n`

`non_mf_groups_exist.tex`, proof of `prop:clifford-locally-rf`, lines 2041--2047:

> This semidirect product is residually finite.  Indeed, an element with
> nontrivial $\Gamma_n$-component survives in a finite quotient of
> $\Gamma_n$.  For a nontrivial element of $C_Y$, let $J$ be the kernel of
> the action $\Gamma_n\to\operatorname{Aut}(C_Y)$.  The quotient $\Gamma_n/J$
> is finite, and the element has nontrivial image in the finite group
> $C_Y\rtimes(\Gamma_n/J)$.

Proof route. The printed argument is formalized for an arbitrary finite normal
factor `M` and a residually finite acting group `G`:
* A nontrivial `G`-component survives in a finite quotient `G ⧸ N` of `G`
  (`Group.exists_finiteIndexNormalSubgroup_notMem`).
* `J = φ.ker` consists exactly of the elements acting trivially.
* `G ⧸ J ≅ φ.range ≤ MulAut M` is finite. The map
  `M ⋊[φ] G → M ⋊[kerLift φ] (G ⧸ J)` is a homomorphism into a finite group that
  keeps the `M`-component, so it detects a nontrivial `M`-component.
* These two cases give residual finiteness
  (`Group.residuallyFinite_of_forall_exists_finite_monoidHom`).

The concrete instance takes `M = C_Y`, the finite lamp window from
`LampWindows`, and `G = Γ_n = (level α hα n).range`. The latter is residually
finite because it is isomorphic to `Γ`.
-/

namespace GroupApproximation.Manuscript.NonMF.AuditClifford2

open MappingTelescope MarkedCompression SoficMarkedCompression SemidirectProduct

noncomputable section

section Printed

variable {M G : Type} [Group M] [Group G] (φ : G →* MulAut M)

/-- An element with nontrivial acting component survives in a finite quotient
of the acting group. -/
theorem exists_finite_quotient_right_ne_one [Group.ResiduallyFinite G]
    {g : M ⋊[φ] G} (hg : g.right ≠ 1) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (f : G →* Q),
      Function.Surjective f ∧ (f.comp SemidirectProduct.rightHom) g ≠ 1 := by
  obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem g.right hg
  refine ⟨G ⧸ N.toSubgroup, inferInstance, inferInstance,
    QuotientGroup.mk' N.toSubgroup, QuotientGroup.mk'_surjective N.toSubgroup, ?_⟩
  intro h
  exact hN (FiniteIndexNormalSubgroup.mem_toSubgroup_iff.mp
    ((QuotientGroup.eq_one_iff (N := N.toSubgroup) g.right).mp h))

#audit_axioms exists_finite_quotient_right_ne_one

/-- The kernel `J` of the action consists exactly of the elements acting
trivially. -/
theorem mem_ker_action_iff (h : G) : h ∈ φ.ker ↔ ∀ m : M, φ h m = m := by
  constructor
  · intro hh m
    rw [MonoidHom.mem_ker.mp hh, MulAut.one_apply]
  · intro hm
    exact MonoidHom.mem_ker.mpr
      (MulEquiv.ext fun m ↦ (hm m).trans (MulAut.one_apply m).symm)

#audit_axioms mem_ker_action_iff

/-- The reduction `M ⋊ G → M ⋊ (G ⧸ J)`. -/
def reduceByKernel : M ⋊[φ] G →* M ⋊[QuotientGroup.kerLift φ] (G ⧸ φ.ker) :=
  SemidirectProduct.map (MonoidHom.id M) (QuotientGroup.mk' φ.ker)
    fun _ ↦ MonoidHom.ext fun _ ↦ rfl

/-- `G ⧸ J` is finite when `M` is finite. -/
theorem finite_quotient_ker_action [Finite M] : Finite (G ⧸ φ.ker) := by
  haveI : Finite (MulAut M) :=
    Finite.of_injective (fun e : MulAut M ↦ (e : M → M)) DFunLike.coe_injective
  exact Finite.of_equiv φ.range (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv

theorem finite_reduceByKernel_target [Finite M] :
    Finite (M ⋊[QuotientGroup.kerLift φ] (G ⧸ φ.ker)) := by
  haveI := finite_quotient_ker_action φ
  exact Finite.of_equiv (M × (G ⧸ φ.ker))
    (SemidirectProduct.equivProd (φ := QuotientGroup.kerLift φ)).symm

theorem reduceByKernel_ne_one_of_left_ne_one {g : M ⋊[φ] G} (hg : g.left ≠ 1) :
    reduceByKernel φ g ≠ 1 :=
  fun h ↦ hg (congrArg SemidirectProduct.left h)

/-- The printed argument: a finite group acted on by a residually finite group
gives a residually finite semidirect product. -/
theorem residuallyFinite_printed [Finite M] [Group.ResiduallyFinite G] :
    Group.ResiduallyFinite (M ⋊[φ] G) := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  by_cases hright : g.right = 1
  · have hleft : g.left ≠ 1 := fun hl ↦ hg (SemidirectProduct.ext hl hright)
    exact ⟨M ⋊[QuotientGroup.kerLift φ] (G ⧸ φ.ker), inferInstance,
      finite_reduceByKernel_target φ, reduceByKernel φ,
      reduceByKernel_ne_one_of_left_ne_one φ hleft⟩
  · obtain ⟨Q, hQgrp, hQ, f, -, hf⟩ := exists_finite_quotient_right_ne_one φ hright
    exact ⟨Q, hQgrp, hQ, f.comp SemidirectProduct.rightHom, hf⟩

end Printed

section Concrete

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

theorem levelRange_residuallyFinite [Group.ResiduallyFinite Γ] (n : ℕ) :
    Group.ResiduallyFinite (level α hα n).range :=
  GroupApproximation.residuallyFinite_of_mulEquiv
    (MonoidHom.ofInjective (level_injective α hα n)).symm

/-- The action `Γ_n → Aut(C_Y)`. -/
abbrev windowAction (n : ℕ) (S : Finset (Cosets α hα)) :
    (level α hα n).range →* MulAut (cliffordWindow α hα n S) :=
  restrictAut (SemidirectAssoc.baseAction (shiftHom α hα) (lampAction α hα))
    (cliffordWindow α hα n S) (level α hα n).range (cliffordWindow_invariant α hα n S)

/-- The semidirect product `C_Y ⋊ Γ_n`. -/
abbrev WindowSemidirect (n : ℕ) (S : Finset (Cosets α hα)) : Type :=
  cliffordWindow α hα n S ⋊[windowAction α hα n S] (level α hα n).range

/-- tex 2041--2042: `C_Y ⋊ Γ_n` is residually finite. -/
theorem manuscriptSentence_windowSemidirectResiduallyFinite [Group.ResiduallyFinite Γ]
    [α.range.FiniteIndex] (n : ℕ) (S : Finset (Cosets α hα)) :
    Group.ResiduallyFinite (WindowSemidirect α hα n S) := by
  haveI : Finite (cliffordWindow α hα n S) := finite_lampWindow (finite_siteWindow α hα n S)
  haveI := levelRange_residuallyFinite α hα n
  exact residuallyFinite_printed (windowAction α hα n S)

#audit_axioms manuscriptSentence_windowSemidirectResiduallyFinite

/-- tex 2042--2043: an element of `C_Y ⋊ Γ_n` with nontrivial `Γ_n`-component
survives in a finite quotient of `Γ_n`. -/
theorem manuscriptSentence_rightComponentSurvivesFiniteQuotient [Group.ResiduallyFinite Γ]
    (n : ℕ) (S : Finset (Cosets α hα)) {g : WindowSemidirect α hα n S}
    (hg : g.right ≠ 1) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (f : (level α hα n).range →* Q),
      Function.Surjective f ∧ (f.comp SemidirectProduct.rightHom) g ≠ 1 := by
  haveI := levelRange_residuallyFinite α hα n
  exact exists_finite_quotient_right_ne_one (windowAction α hα n S) hg

#audit_axioms manuscriptSentence_rightComponentSurvivesFiniteQuotient

/-- tex 2043--2044: `J` is the kernel of the action `Γ_n → Aut(C_Y)`, that is,
the elements of `Γ_n` fixing every element of `C_Y`. -/
theorem manuscriptSentence_actionKernel (n : ℕ) (S : Finset (Cosets α hα)) :
    ∀ h : (level α hα n).range, h ∈ (windowAction α hα n S).ker ↔
      ∀ c : cliffordWindow α hα n S, windowAction α hα n S h c = c :=
  fun h ↦ mem_ker_action_iff (windowAction α hα n S) h

#audit_axioms manuscriptSentence_actionKernel

/-- tex 2044--2046: `Γ_n / J` is finite, and a nontrivial `C_Y`-component has
nontrivial image in the finite group `C_Y ⋊ (Γ_n / J)`. -/
theorem manuscriptSentence_quotientFiniteNontrivialImage [α.range.FiniteIndex] (n : ℕ)
    (S : Finset (Cosets α hα)) :
    Finite ((level α hα n).range ⧸ (windowAction α hα n S).ker) ∧
      Finite (cliffordWindow α hα n S ⋊[QuotientGroup.kerLift (windowAction α hα n S)]
        ((level α hα n).range ⧸ (windowAction α hα n S).ker)) ∧
      ∀ g : WindowSemidirect α hα n S, g.left ≠ 1 →
        reduceByKernel (windowAction α hα n S) g ≠ 1 := by
  haveI : Finite (cliffordWindow α hα n S) := finite_lampWindow (finite_siteWindow α hα n S)
  exact ⟨finite_quotient_ker_action (windowAction α hα n S),
    finite_reduceByKernel_target (windowAction α hα n S),
    fun _ hg ↦ reduceByKernel_ne_one_of_left_ne_one (windowAction α hα n S) hg⟩

#audit_axioms manuscriptSentence_quotientFiniteNontrivialImage

end Concrete

end

end GroupApproximation.Manuscript.NonMF.AuditClifford2
