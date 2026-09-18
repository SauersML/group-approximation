import GroupApproximation.BooneHigman.Metabelian.EnvelopeNormalFormSplit
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# The normal-form section from finitely many normal-form relators

`RNFreeSectionCoreStatement` (`EnvelopeHigmanVStatement.lean`) asks for finitely many relators
`R ⊆ ker (rnFreeHom H x₀)` and a section `s : V_X(H) → V_X ∗ (H ∗ H) ⧸ ⟨⟨R⟩⟩` compatible with
the generators.  This module reduces it to one statement about the explicit relator set
`nfRelators H x₀` of `EnvelopeNormalFormSplit.lean`.

`RNNormalFormRelatorsStatement`: for self-similar finitely presented `H`, assuming `V_X` is
finitely presented, some finite `R ⊆ nfRelators H x₀` normally generates a subgroup containing
`ker (rnFreeHom H x₀)`.

Route of `rnFreeSectionCore_of_normalForm`.
* `nfRelators_subset_ker` (the wreath recursion `nf_wreath`) gives `R ⊆ ker`.
* `nfSection` lifts `g ∈ V_X(H)` along the surjection `rnFreeHom_surjective` (`surjInv`) and
  projects to the quotient.  `nfSection_one`: the lift of `1` is in the kernel, hence in
  `⟨⟨R⟩⟩`.  `nfSection_mul`: `(s v * k)⁻¹ * s (v * φ k)` is in the kernel, hence in `⟨⟨R⟩⟩`,
  so `QuotientGroup.eq` applies.

*Why the isolated statement is strictly smaller and true.*  It removes from the target the
kernel membership of every relator (the wreath recursion on the Cantor set) and the section
construction, and it keeps an explicit relator set in place of an arbitrary one.
Truth.  Write `L_w(h) = e · nfL h · e⁻¹` for any `e ∈ V_X` with `MapsCone e [x₀] w`, and
`L_[](h) = nfH h`.
* The commutation relators make `L_w(h)` independent of `e`: two choices differ by an element
  of `V_X` fixing `cone [x₀]` pointwise.
* The disjoint-cone relators, conjugated by `V_X`, make `L_u(h)` and `L_w(k)` commute for
  incomparable `u, w`.  `V_X` acts transitively on pairs of incomparable cones with nonempty
  complement.  When the complement is empty, `d = 2` and `{u, w} = {[0], [1]}`.
* The splitting and root relators give `L_w(h) = (V_X element) · Π_x L_{w x}(h|_x)`.
So modulo all of `nfRelators H x₀`, every element is `v · Π_i L_{w_i}(h_i)` over a complete
prefix code.  Two such normal forms with the same image agree after refining to a common code
(`prepend_injective_word`, `cantorHom_injective`).  Hence `⟨⟨nfRelators H x₀⟩⟩ = ker`.
`V_X`, `H` and `H` are factors of `RNFree X H`, so no relators of their own are needed.  Now
`V_X ∗ (H ∗ H)` is finitely presented, and `V_X(H)` is finitely presented for self-similar
finitely presented `H`; this is the truth input of `RNFreeSectionCoreStatement` in
`EnvelopeFPSection.lean`.  The kernel of a surjection between finitely presented groups is
finitely normally generated (B. H. Neumann), so a finite subset of any normal generating set
already normally generates it.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

/-- **Finitely many normal-form relators suffice.**  For a self-similar finitely presented
`H ≤ Aut(T_X)`, given that `V_X` is finitely presented, finitely many relators from the four
explicit families `nfRelators H x₀` normally generate the kernel of `V_X ∗ (H ∗ H) → V_X(H)`. -/
def RNNormalFormRelatorsStatement : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Group.IsFinitelyPresented ↥H → Group.IsFinitelyPresented ↥(higmanThompsonV X) →
      ∃ (x₀ : X) (R : Set (RNFree X H)), R.Finite ∧ R ⊆ nfRelators H x₀ ∧
        (rnFreeHom H x₀).ker ≤ Subgroup.normalClosure R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNNormalFormRelatorsStatement

variable {X : Type*} [Finite X] [Nontrivial X]

/-- Lift along `rnFreeHom H x₀` and project to `RNFree X H ⧸ ⟨⟨R⟩⟩`. -/
def nfSection (H : Subgroup (TreeAut X)) (x₀ : X) (R : Set (RNFree X H))
    (v : ↥(roverNekrashevych X H)) : RNFree X H ⧸ Subgroup.normalClosure R :=
  ((Function.surjInv (rnFreeHom_surjective H x₀) v : RNFree X H) :
    RNFree X H ⧸ Subgroup.normalClosure R)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfSection

theorem nfSection_one (H : Subgroup (TreeAut X)) (x₀ : X) (R : Set (RNFree X H))
    (hker : (rnFreeHom H x₀).ker ≤ Subgroup.normalClosure R) : nfSection H x₀ R 1 = 1 := by
  rw [nfSection, QuotientGroup.eq_one_iff]
  exact hker (MonoidHom.mem_ker.mpr (Function.surjInv_eq (rnFreeHom_surjective H x₀) 1))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfSection_one

theorem nfSection_mul (H : Subgroup (TreeAut X)) (x₀ : X) (R : Set (RNFree X H))
    (hker : (rnFreeHom H x₀).ker ≤ Subgroup.normalClosure R) (v : ↥(roverNekrashevych X H))
    (k : RNFree X H) :
    nfSection H x₀ R v * (k : RNFree X H ⧸ Subgroup.normalClosure R) =
      nfSection H x₀ R (v * rnFreeHom H x₀ k) := by
  rw [nfSection, nfSection, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  refine hker (MonoidHom.mem_ker.mpr ?_)
  rw [map_mul, map_inv, map_mul, Function.surjInv_eq (rnFreeHom_surjective H x₀),
    Function.surjInv_eq (rnFreeHom_surjective H x₀), inv_mul_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfSection_mul

end

/-- **Endpoint.**  Higman's theorem and the normal-form relator statement give the core of the
normal-form section. -/
theorem rnFreeSectionCore_of_normalForm (hV : HigmanVFPStatement)
    (hnf : RNNormalFormRelatorsStatement) : RNFreeSectionCoreStatement := by
  intro X _ _ H hH hfp
  obtain ⟨x₀, R, hR, hRnf, hker⟩ := hnf X H hH hfp (hV X)
  exact ⟨x₀, R, hR, Set.Subset.trans hRnf (nfRelators_subset_ker H x₀), nfSection H x₀ R,
    nfSection_one H x₀ R hker, fun v k _ => nfSection_mul H x₀ R hker v k⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFreeSectionCore_of_normalForm

end GroupApproximation.BooneHigman.Metabelian.Envelope
