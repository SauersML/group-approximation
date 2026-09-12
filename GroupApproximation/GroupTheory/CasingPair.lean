import GroupApproximation.GroupTheory.FinitePresentationExtension
import GroupApproximation.GroupTheory.FGAbelianFinitePresentation
import Mathlib.GroupTheory.QuotientGroup.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Casing pairs

Hyde–Lodha, Lemma 4.2: "Let `G` be a group and `N` a subgroup such that `N` is of type `F_∞`, `G` is
finitely generated, and `G' ≤ N`.  Let `H` satisfy `N ≤ H ≤ G`.  Then the pair `(N, G)` is said to form
a casing pair for `H`.  If a group `H` admits a casing pair `N, G`, then `H` is of type `F_∞`."

`isFinitelyPresented_of_casingPair` is the finite-presentation form: `N` is normal in `H` (it contains
`G'`), `H ⧸ N` is a subgroup of the finitely generated abelian group `G ⧸ N`, hence finitely presented
(`FGAbelianFinitePresentation`), and extensions of finitely presented groups are finitely presented
(`FinitePresentationExtension`).
-/

namespace GroupApproximation
namespace CasingPair

open scoped commutatorElement

/-- **Casing pairs (finite presentation).** -/
theorem isFinitelyPresented_of_casingPair {G : Type*} [Group G] [hG : Group.FG G]
    (N H : Subgroup G) (hNH : N ≤ H) (hGN : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ N)
    [hNfp : Group.IsFinitelyPresented N] : Group.IsFinitelyPresented H := by
  have hcomm : ∀ a b : G, ⁅a, b⁆ ∈ N := fun a b =>
    hGN (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  haveI hNn : N.Normal := ⟨fun n hn g => by
    have e : g * n * g⁻¹ = ⁅g, n⁆ * n := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem (hcomm g n) hn⟩
  have hcommQ : ∀ a b : G ⧸ N, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
    have h : QuotientGroup.mk' N ⁅x, y⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hcomm x y)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h
    exact h.eq
  letI : CommGroup (G ⧸ N) := { (inferInstance : Group (G ⧸ N)) with mul_comm := hcommQ }
  haveI : Group.FG (G ⧸ N) := Group.fg_of_surjective (QuotientGroup.mk'_surjective N)
  let π : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  haveI : Group.IsFinitelyPresented π.range :=
    FGAbelianFinitePresentation.isFinitelyPresented_subgroup_of_commGroup π.range
  have hker : π.ker = N.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (h : G)
  haveI : Group.IsFinitelyPresented (H ⧸ π.ker) :=
    Group.IsFinitelyPresented.equiv (QuotientGroup.quotientKerEquivRange π).symm
  haveI hNHn : (N.subgroupOf H).Normal := by
    rw [← hker]
    exact MonoidHom.normal_ker π
  haveI : Group.IsFinitelyPresented (H ⧸ N.subgroupOf H) :=
    Group.IsFinitelyPresented.equiv (QuotientGroup.quotientMulEquivOfEq hker)
  haveI : Group.IsFinitelyPresented (N.subgroupOf H) :=
    Group.IsFinitelyPresented.equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  exact FinitePresentationExtension.isFinitelyPresented_of_normal (N.subgroupOf H)

#audit_axioms GroupApproximation.CasingPair.isFinitelyPresented_of_casingPair

end CasingPair
end GroupApproximation
