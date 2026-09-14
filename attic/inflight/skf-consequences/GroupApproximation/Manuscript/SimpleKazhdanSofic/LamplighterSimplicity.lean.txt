import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralSimplicityAssembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterRing

/-!
# The lamplighter host is simple

`simple_kazhdan_sofic_group.tex` at 696c4b602, section "LEF groups", proof of `cor:lef` and
`cor:host`:

> Let $\Delta$ act on $\Omega=\F_2^{\Delta}$ by $(\delta x)(h)=x(\delta^{-1}h)$, and let $\Lambda$ be
> the group of maps $x\mapsto\delta x+f$ … So the action is minimal and topologically free. The ring
> $R_\Delta=\LC(\Omega,\F_2)\rtimes\Lambda$ …

The host `G_Δ = EL_n(R_Δ)` is simple for every `n ≥ 3`. The proof is the general Simplicity theorem
(`General.isSimpleGroup_clopenGroupCrossedProduct`, `thm:general`) applied to the lamplighter action.
Its hypotheses come from sk-lef-action's `LamplighterAction` and from Mathlib:

* `Lamplighter.isMinimal`: the action of `Λ = LampAffine Δ` on `Ω = LampSpace Δ` is minimal;
* `Lamplighter.isTopologicallyFree` (for infinite `Δ`): no nontrivial element fixes a nonempty open
  set, which gives `interior {x | ξ • x = x} = ∅` for `ξ ≠ 1`;
* `Ω = Δ → ZMod 2` is compact, totally separated and nonempty (Mathlib's instances for products of
  finite discrete spaces).

* `Lamplighter.isSimpleGroup_lampRing`;
* the closed endpoint `Lamplighter.printedLamplighterHostSimple`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Lamplighter

/-- **The lamplighter host is simple**: `EL_n(LC(Ω, F_2) ⋊ Λ)` is a simple group for every infinite
`Δ` and every `n ≥ 3`. -/
theorem isSimpleGroup_lampRing (Δ : Type*) [Group Δ] [Infinite Δ] {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup ↥(elementaryGroup (Fin n) (LampRing Δ)) := by
  refine General.isSimpleGroup_clopenGroupCrossedProduct (fun ξ hξ => ?_) hn
  by_contra hne
  obtain ⟨x, hx, hmove⟩ :=
    isTopologicallyFree Δ ξ hξ _ isOpen_interior (Set.nonempty_iff_ne_empty.2 hne)
  have hfix : x ∈ {y : LampSpace Δ | ξ • y = y} := interior_subset hx
  exact hmove hfix

/-- **The lamplighter host is simple** (proof of `cor:lef` and `cor:host`, through `thm:general`):
for every infinite group `Δ` and every `n ≥ 3`, `EL_n(LC(F_2^Δ, F_2) ⋊ Λ)` is simple. -/
def PrintedLamplighterHostSimple : Prop :=
  ∀ (Δ : Type) [Group Δ] [Infinite Δ] (n : ℕ), 3 ≤ n →
    IsSimpleGroup ↥(elementaryGroup (Fin n) (LampRing Δ))

theorem printedLamplighterHostSimple : PrintedLamplighterHostSimple :=
  fun Δ _ _ _ hn => isSimpleGroup_lampRing Δ hn

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.isSimpleGroup_lampRing
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.printedLamplighterHostSimple

end Lamplighter
end SimpleKazhdanSofic
end GroupApproximation
