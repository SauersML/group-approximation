import GroupApproximation.Sofic.CentralCoverInheritance
import Mathlib.GroupTheory.QuotientGroup.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# A perfect group over a superperfect base: the kernel is its own coinvariant commutator

Lane sk-leavitt-04, abstract half (carto `sk-leavitt`, Khanh arXiv:2609.08428, proof of Thm 5.1).

Let `φ : G ↠ H` be surjective with `G` perfect, and write `N = ker φ`.  Then
`E = G ⧸ ⁅G, N⁆` is a central extension of `H`:

* `φ` descends to `E → H`, because `⁅G, N⁆ ≤ N`;
* its kernel `N ⧸ ⁅G, N⁆` is central, because `⁅g, n⁆ ∈ ⁅G, N⁆` for `g ∈ G`, `n ∈ N`;
* `E` is perfect, as a quotient of the perfect group `G`.

If every perfect central extension of `H` is injective (superperfectness of `H`, i.e.
`H₂(H) = 0` for perfect `H`), then `E → H` is injective, so `N ⧸ ⁅G, N⁆` is trivial:
`N ≤ ⁅G, N⁆`.

Everything here is proved.  The superperfectness of `H` is a hypothesis of the theorem, printed
as the universal property itself (no stand-in `Prop`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open scoped commutatorElement

/-- The central extension `G ⧸ ⁅G, ker φ⁆ ↠ H` induced by a surjection `φ : G ↠ H`. -/
def commutatorQuotientExtension {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) :
    GroupApproximation.CentralExtension (G ⧸ ⁅(⊤ : Subgroup G), φ.ker⁆) H where
  projection :=
    QuotientGroup.lift ⁅(⊤ : Subgroup G), φ.ker⁆ φ (Subgroup.commutator_le_right _ _)
  surjective := by
    intro h
    obtain ⟨g, rfl⟩ := hφ h
    exact ⟨(g : G ⧸ ⁅(⊤ : Subgroup G), φ.ker⁆), rfl⟩
  ker_le_center := by
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker] at hx
    have hg : φ g = 1 := hx
    have hgker : g ∈ φ.ker := MonoidHom.mem_ker.mpr hg
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    have hc : ⁅h, g⁆ ∈ ⁅(⊤ : Subgroup G), φ.ker⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top h) hgker
    have h1 : QuotientGroup.mk' ⁅(⊤ : Subgroup G), φ.ker⁆ ⁅h, g⁆ = 1 :=
      (QuotientGroup.eq_one_iff ⁅h, g⁆).mpr hc
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.commutatorQuotientExtension

@[simp] theorem commutatorQuotientExtension_projection_mk {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Surjective φ) (g : G) :
    (commutatorQuotientExtension φ hφ).projection (g : G ⧸ ⁅(⊤ : Subgroup G), φ.ker⁆) =
      φ g :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.commutatorQuotientExtension_projection_mk

/-- **Perfect cover over a superperfect base.**  If `G` is perfect, `φ : G ↠ H` is surjective,
and every perfect central extension of `H` is injective, then `ker φ ≤ ⁅G, ker φ⁆`. -/
theorem ker_le_commutator_of_superperfect {G : Type} {H : Type*} [Group G] [Group H]
    [Group.IsPerfect G] (φ : G →* H) (hφ : Function.Surjective φ)
    (hsp : ∀ (E : Type) [Group E] (P : GroupApproximation.CentralExtension E H),
      commutator E = ⊤ → Function.Injective P.projection) :
    φ.ker ≤ ⁅(⊤ : Subgroup G), φ.ker⁆ := by
  intro g hg
  have hperf : commutator (G ⧸ ⁅(⊤ : Subgroup G), φ.ker⁆) = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  have hinj : Function.Injective (commutatorQuotientExtension φ hφ).projection :=
    hsp (G ⧸ ⁅(⊤ : Subgroup G), φ.ker⁆) (commutatorQuotientExtension φ hφ) hperf
  have h1 : (commutatorQuotientExtension φ hφ).projection
      (g : G ⧸ ⁅(⊤ : Subgroup G), φ.ker⁆) =
      (commutatorQuotientExtension φ hφ).projection 1 := by
    rw [map_one, commutatorQuotientExtension_projection_mk]
    exact MonoidHom.mem_ker.mp hg
  exact (QuotientGroup.eq_one_iff g).mp (hinj h1)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.ker_le_commutator_of_superperfect

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
