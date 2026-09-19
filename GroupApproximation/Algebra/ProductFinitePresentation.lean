import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Direct products of finitely presented groups

Mathlib closes `Group.IsFinitelyPresented` under free products but not
under direct products, which is what the manuscript's multiplicity
paragraph needs: the family `E × ℤ^k` has to be finitely presented before
anything else about it can be said.

The proof is the classical one.  The direct product is the free product
modulo the commutators between the two factors, and a normal-closure
witness only has to name commutators of *generators*: the centralizer of
an element is a subgroup, so commuting with a generating set is commuting
with the whole factor.  Concretely, `coprodToProd` is surjective and its
kernel is the normal closure of the finitely many commutators
`⁅inl a, inr b⁆` with `a` and `b` drawn from finite generating sets, which
is exactly the input `Group.IsFinitelyPresented.of_surjective` wants.

The inverse map is `MonoidHom.noncommCoprod` applied to the two factor
maps into the quotient; the commutation hypothesis it needs is the
two-step centralizer argument.
-/

namespace GroupApproximation
namespace ProductFinitePresentation

open scoped Monoid.Coprod commutatorElement

variable {G H : Type*} [Group G] [Group H]

/-! ## The canonical surjection -/

/-- The canonical surjection of the free product onto the direct product. -/
def coprodToProd (G H : Type*) [Group G] [Group H] : G ∗ H →* G × H :=
  Monoid.Coprod.lift (MonoidHom.inl G H) (MonoidHom.inr G H)

@[simp] theorem coprodToProd_inl (a : G) :
    coprodToProd G H (Monoid.Coprod.inl a) = (a, 1) := rfl

@[simp] theorem coprodToProd_inr (b : H) :
    coprodToProd G H (Monoid.Coprod.inr b) = (1, b) := rfl

theorem coprodToProd_surjective : Function.Surjective (coprodToProd G H) := by
  rintro ⟨a, b⟩
  refine ⟨Monoid.Coprod.inl a * Monoid.Coprod.inr b, ?_⟩
  rw [map_mul, coprodToProd_inl, coprodToProd_inr]
  simp

/-! ## The commutator relators -/

/-- The commutators between the two factors, taken over a pair of
generating sets.  Their normal closure is the whole kernel. -/
def relators (SG : Set G) (SH : Set H) : Set (G ∗ H) :=
  (fun p : G × H ↦
    ⁅(Monoid.Coprod.inl p.1 : G ∗ H), (Monoid.Coprod.inr p.2 : G ∗ H)⁆) ''
      SG ×ˢ SH

theorem relators_finite {SG : Set G} {SH : Set H} (hG : SG.Finite)
    (hH : SH.Finite) : (relators SG SH).Finite := by
  unfold relators
  exact (hG.prod hH).image _

theorem mem_relators {SG : Set G} {SH : Set H} {a : G} {b : H} (ha : a ∈ SG)
    (hb : b ∈ SH) :
    ⁅(Monoid.Coprod.inl a : G ∗ H), (Monoid.Coprod.inr b : G ∗ H)⁆ ∈
      relators SG SH := by
  unfold relators
  exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

theorem relators_subset_ker (SG : Set G) (SH : Set H) :
    relators SG SH ⊆ ((coprodToProd G H).ker : Set (G ∗ H)) := by
  rintro _ ⟨⟨a, b⟩, -, rfl⟩
  have hcomm : ((a, 1) : G × H) * (1, b) = ((1, b) : G × H) * (a, 1) := by
    simp
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
    coprodToProd_inl, coprodToProd_inr]
  exact commutatorElement_eq_one_iff_commute.mpr hcomm

/-! ## The kernel is exactly that normal closure -/

theorem ker_eq_normalClosure {SG : Set G} {SH : Set H}
    (hSG : Subgroup.closure SG = ⊤) (hSH : Subgroup.closure SH = ⊤) :
    Subgroup.normalClosure (relators SG SH) = (coprodToProd G H).ker := by
  refine le_antisymm
    (Subgroup.normalClosure_le_normal (relators_subset_ker SG SH)) ?_
  set N := Subgroup.normalClosure (relators SG SH) with hNdef
  set π := QuotientGroup.mk' N with hπdef
  have hrel : ∀ a ∈ SG, ∀ b ∈ SH,
      ⁅(Monoid.Coprod.inl a : G ∗ H), (Monoid.Coprod.inr b : G ∗ H)⁆ ∈ N :=
    fun a ha b hb ↦
    Subgroup.subset_normalClosure (mem_relators ha hb)
  -- Generators of the first factor commute with the whole second factor.
  have step1 : ∀ a ∈ SG, ∀ b : H,
      Commute (π (Monoid.Coprod.inl a)) (π (Monoid.Coprod.inr b)) := by
    intro a ha
    have hle : Subgroup.closure SH ≤
        Subgroup.comap (π.comp Monoid.Coprod.inr)
          (Subgroup.centralizer {π (Monoid.Coprod.inl a)}) := by
      rw [Subgroup.closure_le]
      rintro b hb
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply,
        Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
      have h1 : ⁅π (Monoid.Coprod.inl a), π (Monoid.Coprod.inr b)⁆ = 1 := by
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr (hrel a ha b hb)
      exact commutatorElement_eq_one_iff_commute.mp h1
    intro b
    have hb : b ∈ Subgroup.closure SH := hSH ▸ Subgroup.mem_top b
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp (hle hb))) _ rfl
  -- Hence the whole first factor commutes with the whole second factor.
  have hcomm : ∀ (a : G) (b : H),
      Commute (π (Monoid.Coprod.inl a)) (π (Monoid.Coprod.inr b)) := by
    intro a b
    have hle : Subgroup.closure SG ≤
        Subgroup.comap (π.comp Monoid.Coprod.inl)
          (Subgroup.centralizer {π (Monoid.Coprod.inr b)}) := by
      rw [Subgroup.closure_le]
      rintro a' ha'
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply,
        Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
      exact (step1 a' ha' b).symm
    have ha : a ∈ Subgroup.closure SG := hSG ▸ Subgroup.mem_top a
    exact ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_comap.mp (hle ha))) _ rfl).symm
  -- The induced map back is a homomorphism precisely because of that.
  set φ := MonoidHom.noncommCoprod (π.comp Monoid.Coprod.inl)
    (π.comp Monoid.Coprod.inr) hcomm with hφdef
  have hφ : φ.comp (coprodToProd G H) = π := by
    refine Monoid.Coprod.hom_ext ?_ ?_
    · rw [MonoidHom.comp_assoc,
        show (coprodToProd G H).comp Monoid.Coprod.inl = MonoidHom.inl G H from rfl,
        hφdef, MonoidHom.noncommCoprod_comp_inl]
    · rw [MonoidHom.comp_assoc,
        show (coprodToProd G H).comp Monoid.Coprod.inr = MonoidHom.inr G H from rfl,
        hφdef, MonoidHom.noncommCoprod_comp_inr]
  intro x hx
  have hxone : π x = 1 := by
    rw [← hφ, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one]
  exact (QuotientGroup.eq_one_iff x).mp hxone

/-! ## Finite presentation of the direct product -/

theorem fg_of_isFinitelyPresented (G : Type*) [Group G]
    [h : Group.IsFinitelyPresented G] : Group.FG G := by
  obtain ⟨n, φ, hφ, -⟩ := h.out
  exact Group.fg_of_surjective hφ

/-- **The direct product of two finitely presented groups is finitely
presented.** -/
instance instProd [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented H] :
    Group.IsFinitelyPresented (G × H) := by
  obtain ⟨SG, hSG, hSGfin⟩ :=
    Group.fg_iff.mp (fg_of_isFinitelyPresented G)
  obtain ⟨SH, hSH, hSHfin⟩ :=
    Group.fg_iff.mp (fg_of_isFinitelyPresented H)
  exact Group.IsFinitelyPresented.of_surjective (coprodToProd G H)
    coprodToProd_surjective
    ⟨relators SG SH, relators_finite hSGfin hSHfin,
      ker_eq_normalClosure hSG hSH⟩

end ProductFinitePresentation
end GroupApproximation
