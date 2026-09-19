import GroupApproximation.Domination.Comparison
import GroupApproximation.Sofic.HyperlinearResidualDetector
import Mathlib.GroupTheory.PresentedGroup

/-!
# Presentation radicals and exact finite-stage consequences

For a finite relator set `R` in a free group, this file attaches the semantic
sofic and hyperlinear radicals to the presented group `F/⟪R⟫`.  The terminology
and the quotient universal property are standard.  The quantitative
domination predicates live on exact representations of the free group, i.e.
on arbitrary assignments of matrices or permutations to the generators.

The full qualitative-radical equivalences require the metric-ultraproduct
bridge and are developed separately.  Here we prove the exact finite-stage
fact used by both that bridge and the jet argument: a finite action satisfying
all relators exactly cannot detect a sofic-radical word.
-/

namespace GroupApproximation

universe u

/-- An element is invisible to every homomorphism into a hyperlinear group.
This is the hyperlinear analogue of `SoficInvisible`. -/
def HyperlinearInvisible {G : Type u} [Group G] (x : G) : Prop :=
  ∀ (H : Type u) (_ : Group H), IsHyperlinear H → ∀ f : G →* H, f x = 1

theorem soficInvisible_of_hyperlinearInvisible
    {G : Type u} [Group G] {x : G} (hx : HyperlinearInvisible x) :
    SoficInvisible x := by
  intro S _ hS f
  exact hx S inferInstance (isHyperlinear_of_isSofic hS) f

/-- Membership of the marked word in the sofic radical of the group presented
by `R`. -/
def SoficPresentationInvisible {α : Type u}
    (R : Finset (FreeGroup α)) (w : FreeGroup α) : Prop :=
  SoficInvisible (PresentedGroup.mk (R : Set (FreeGroup α)) w)

/-- Membership of the marked word in the hyperlinear radical of the group
presented by `R`. -/
def HyperlinearPresentationInvisible {α : Type u}
    (R : Finset (FreeGroup α)) (w : FreeGroup α) : Prop :=
  HyperlinearInvisible (PresentedGroup.mk (R : Set (FreeGroup α)) w)

theorem soficPresentationInvisible_of_hyperlinear
    {α : Type u} {R : Finset (FreeGroup α)} {w : FreeGroup α}
    (h : HyperlinearPresentationInvisible R w) :
    SoficPresentationInvisible R w :=
  soficInvisible_of_hyperlinearInvisible h

namespace FinitePermutationRepresentation

variable {G : Type*} [Group G]

/-- Zero squared-character defect is equivalent to acting trivially.  The
nonnegativity of a finite-action character is essential here. -/
theorem map_eq_one_of_characterDefect_eq_zero
    (ρ : FinitePermutationRepresentation G) (g : G)
    (h : ρ.characterDefect g = 0) : ρ.map g = 1 := by
  have hchar0 := ρ.character_nonneg g
  have hchar1 := ρ.character_le_one g
  have hchar : ρ.character g = 1 := by
    unfold characterDefect at h
    nlinarith
  have hdist : hammingDistance ρ.carrier (ρ.map g) 1 = 0 := by
    rw [ρ.character_eq_one_sub_hammingDistance] at hchar
    linarith
  exact (hammingDistance_eq_zero_iff ρ.carrier (ρ.map g) 1).mp hdist

end FinitePermutationRepresentation

/-- If total permutation-character relator defect is zero, every relator is
represented by the identity. -/
theorem permutation_relators_eq_one_of_totalDefect_eq_zero
    {G : Type*} [Group G] (R : Finset G)
    (ρ : FinitePermutationRepresentation G)
    (hzero : (permutationPowerDefectSystem G).totalDefect R ρ = 0) :
    ∀ r ∈ R, ρ.map r = 1 := by
  intro r hr
  apply ρ.map_eq_one_of_characterDefect_eq_zero r
  apply (Finset.sum_eq_zero_iff_of_nonneg
    (fun g _ ↦ ρ.characterDefect_nonneg g)).mp
  · simpa [PowerDefectSystem.totalDefect,
      permutationPowerDefectSystem] using hzero
  · exact hr

/-- **Exact finite-action radical test.**  A finite action which satisfies all
presentation relators exactly factors through the presented group.  Since a
finite permutation group is sofic, a sofic-radical word is killed.

The facts that finite groups are sofic and that presented groups satisfy this
universal property are standard; the theorem records their precise use in the
domination setup. -/
theorem characterDefect_eq_zero_of_soficPresentationInvisible
    {α : Type} {R : Finset (FreeGroup α)} {w : FreeGroup α}
    (hw : SoficPresentationInvisible R w)
    (ρ : FinitePermutationRepresentation (FreeGroup α))
    (hR : (permutationPowerDefectSystem (FreeGroup α)).totalDefect R ρ = 0) :
    ρ.characterDefect w = 0 := by
  have hrels : ∀ r ∈ R, ρ.map r = 1 :=
    permutation_relators_eq_one_of_totalDefect_eq_zero R ρ hR
  have hclosure : Subgroup.normalClosure (R : Set (FreeGroup α)) ≤
      MonoidHom.ker ρ.toMonoidHom :=
    Subgroup.normalClosure_le_normal fun r hr ↦
      MonoidHom.mem_ker.mpr (hrels r hr)
  let φ : PresentedGroup (R : Set (FreeGroup α)) →* Equiv.Perm ρ.carrier :=
    QuotientGroup.lift (Subgroup.normalClosure (R : Set (FreeGroup α)))
      ρ.toMonoidHom (fun x hx ↦ MonoidHom.mem_ker.mp (hclosure hx))
  have hwkill : φ (PresentedGroup.mk (R : Set (FreeGroup α)) w) = 1 :=
    hw (Equiv.Perm ρ.carrier) inferInstance
      (isSofic_of_finite' (Equiv.Perm ρ.carrier)) φ
  have hφw : φ (PresentedGroup.mk (R : Set (FreeGroup α)) w) =
      ρ.toMonoidHom w := by
    exact QuotientGroup.lift_mk _ _ w
  have hmap : ρ.map w = 1 := by
    rw [hφw] at hwkill
    exact hwkill
  unfold FinitePermutationRepresentation.characterDefect
  have hcharacter : ρ.character w = 1 := by
    rw [FinitePermutationRepresentation.character_eq_one_sub_hammingDistance,
      hmap, hammingDistance_self]
    ring
  rw [hcharacter]
  norm_num

end GroupApproximation
