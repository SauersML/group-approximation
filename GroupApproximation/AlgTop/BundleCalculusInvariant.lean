import GroupApproximation.AlgTop.BundleCalculusTransport
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Bundle calculus IV: unitary invariants are homotopy invariants, and rank

Every numerical invariant of a bundle that the campaign will want -- rank, a
Chern number, a class in `K₀`, a determinant of a clutching function -- is a
function of the projection that does not change under unitary conjugation.  So
rather than prove homotopy invariance once per invariant, prove it once for
*all* of them:

> if `τ` is unchanged by unitary conjugation, then `τ ∘ f` is locally constant
> along any continuous family `f` of projections, and constant along one indexed
> by a preconnected space.

The proof is three lines on top of `BundleCalculusProjection`, and it is the
reason that file states its theorem for an arbitrary index space rather than for
`[0,1]`: with the index space a parameter, the *same* statement gives homotopy
invariance (index `[0,1]`) and constancy of rank over a connected base (index the
base itself).

Rank is then the case `τ = Matrix.trace`.  Its invariance is one rewrite --
`trace (u a u*) = trace (u* u a) = trace a` -- and it needs only `star u * u = 1`,
not unitarity.  Nothing here needs the fact that the trace of a projection is an
integer, which is the usual route to local constancy and is a genuinely harder
theorem.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace BundleCalculus

section General

variable {A B : Type*} [Monoid A] [StarMul A]

/-- A unitary invariant does not distinguish unitarily conjugate projections.
This is the whole interface: everything downstream is this lemma composed with a
theorem of `BundleCalculusProjection`. -/
theorem eq_of_unitaryConj (τ : A → B)
    (hτ : ∀ u ∈ unitary A, ∀ a : A, τ (u * a * star u) = τ a)
    {p q : A} (h : UnitaryConj p q) : τ p = τ q := by
  obtain ⟨u, hu, huq⟩ := h
  rw [← huq, hτ u hu p]

end General

section CStar

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **A unitary invariant of a continuous family of projections is locally
constant.**  No connectedness, and no integrality of the invariant: the
neighbourhood on which it is constant is the ball where the projections are at
distance less than `1`. -/
theorem isLocallyConstant_of_unitaryInvariant {X : Type*} [TopologicalSpace X]
    (τ : A → B) (hτ : ∀ u ∈ unitary A, ∀ a : A, τ (u * a * star u) = τ a)
    {f : X → A} (hf : Continuous f) (hproj : ∀ x, IsStarProjection (f x)) :
    IsLocallyConstant fun x => τ (f x) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have hopen : IsOpen {y : X | ‖f y - f x‖ < 1} :=
    isOpen_lt ((hf.sub continuous_const).norm) continuous_const
  have hmem : x ∈ {y : X | ‖f y - f x‖ < 1} := by simp
  filter_upwards [hopen.mem_nhds hmem] with y hy
  exact eq_of_unitaryConj τ hτ (unitaryConj_of_norm_sub_lt_one (hproj y) (hproj x) hy)

/-- **A unitary invariant is constant along a family indexed by a preconnected
space.**  With the index space `[0,1]` this is homotopy invariance of the
invariant; with the index space the base of a bundle it is constancy over a
connected base. -/
theorem eq_of_preconnected {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y]
    (τ : A → B) (hτ : ∀ u ∈ unitary A, ∀ a : A, τ (u * a * star u) = τ a)
    {f : Y → A} (hf : Continuous f) (hproj : ∀ y, IsStarProjection (f y)) (y₀ y₁ : Y) :
    τ (f y₀) = τ (f y₁) :=
  eq_of_unitaryConj τ hτ (unitaryConj_of_preconnected hf hproj y₀ y₁)

theorem eq_of_isPreconnected {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    (hs : IsPreconnected s) (τ : A → B)
    (hτ : ∀ u ∈ unitary A, ∀ a : A, τ (u * a * star u) = τ a)
    {f : Y → A} (hf : Continuous f) (hproj : ∀ y, IsStarProjection (f y))
    {y₀ y₁ : Y} (h₀ : y₀ ∈ s) (h₁ : y₁ ∈ s) :
    τ (f y₀) = τ (f y₁) :=
  eq_of_unitaryConj τ hτ (unitaryConj_of_isPreconnected hs hf hproj h₀ h₁)

end CStar

section Trace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] [StarRing R]

/-- The matrix trace is invariant under conjugation by an isometry.  Only
`star u * u = 1` is used, so unitarity is more than required. -/
theorem trace_isometry_conj {u a : Matrix ι ι R} (hu : star u * u = 1) :
    Matrix.trace (u * a * star u) = Matrix.trace a := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, hu, one_mul]

end Trace

section Rank

open scoped ComplexOrder

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rank of a bundle at a point of the base: the trace of the projection
there.  It is valued in `ℂ` because that is where the trace lands; that it is a
nonnegative integer is a separate theorem and is not needed for anything
below. -/
noncomputable def rankAt (P : C(X, CStarMatrix ι ι ℂ)) (x : X) : ℂ :=
  Matrix.trace (P x)

theorem trace_unitaryInvariant :
    ∀ u ∈ unitary (CStarMatrix ι ι ℂ), ∀ a : CStarMatrix ι ι ℂ,
      Matrix.trace (u * a * star u) = Matrix.trace a := by
  intro u hu a
  exact trace_isometry_conj (Unitary.star_mul_self_of_mem hu)

/-- **Rank is locally constant.** -/
theorem isLocallyConstant_rankAt {P : C(X, CStarMatrix ι ι ℂ)}
    (hP : ∀ x, IsStarProjection (P x)) : IsLocallyConstant (rankAt P) :=
  isLocallyConstant_of_unitaryInvariant Matrix.trace trace_unitaryInvariant
    (map_continuous P) hP

/-- **Rank is constant on a connected base.** -/
theorem rankAt_eq_of_preconnectedSpace [PreconnectedSpace X]
    {P : C(X, CStarMatrix ι ι ℂ)} (hP : ∀ x, IsStarProjection (P x)) (x₀ x₁ : X) :
    rankAt P x₀ = rankAt P x₁ :=
  eq_of_preconnected Matrix.trace trace_unitaryInvariant (map_continuous P) hP x₀ x₁

end Rank

end BundleCalculus
end GroupApproximation
