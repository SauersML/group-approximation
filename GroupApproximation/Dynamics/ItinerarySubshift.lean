import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Topology.DiscreteQuotient
import GroupApproximation.Meta.AxiomGuard

/-!
# Itinerary subshifts and one-block factors

`non_mf_groups_exist.tex`, lines 1428–1432 (proof of `lem:chain-core-models`, general `X`):
"For general $X$, choose refining finite clopen partitions $\mathcal P_m$ with mesh tending to
zero.  Let $\pi_m\colon X\to X_m$ be their itinerary subshifts, and let $Y_m$ be the cores just
constructed.  Refinement gives one-block factor maps $\rho_{lm}\colon X_l\to X_m$."

A finite clopen partition is a `DiscreteQuotient S` of `X`.  The itinerary of `x` records the
atom of `S` containing `T^i x` at every time `i : ℤ`; the itinerary subshift is its range, a
closed shift-invariant subset of `ℤ → S` (spelled as in `SubshiftWordGraph`: a `Set (ℤ → A)`
with `∀ n, Set.MapsTo (shift n) X X`).  When `S ≤ S'`, the one-block map sends each symbol
to the atom of `S'` containing it.

* `itinerary`, `continuous_itinerary`, `itinerary_zpow_apply`, `itinerary_apply_self`;
* `itinerarySubshift`, `isClosed_itinerarySubshift`, `mapsTo_shift_itinerarySubshift`;
* `oneBlock`, `continuous_oneBlock`, `oneBlock_shift`, `oneBlock_itinerary`,
  `oneBlock_image_itinerarySubshift`, `oneBlock_oneBlock`.
-/

namespace GroupApproximation
namespace ChainCore

open SymbolicDynamics.FullShift

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)

/-- The itinerary map `π : X → (ℤ → S)`, `x ↦ (i ↦ [T^i x])`. -/
def itinerary (S : DiscreteQuotient X) (x : X) : ℤ → S :=
  fun i ↦ S.proj ((T ^ i) x)

theorem itinerary_apply (S : DiscreteQuotient X) (x : X) (i : ℤ) :
    itinerary T S x i = S.proj ((T ^ i) x) :=
  rfl

theorem continuous_itinerary (S : DiscreteQuotient X) : Continuous (itinerary T S) :=
  continuous_pi fun i ↦ S.proj_continuous.comp (T ^ i).continuous

/-- The itinerary map intertwines `T^n` with the shift by `n`. -/
theorem itinerary_zpow_apply (S : DiscreteQuotient X) (n : ℤ) (x : X) :
    itinerary T S ((T ^ n) x) = shift n (itinerary T S x) := by
  funext i
  rw [shift_apply, itinerary_apply, itinerary_apply, ← Homeomorph.mul_apply, ← zpow_add,
    add_comm]

/-- The itinerary map intertwines `T` with the shift: `π ∘ T = σ ∘ π`. -/
theorem itinerary_apply_self (S : DiscreteQuotient X) (x : X) :
    itinerary T S (T x) = shift 1 (itinerary T S x) := by
  simpa only [zpow_one] using itinerary_zpow_apply T S 1 x

/-- The itinerary subshift `X_m`: the set of itineraries of points of `X`. -/
def itinerarySubshift (S : DiscreteQuotient X) : Set (ℤ → S) :=
  Set.range (itinerary T S)

theorem isClosed_itinerarySubshift [CompactSpace X] (S : DiscreteQuotient X) :
    IsClosed (itinerarySubshift T S) :=
  (isCompact_range (continuous_itinerary T S)).isClosed

theorem mapsTo_shift_itinerarySubshift (S : DiscreteQuotient X) (n : ℤ) :
    Set.MapsTo (shift n) (itinerarySubshift T S) (itinerarySubshift T S) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(T ^ n) x, itinerary_zpow_apply T S n x⟩

variable {T}

/-- The one-block factor map `ρ : (ℤ → S) → (ℤ → S')` for a refinement `S ≤ S'`. -/
def oneBlock {S S' : DiscreteQuotient X} (h : S ≤ S') (y : ℤ → S) : ℤ → S' :=
  fun i ↦ DiscreteQuotient.ofLE h (y i)

theorem oneBlock_apply {S S' : DiscreteQuotient X} (h : S ≤ S') (y : ℤ → S) (i : ℤ) :
    oneBlock h y i = DiscreteQuotient.ofLE h (y i) :=
  rfl

theorem continuous_oneBlock {S S' : DiscreteQuotient X} (h : S ≤ S') :
    Continuous (oneBlock h) :=
  continuous_pi fun i ↦ (DiscreteQuotient.ofLE_continuous h).comp (continuous_apply i)

theorem oneBlock_shift {S S' : DiscreteQuotient X} (h : S ≤ S') (n : ℤ) (y : ℤ → S) :
    oneBlock h (shift n y) = shift n (oneBlock h y) :=
  rfl

theorem oneBlock_oneBlock {S S' S'' : DiscreteQuotient X} (h : S ≤ S') (h' : S' ≤ S'')
    (y : ℤ → S) : oneBlock h' (oneBlock h y) = oneBlock (h.trans h') y := by
  funext i
  obtain ⟨x, hx⟩ := S.proj_surjective (y i)
  rw [oneBlock_apply, oneBlock_apply, oneBlock_apply, ← hx, DiscreteQuotient.ofLE_proj,
    DiscreteQuotient.ofLE_proj, DiscreteQuotient.ofLE_proj]

theorem oneBlock_itinerary {S S' : DiscreteQuotient X} (h : S ≤ S') (x : X) :
    oneBlock h (itinerary T S x) = itinerary T S' x := by
  funext i
  rw [oneBlock_apply, itinerary_apply, itinerary_apply, DiscreteQuotient.ofLE_proj]

/-- The one-block factor maps the itinerary subshift of `S` onto that of `S'`. -/
theorem oneBlock_image_itinerarySubshift {S S' : DiscreteQuotient X} (h : S ≤ S') :
    oneBlock h '' itinerarySubshift T S = itinerarySubshift T S' := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (oneBlock_itinerary h x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨itinerary T S x, ⟨x, rfl⟩, oneBlock_itinerary h x⟩

end ChainCore
end GroupApproximation

#audit_axioms GroupApproximation.ChainCore.continuous_itinerary
#audit_axioms GroupApproximation.ChainCore.itinerary_zpow_apply
#audit_axioms GroupApproximation.ChainCore.itinerary_apply_self
#audit_axioms GroupApproximation.ChainCore.isClosed_itinerarySubshift
#audit_axioms GroupApproximation.ChainCore.mapsTo_shift_itinerarySubshift
#audit_axioms GroupApproximation.ChainCore.continuous_oneBlock
#audit_axioms GroupApproximation.ChainCore.oneBlock_shift
#audit_axioms GroupApproximation.ChainCore.oneBlock_oneBlock
#audit_axioms GroupApproximation.ChainCore.oneBlock_itinerary
#audit_axioms GroupApproximation.ChainCore.oneBlock_image_itinerarySubshift
