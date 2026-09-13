import GroupApproximation.Dynamics.ItinerarySubshift
import GroupApproximation.Dynamics.SubshiftLanguageStabilization
import GroupApproximation.Meta.AxiomGuard

/-!
# The inverse-limit core `Y_*`

`non_mf_groups_exist.tex`, lines 1433–1439 (proof of `lem:chain-core-models`, general `X`):
"Thus $\rho_{lm}(Y_l)\subseteq Y_m$, and
\[ Y_* =\bigcap_m\pi_m^{-1}(Y_m),\qquad \pi_m(Y_*)=\bigcap_{l\ge m}\rho_{lm}(Y_l). \]
The second equality follows from compactness in the fibers."

Here `S : ℕ → DiscreteQuotient X` is antitone, `π_m = itinerary T (S m)` and
`ρ_lm = oneBlock (hS h)` for `h : m ≤ l`.  The family `Y m ⊆ itinerarySubshift T (S m)` is any
closed family with `ρ_lm(Y_l) ⊆ Y_m`; the cores of `sec:chain-core` are one instance.

* `inverseLimitCore T Y = ⋂ m, π_m⁻¹(Y m)`, `mem_inverseLimitCore`, `isClosed_inverseLimitCore`;
* `itinerary_mem_of_le`, `preimage_itinerary_antitone`: the preimages decrease;
* `itinerary_image_inverseLimitCore`: `π_m(Y_*) = ⋂_{l ≥ m} ρ_lm(Y_l)`;
* `inverseLimitCore_nonempty`, `mapsTo_zpow_inverseLimitCore`.
-/

namespace GroupApproximation
namespace ChainCore

open Set SymbolicDynamics.FullShift

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) {S : ℕ → DiscreteQuotient X}

/-- The inverse-limit core `Y_* = ⋂_m π_m⁻¹(Y_m)`. -/
def inverseLimitCore (Y : ∀ m, Set (ℤ → S m)) : Set X :=
  ⋂ m, itinerary T (S m) ⁻¹' Y m

theorem mem_inverseLimitCore {Y : ∀ m, Set (ℤ → S m)} {x : X} :
    x ∈ inverseLimitCore T Y ↔ ∀ m, itinerary T (S m) x ∈ Y m :=
  mem_iInter

theorem isClosed_inverseLimitCore {Y : ∀ m, Set (ℤ → S m)} (hcl : ∀ m, IsClosed (Y m)) :
    IsClosed (inverseLimitCore T Y) :=
  isClosed_iInter fun m ↦ (hcl m).preimage (continuous_itinerary T (S m))

/-- If `ρ_lm(Y_l) ⊆ Y_m`, a point whose `l`-th itinerary lies in `Y_l` has its `m`-th itinerary in
`Y_m`. -/
theorem itinerary_mem_of_le (hS : Antitone S) {Y : ∀ m, Set (ℤ → S m)}
    (hcompat : ∀ {l m : ℕ} (h : m ≤ l), oneBlock (hS h) '' Y l ⊆ Y m) {m l : ℕ} (h : m ≤ l)
    (x : X) (hx : itinerary T (S l) x ∈ Y l) : itinerary T (S m) x ∈ Y m := by
  rw [← oneBlock_itinerary (T := T) (hS h) x]
  exact hcompat h ⟨_, hx, rfl⟩

theorem preimage_itinerary_antitone (hS : Antitone S) {Y : ∀ m, Set (ℤ → S m)}
    (hcompat : ∀ {l m : ℕ} (h : m ≤ l), oneBlock (hS h) '' Y l ⊆ Y m) :
    Antitone fun r ↦ itinerary T (S r) ⁻¹' Y r :=
  fun _ _ h x hx ↦ itinerary_mem_of_le T hS hcompat h x hx

/-- **Compactness in the fibers**: `π_m(Y_*) = ⋂_{l ≥ m} ρ_lm(Y_l)`. -/
theorem itinerary_image_inverseLimitCore [CompactSpace X] (hS : Antitone S)
    {Y : ∀ m, Set (ℤ → S m)} (hsub : ∀ m, Y m ⊆ itinerarySubshift T (S m))
    (hcompat : ∀ {l m : ℕ} (h : m ≤ l), oneBlock (hS h) '' Y l ⊆ Y m)
    (hcl : ∀ m, IsClosed (Y m)) (m : ℕ) :
    itinerary T (S m) '' inverseLimitCore T Y = ⋂ (l : ℕ) (h : m ≤ l), oneBlock (hS h) '' Y l := by
  refine Subset.antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_iInter₂.2 fun l h ↦
      ⟨itinerary T (S l) x, (mem_inverseLimitCore T).1 hx l, oneBlock_itinerary (T := T) (hS h) x⟩
  · have hy' : ∀ l (h : m ≤ l), y ∈ oneBlock (hS h) '' Y l := fun l h ↦ mem_iInter₂.1 hy l h
    obtain ⟨x, hx⟩ := nonempty_iInter_of_antitone
      (Z := fun r ↦ itinerary T (S r) ⁻¹' Y r ∩ itinerary T (S m) ⁻¹' {y})
      (fun _ _ h x hx ↦ ⟨itinerary_mem_of_le T hS hcompat h x hx.1, hx.2⟩)
      (fun r ↦ ((hcl r).preimage (continuous_itinerary T (S r))).inter
        (isClosed_singleton.preimage (continuous_itinerary T (S m))))
      fun r ↦ by
        obtain ⟨z, hz, hzy⟩ := hy' (max r m) (le_max_right r m)
        obtain ⟨x, rfl⟩ := hsub (max r m) hz
        exact ⟨x, itinerary_mem_of_le T hS hcompat (le_max_left r m) x hz,
          (oneBlock_itinerary (T := T) (hS (le_max_right r m)) x).symm.trans hzy⟩
    have hx' := mem_iInter.1 hx
    exact ⟨x, (mem_inverseLimitCore T).2 fun r ↦ (hx' r).1, (hx' 0).2⟩

/-- `Y_*` is nonempty when every `Y_m` is. -/
theorem inverseLimitCore_nonempty [CompactSpace X] (hS : Antitone S) {Y : ∀ m, Set (ℤ → S m)}
    (hsub : ∀ m, Y m ⊆ itinerarySubshift T (S m))
    (hcompat : ∀ {l m : ℕ} (h : m ≤ l), oneBlock (hS h) '' Y l ⊆ Y m)
    (hcl : ∀ m, IsClosed (Y m)) (hne : ∀ m, (Y m).Nonempty) :
    (inverseLimitCore T Y).Nonempty := by
  refine nonempty_iInter_of_antitone (preimage_itinerary_antitone T hS hcompat)
    (fun r ↦ (hcl r).preimage (continuous_itinerary T (S r))) fun r ↦ ?_
  obtain ⟨z, hz⟩ := hne r
  obtain ⟨x, rfl⟩ := hsub r hz
  exact ⟨x, hz⟩

/-- `Y_*` is invariant under every power of `T` when each `Y_m` is shift-invariant. -/
theorem mapsTo_zpow_inverseLimitCore {Y : ∀ m, Set (ℤ → S m)}
    (hY : ∀ m (n : ℤ), MapsTo (shift n) (Y m) (Y m)) (n : ℤ) :
    MapsTo ⇑(T ^ n) (inverseLimitCore T Y) (inverseLimitCore T Y) := by
  intro x hx
  refine (mem_inverseLimitCore T).2 fun m ↦ ?_
  rw [itinerary_zpow_apply]
  exact hY m n ((mem_inverseLimitCore T).1 hx m)

end ChainCore
end GroupApproximation

#audit_axioms GroupApproximation.ChainCore.mem_inverseLimitCore
#audit_axioms GroupApproximation.ChainCore.isClosed_inverseLimitCore
#audit_axioms GroupApproximation.ChainCore.itinerary_mem_of_le
#audit_axioms GroupApproximation.ChainCore.preimage_itinerary_antitone
#audit_axioms GroupApproximation.ChainCore.itinerary_image_inverseLimitCore
#audit_axioms GroupApproximation.ChainCore.inverseLimitCore_nonempty
#audit_axioms GroupApproximation.ChainCore.mapsTo_zpow_inverseLimitCore
