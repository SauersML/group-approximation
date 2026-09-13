import GroupApproximation.Dynamics.CoreSubshift
import GroupApproximation.Dynamics.ItineraryInverseLimit
import GroupApproximation.Meta.AxiomGuard

/-!
# One-block factors, the cycle condition, and the cores `Y_m`

`non_mf_groups_exist.tex`, lines 1430–1439 (proof of `lem:chain-core-models`, general `X`):
"let $Y_m$ be the cores just constructed.  Refinement gives one-block factor maps
$\rho_{lm}\colon X_l\to X_m$.  Such maps preserve the cycle condition, since cycles map to closed
walks.  Thus $\rho_{lm}(Y_l)\subseteq Y_m$, and
\[ Y_* =\bigcap_m\pi_m^{-1}(Y_m),\qquad \pi_m(Y_*)=\bigcap_{l\ge m}\rho_{lm}(Y_l). \]
The second equality follows from compactness in the fibers."

A symbol map `φ : A → B` acts on configurations by `x ↦ φ ∘ x` and on words by `w ↦ φ ∘ w`.  It
sends edges of the word graphs of `X` to edges of the word graphs of the image of `X`, so walks to
walks and cycles to closed walks.  Hence cyclic edges map to cyclic edges, and the image of a set
with the cycle condition has the cycle condition.  The core `Y_0` of `X` is the set of points all of
whose words give cyclic edges (`mem_coreSubshift_iff`), so `φ ∘ ·` maps the core of `X` into the
core of the image.  The one-block map of a refinement `S ≤ S'` is `ofLE h ∘ ·` and maps the
itinerary subshift of `S` onto that of `S'`, so it maps the core `Y_S` into `Y_{S'}`.

* `wordEdge_comp`, `reflTransGen_wordEdge_comp`, `isCyclicEdge_comp`, `cycleCondition_image_comp`,
  `mapsTo_comp_coreSubshift`;
* `itineraryCore T S = coreSubshift (itinerarySubshift T S)`, `isClosed_itineraryCore`,
  `mapsTo_shift_itineraryCore`, `itineraryCore_subset`;
* `cycleCondition_oneBlock_image`; `oneBlock_image_itineraryCore_subset`: `ρ_lm(Y_l) ⊆ Y_m`;
* `generalCore T S = ⋂_m π_m⁻¹(Y_m)`, `isClosed_generalCore`, `mapsTo_zpow_generalCore`;
  `itinerary_image_generalCore`: `π_m(Y_*) = ⋂_{l ≥ m} ρ_lm(Y_l)`.
-/

namespace GroupApproximation
namespace ChainCore

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph

section Symbol

variable {A B : Type*}

/-- A symbol map sends an edge of the word graph of `X` to an edge of the word graph of the image
of `X`. -/
theorem wordEdge_comp (φ : A → B) {X : Set (ℤ → A)} {r : ℕ} {u v : Fin r → A}
    (huv : wordEdge X r u v) : wordEdge ((fun x : ℤ → A ↦ φ ∘ x) '' X) r (φ ∘ u) (φ ∘ v) := by
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl, rfl⟩ := huv
  exact ⟨word (φ ∘ x) 0 (r + 1), ⟨φ ∘ x, ⟨x, hx, rfl⟩, rfl⟩, rfl, rfl⟩

/-- A symbol map sends walks of the word graph of `X` to walks of the word graph of its image. -/
theorem reflTransGen_wordEdge_comp (φ : A → B) {X : Set (ℤ → A)} {r : ℕ} {u v : Fin r → A}
    (huv : Relation.ReflTransGen (wordEdge X r) u v) :
    Relation.ReflTransGen (wordEdge ((fun x : ℤ → A ↦ φ ∘ x) '' X) r) (φ ∘ u) (φ ∘ v) :=
  Relation.ReflTransGen.lift (fun u : Fin r → A ↦ φ ∘ u) (fun _ _ ↦ wordEdge_comp φ) _ _ huv

/-- **Cycles map to closed walks**: a symbol map sends a cyclic edge of the word graph of `X` to a
cyclic edge of the word graph of its image. -/
theorem isCyclicEdge_comp (φ : A → B) {X : Set (ℤ → A)} {r : ℕ} {w : Fin (r + 1) → A}
    (hw : IsCyclicEdge X r w) : IsCyclicEdge ((fun x : ℤ → A ↦ φ ∘ x) '' X) r (φ ∘ w) := by
  obtain ⟨⟨x, hx, rfl⟩, hcyc⟩ := hw
  exact ⟨⟨φ ∘ x, ⟨x, hx, rfl⟩, rfl⟩, reflTransGen_wordEdge_comp φ hcyc⟩

/-- **Symbol maps preserve the cycle condition.** -/
theorem cycleCondition_image_comp (φ : A → B) {X : Set (ℤ → A)} (hX : CycleCondition X) :
    CycleCondition ((fun x : ℤ → A ↦ φ ∘ x) '' X) := by
  rintro r _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact isCyclicEdge_comp φ (hX r (word x 0 (r + 1)) ⟨x, hx, rfl⟩)

/-- A symbol map sends the core of `X` into the core of the image of `X`. -/
theorem mapsTo_comp_coreSubshift (φ : A → B) (X : Set (ℤ → A)) :
    MapsTo (fun x : ℤ → A ↦ φ ∘ x) (coreSubshift X)
      (coreSubshift ((fun x : ℤ → A ↦ φ ∘ x) '' X)) := fun _ hx ↦
  mem_coreSubshift_iff.2 fun r i ↦ isCyclicEdge_comp φ (mem_coreSubshift_iff.1 hx r i)

end Symbol

section Itinerary

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)

/-- The core `Y_S` of the itinerary subshift of a finite clopen partition `S`: "let $Y_m$ be the
cores just constructed". -/
def itineraryCore (S : DiscreteQuotient X) : Set (ℤ → S) :=
  coreSubshift (itinerarySubshift T S)

theorem isClosed_itineraryCore (S : DiscreteQuotient X) : IsClosed (itineraryCore T S) :=
  isClosed_coreSubshift (itinerarySubshift T S)

theorem mapsTo_shift_itineraryCore (S : DiscreteQuotient X) (n : ℤ) :
    MapsTo (shift n) (itineraryCore T S) (itineraryCore T S) :=
  mapsTo_shift_coreSubshift (itinerarySubshift T S) n

theorem itineraryCore_subset [CompactSpace X] (S : DiscreteQuotient X) :
    itineraryCore T S ⊆ itinerarySubshift T S :=
  coreSubshift_subset (isClosed_itinerarySubshift T S) (mapsTo_shift_itinerarySubshift T S)

variable {T}

/-- **One-block factor maps preserve the cycle condition** (`non_mf_groups_exist.tex`,
lines 1432–1433). -/
theorem cycleCondition_oneBlock_image {S S' : DiscreteQuotient X} (h : S ≤ S') {Z : Set (ℤ → S)}
    (hZ : CycleCondition Z) : CycleCondition (oneBlock h '' Z) :=
  cycleCondition_image_comp (DiscreteQuotient.ofLE h) hZ

/-- `ρ_lm(Y_l) ⊆ Y_m` (`non_mf_groups_exist.tex`, lines 1433–1434): every word of `ρ(y)` is the
image of a word of `y`, cyclic edges map to cyclic edges, and `ρ(X_l) = X_m`. -/
theorem oneBlock_image_itineraryCore_subset {S S' : DiscreteQuotient X} (h : S ≤ S') :
    oneBlock h '' itineraryCore T S ⊆ itineraryCore T S' := by
  rintro _ ⟨y, hy, rfl⟩
  show oneBlock h y ∈ coreSubshift (itinerarySubshift T S')
  rw [← oneBlock_image_itinerarySubshift (T := T) h]
  exact mapsTo_comp_coreSubshift (DiscreteQuotient.ofLE h) (itinerarySubshift T S) hy

variable (T)

/-- The inverse-limit core `Y_* = ⋂_m π_m⁻¹(Y_m)` of the itinerary cores. -/
def generalCore (S : ℕ → DiscreteQuotient X) : Set X :=
  inverseLimitCore (S := S) T fun m ↦ itineraryCore T (S m)

theorem isClosed_generalCore (S : ℕ → DiscreteQuotient X) : IsClosed (generalCore T S) :=
  isClosed_inverseLimitCore T fun m ↦ isClosed_itineraryCore T (S m)

theorem mapsTo_zpow_generalCore (S : ℕ → DiscreteQuotient X) (n : ℤ) :
    MapsTo ⇑(T ^ n) (generalCore T S) (generalCore T S) :=
  mapsTo_zpow_inverseLimitCore T (fun m k ↦ mapsTo_shift_itineraryCore T (S m) k) n

/-- **Compactness in the fibers** for the itinerary cores: `π_m(Y_*) = ⋂_{l ≥ m} ρ_lm(Y_l)`
(`non_mf_groups_exist.tex`, lines 1436–1439). -/
theorem itinerary_image_generalCore [CompactSpace X] {S : ℕ → DiscreteQuotient X}
    (hS : Antitone S) (m : ℕ) :
    itinerary T (S m) '' generalCore T S =
      ⋂ (l : ℕ) (h : m ≤ l), oneBlock (hS h) '' itineraryCore T (S l) :=
  itinerary_image_inverseLimitCore T hS (fun l ↦ itineraryCore_subset T (S l))
    (fun h ↦ oneBlock_image_itineraryCore_subset (hS h))
    (fun l ↦ isClosed_itineraryCore T (S l)) m

end Itinerary

end ChainCore
end GroupApproximation

#audit_axioms GroupApproximation.ChainCore.wordEdge_comp
#audit_axioms GroupApproximation.ChainCore.reflTransGen_wordEdge_comp
#audit_axioms GroupApproximation.ChainCore.isCyclicEdge_comp
#audit_axioms GroupApproximation.ChainCore.cycleCondition_image_comp
#audit_axioms GroupApproximation.ChainCore.mapsTo_comp_coreSubshift
#audit_axioms GroupApproximation.ChainCore.isClosed_itineraryCore
#audit_axioms GroupApproximation.ChainCore.mapsTo_shift_itineraryCore
#audit_axioms GroupApproximation.ChainCore.itineraryCore_subset
#audit_axioms GroupApproximation.ChainCore.cycleCondition_oneBlock_image
#audit_axioms GroupApproximation.ChainCore.oneBlock_image_itineraryCore_subset
#audit_axioms GroupApproximation.ChainCore.isClosed_generalCore
#audit_axioms GroupApproximation.ChainCore.mapsTo_zpow_generalCore
#audit_axioms GroupApproximation.ChainCore.itinerary_image_generalCore
