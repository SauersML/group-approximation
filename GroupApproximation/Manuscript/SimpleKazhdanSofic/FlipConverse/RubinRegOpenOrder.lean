import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinRegOpenPolar
import GroupApproximation.Meta.AxiomGuard

/-!
# Rubin dictionary, part 2: order on rigid stabilisers and on their polars

Census row `2e7c7d9ab149`; lane `sk-flip-13` (Rubin route, infrastructure).  Notation as in
`RubinRegOpenPolar`: `F_O = {g ∈ [[T]] | SupportedIn g O}`, `C` the centraliser in `[[T]]`.

**Correction of the lane statement.**  The lane asked for
`rigid_le_iff : F_O ⊆ F_{O'} ↔ interior (closure O) ⊆ interior (closure O')`.  This is FALSE:
for `x ≠ y` in the Cantor space, `O = {x}ᶜ`, `O' = {y}ᶜ` are open and dense, so both regular
interiors are `univ`, but an element of `[[T]]` supported in `{x}ᶜ` moving `y` exists
(`exists_supportedIn_apply_ne`), so `F_O ⊄ F_{O'}`.  This is proved in Lean as
`regOpen_rigid_subset_counterexample`.  The true statements authored instead:

* `regOpen_rigid_subset_iff` (for `O` open, `O'` arbitrary): `F_O ⊆ F_{O'} ↔ O ⊆ O'`.
  `⇐` is `SupportedIn.mono`; `⇒`: for `x ∈ O \ O'`, `exists_supportedIn_apply_ne` gives
  `g ∈ F_O` with `g x ≠ x`, so `g ∉ F_{O'}`.
* `regOpen_centralizer_centralizer_rigid_subset_iff` (the regular-open dictionary, for `O, O'`
  open): `C(C(F_O)) ⊆ C(C(F_{O'})) ↔ interior (closure O) ⊆ interior (closure O')`.  Rewrite both
  double centralisers with `regOpen_centralizer_centralizer_rigid_open` and apply
  `regOpen_rigid_subset_iff` to the open set `interior (closure O)`.  This is the order statement
  the lane intended: the regular interior is seen by the polars, not by `F_O` itself.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- Rigid stabilisers of open sets reflect and preserve inclusion: `F_O ⊆ F_{O'} ↔ O ⊆ O'`. -/
theorem regOpen_rigid_subset_iff [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {O O' : Set X} (hO : IsOpen O) :
    {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) O} ⊆
        {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) O'} ↔ O ⊆ O' := by
  constructor
  · intro hsub x hxO
    by_contra hxO'
    obtain ⟨g, hg, hgO, hgx⟩ := exists_supportedIn_apply_ne hT hO hxO
    have hmem : (⟨g, hg⟩ : topologicalFullGroup T) ∈
        {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) O} := hgO
    have h1 : SupportedIn g O' := hsub hmem
    exact hgx (h1 x hxO')
  · intro hOO' g hg
    have hg' : SupportedIn (g : X ≃ₜ X) O := hg
    have h2 : SupportedIn (g : X ≃ₜ X) O' := hg'.mono hOO'
    exact h2

/-- Regular-open dictionary: for `O, O'` open,
`C(C(F_O)) ⊆ C(C(F_{O'})) ↔ interior (closure O) ⊆ interior (closure O')`. -/
theorem regOpen_centralizer_centralizer_rigid_subset_iff [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {O O' : Set X} (hO : IsOpen O) (hO' : IsOpen O') :
    (Subgroup.centralizer
        (Subgroup.centralizer {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) O} :
          Set (topologicalFullGroup T)) : Set (topologicalFullGroup T)) ⊆
        (Subgroup.centralizer
          (Subgroup.centralizer {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) O'} :
            Set (topologicalFullGroup T)) : Set (topologicalFullGroup T)) ↔
      interior (closure O) ⊆ interior (closure O') := by
  rw [regOpen_centralizer_centralizer_rigid_open hT hO,
    regOpen_centralizer_centralizer_rigid_open hT hO']
  exact regOpen_rigid_subset_iff hT isOpen_interior

/-- The literal lane statement `F_O ⊆ F_{O'} ↔ interior (closure O) ⊆ interior (closure O')`
fails: for `x ≠ y`, the dense open sets `{x}ᶜ`, `{y}ᶜ` have the same regular interior but
`F_{{x}ᶜ} ⊄ F_{{y}ᶜ}`. -/
theorem regOpen_rigid_subset_counterexample [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T)
    {x y : X} (hxy : x ≠ y) :
    interior (closure ({x}ᶜ : Set X)) ⊆ interior (closure ({y}ᶜ : Set X)) ∧
      ¬ {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) {x}ᶜ} ⊆
          {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) {y}ᶜ} := by
  refine ⟨?_, fun hsub => ?_⟩
  · rw [closure_compl_singleton y, interior_univ]
    exact Set.subset_univ _
  · have h1 : ({x}ᶜ : Set X) ⊆ {y}ᶜ :=
      (regOpen_rigid_subset_iff hT isOpen_compl_singleton).1 hsub
    have h2 : y ∈ ({y}ᶜ : Set X) := h1 (Set.mem_compl_singleton_iff.2 hxy.symm)
    exact (Set.mem_compl_singleton_iff.1 h2) rfl

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.regOpen_rigid_subset_iff
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.regOpen_centralizer_centralizer_rigid_subset_iff
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.regOpen_rigid_subset_counterexample
