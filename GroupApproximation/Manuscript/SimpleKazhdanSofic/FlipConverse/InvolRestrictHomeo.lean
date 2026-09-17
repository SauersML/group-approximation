import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.FullGroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SpatialInvolutions
import GroupApproximation.Meta.AxiomGuard

/-!
# Involution normal form, part 2: restriction to an invariant clopen set stays in `[[T]]`

Lane `sk-flip-12` (infrastructure for census row `2e7c7d9ab149`, "for topological full groups
the converse holds"; no printed tex sentence of its own).

Statement.  Let `h ∈ [[T]]` and let `U` be a clopen set with `h '' U = U`.  Then the map
`h₁ = h` on `U`, `h₁ = id` off `U` is again an element of `[[T]]`, supported in `U`, and agrees
with `h` on `U` (`restrict_mem_topologicalFullGroup`).

Proof.
* `h` maps `U` into `U`, and `h x ∈ U → x ∈ U` by injectivity (`mem_iff_apply_mem_of_image_eq`).
  Hence `h.symm` also maps `U` into `U`.
* `restrictToClopenFun h U x := if x ∈ U then h x else x`, with inverse
  `restrictToClopenFun h.symm U`: on `U` both are `h`, `h⁻¹`, which preserve `U`; off `U` both are
  the identity.
* A function defined by cases on a clopen set from two continuous functions is continuous
  (`continuous_ite_clopen`: the frontier of `U` is empty, so `Continuous.if` applies).  So
  `restrictToClopen` is a homeomorphism.
* If `h x = T^{n(x)} x` with `n` continuous, then `h₁ x = T^{n₁(x)} x` with
  `n₁ x := if x ∈ U then n x else 0`, again continuous by `continuous_ite_clopen`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

open Classical in
/-- Case split along a clopen set of two continuous maps is continuous. -/
theorem continuous_ite_clopen {Y : Type*} [TopologicalSpace Y] {U : Set X} (hU : IsClopen U)
    {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => if x ∈ U then f x else g x := by
  have hfr : frontier {x | x ∈ U} = ∅ := by
    rw [Set.setOf_mem_eq]
    exact isClopen_iff_frontier_eq_empty.1 hU
  refine Continuous.if (fun a ha => ?_) hf hg
  have h0 : a ∈ (∅ : Set X) := by
    rw [← hfr]
    exact ha
  exact absurd h0 (Set.notMem_empty a)

/-- A bijection with `h '' U = U` satisfies `h x ∈ U ↔ x ∈ U`. -/
theorem mem_iff_apply_mem_of_image_eq (h : X ≃ₜ X) {U : Set X} (hinv : h '' U = U) (x : X) :
    h x ∈ U ↔ x ∈ U := by
  constructor
  · intro hx
    have hx' : h x ∈ h '' U := by
      rw [hinv]
      exact hx
    obtain ⟨u, hu, hux⟩ := hx'
    have hux' : u = x := h.injective hux
    rw [← hux']
    exact hu
  · intro hx
    rw [← hinv]
    exact Set.mem_image_of_mem h hx

/-- Conversely, `h x ∈ U ↔ x ∈ U` for all `x` gives `h '' U = U`. -/
theorem image_eq_of_forall_apply_mem_iff (h : X ≃ₜ X) {U : Set X}
    (hU : ∀ x, h x ∈ U ↔ x ∈ U) : h '' U = U := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hU x).2 hx
  · intro hy
    have hsy : h.symm y ∈ U := by
      apply (hU (h.symm y)).1
      rw [Homeomorph.apply_symm_apply]
      exact hy
    have himg : h (h.symm y) ∈ h '' U := Set.mem_image_of_mem h hsy
    rwa [Homeomorph.apply_symm_apply] at himg

open Classical in
/-- `h` on `U`, the identity off `U`. -/
noncomputable def restrictToClopenFun (h : X ≃ₜ X) (U : Set X) (x : X) : X :=
  if x ∈ U then h x else x

theorem restrictToClopenFun_of_mem (h : X ≃ₜ X) {U : Set X} {x : X} (hx : x ∈ U) :
    restrictToClopenFun h U x = h x := by
  classical
  rw [restrictToClopenFun, if_pos hx]

theorem restrictToClopenFun_of_notMem (h : X ≃ₜ X) {U : Set X} {x : X} (hx : x ∉ U) :
    restrictToClopenFun h U x = x := by
  classical
  rw [restrictToClopenFun, if_neg hx]

theorem restrictToClopenFun_symm_apply (h : X ≃ₜ X) {U : Set X} (hinv : h '' U = U) (x : X) :
    restrictToClopenFun h.symm U (restrictToClopenFun h U x) = x := by
  by_cases hx : x ∈ U
  · have hhx : h x ∈ U := (mem_iff_apply_mem_of_image_eq h hinv x).2 hx
    rw [restrictToClopenFun_of_mem h hx, restrictToClopenFun_of_mem h.symm hhx,
      Homeomorph.symm_apply_apply]
  · rw [restrictToClopenFun_of_notMem h hx, restrictToClopenFun_of_notMem h.symm hx]

theorem restrictToClopenFun_apply_symm (h : X ≃ₜ X) {U : Set X} (hinv : h '' U = U) (y : X) :
    restrictToClopenFun h U (restrictToClopenFun h.symm U y) = y := by
  by_cases hy : y ∈ U
  · have hsy : h.symm y ∈ U := by
      apply (mem_iff_apply_mem_of_image_eq h hinv (h.symm y)).1
      rw [Homeomorph.apply_symm_apply]
      exact hy
    rw [restrictToClopenFun_of_mem h.symm hy, restrictToClopenFun_of_mem h hsy,
      Homeomorph.apply_symm_apply]
  · rw [restrictToClopenFun_of_notMem h.symm hy, restrictToClopenFun_of_notMem h hy]

theorem continuous_restrictToClopenFun {h : X ≃ₜ X} {U : Set X} (hU : IsClopen U)
    (hh : Continuous h) : Continuous (restrictToClopenFun h U) :=
  continuous_ite_clopen (f := fun x => h x) (g := fun x => x) hU hh continuous_id

/-- The restriction of `h` to an `h`-invariant clopen set `U`, extended by the identity. -/
noncomputable def restrictToClopen (h : X ≃ₜ X) {U : Set X} (hU : IsClopen U)
    (hinv : h '' U = U) : X ≃ₜ X :=
  ⟨⟨restrictToClopenFun h U, restrictToClopenFun h.symm U, restrictToClopenFun_symm_apply h hinv,
    restrictToClopenFun_apply_symm h hinv⟩,
    continuous_restrictToClopenFun hU h.continuous,
    continuous_restrictToClopenFun hU h.symm.continuous⟩

theorem restrictToClopen_apply (h : X ≃ₜ X) {U : Set X} (hU : IsClopen U) (hinv : h '' U = U)
    (x : X) : restrictToClopen h hU hinv x = restrictToClopenFun h U x :=
  rfl

theorem restrictToClopen_supportedIn (h : X ≃ₜ X) {U : Set X} (hU : IsClopen U)
    (hinv : h '' U = U) : SupportedIn (restrictToClopen h hU hinv) U := fun x hx => by
  rw [restrictToClopen_apply, restrictToClopenFun_of_notMem h hx]

theorem restrictToClopen_apply_of_mem (h : X ≃ₜ X) {U : Set X} (hU : IsClopen U)
    (hinv : h '' U = U) {x : X} (hx : x ∈ U) : restrictToClopen h hU hinv x = h x := by
  rw [restrictToClopen_apply, restrictToClopenFun_of_mem h hx]

theorem restrictToClopen_mem {T h : X ≃ₜ X} (hh : h ∈ topologicalFullGroup T) {U : Set X}
    (hU : IsClopen U) (hinv : h '' U = U) :
    restrictToClopen h hU hinv ∈ topologicalFullGroup T := by
  classical
  obtain ⟨n, hn, hhn⟩ := mem_topologicalFullGroup.1 hh
  refine mem_topologicalFullGroup.2
    ⟨fun x => if x ∈ U then n x else 0,
      continuous_ite_clopen (f := n) (g := fun _ => (0 : ℤ)) hU hn continuous_const,
      fun x => ?_⟩
  rw [restrictToClopen_apply]
  by_cases hx : x ∈ U
  · show restrictToClopenFun h U x = (T ^ (if x ∈ U then n x else 0)) x
    rw [restrictToClopenFun_of_mem h hx, if_pos hx, hhn x]
  · show restrictToClopenFun h U x = (T ^ (if x ∈ U then n x else 0)) x
    rw [restrictToClopenFun_of_notMem h hx, if_neg hx, homeoPow_zero]

/-- **Lane sk-flip-12, main statement.**  The restriction of `h ∈ [[T]]` to an `h`-invariant
clopen set `U` (identity off `U`) lies in `[[T]]`, is supported in `U` and agrees with `h`
on `U`. -/
theorem restrict_mem_topologicalFullGroup {T h : X ≃ₜ X} (hh : h ∈ topologicalFullGroup T)
    {U : Set X} (hU : IsClopen U) (hinv : h '' U = U) :
    ∃ h₁ ∈ topologicalFullGroup T, SupportedIn h₁ U ∧ ∀ x ∈ U, h₁ x = h x :=
  ⟨restrictToClopen h hU hinv, restrictToClopen_mem hh hU hinv,
    restrictToClopen_supportedIn h hU hinv, fun _ hx => restrictToClopen_apply_of_mem h hU hinv hx⟩

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.continuous_ite_clopen
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.mem_iff_apply_mem_of_image_eq
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.image_eq_of_forall_apply_mem_iff
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.restrictToClopenFun
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.restrictToClopenFun_of_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.restrictToClopenFun_of_notMem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.restrictToClopenFun_symm_apply
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.restrictToClopenFun_apply_symm
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.continuous_restrictToClopenFun
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.restrictToClopen
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.restrictToClopen_apply
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.restrictToClopen_supportedIn
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.restrictToClopen_apply_of_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.restrictToClopen_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.restrict_mem_topologicalFullGroup
