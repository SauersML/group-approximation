import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.BigOperators.Fin
import GroupApproximation.Meta.AxiomGuard

/-!
# Unimodular rows, reducible rows and Bass's stable range condition

Lane `bh-met-90f`, helper module.  Concrete definitions for a commutative ring `R`:

* `vdkStab_IsUnimodular v`: the row `v ∈ Rⁿ` is unimodular, `∑ᵢ vᵢ wᵢ = 1` for some `w`.
* `vdkStab_reduceRow v b`: for `v = (v₀, …, v_{n-1}, c) ∈ R^{n+1}` and `b ∈ Rⁿ`, the row
  `(vᵢ + bᵢ c)_{i < n} ∈ Rⁿ`.
* `vdkStab_IsReducible v`: `vdkStab_reduceRow v b` is unimodular for some `b`.
* `vdkStab_StableRangeLE R r`: Bass's `sr(R) ≤ r`; every unimodular row of length `≥ r + 1`
  is reducible.  (Bass states it for length exactly `r + 1`; the two are equivalent by Bass's
  lemma, and the form used here is the one that is consumed.)

Basic facts proved here: the ideal-theoretic reformulation (`1 ∈ span (range v)`), transport
along ring maps and ring isomorphisms, and monotonicity in `r`.  Fields and PIDs are treated in
`VdKStabPID.lean`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- A row `v ∈ Rⁿ` is **unimodular** if `∑ᵢ vᵢ wᵢ = 1` for some `w ∈ Rⁿ`. -/
def vdkStab_IsUnimodular {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) : Prop :=
  ∃ w : Fin n → R, ∑ i, v i * w i = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_IsUnimodular

/-- For `v = (v₀, …, v_{n-1}, c)` and `b ∈ Rⁿ`, the row `(vᵢ + bᵢ c)_{i < n}`. -/
def vdkStab_reduceRow {R : Type*} [CommRing R] {n : ℕ} (v : Fin (n + 1) → R) (b : Fin n → R) :
    Fin n → R :=
  fun i ↦ v (Fin.castSucc i) + b i * v (Fin.last n)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_reduceRow

theorem vdkStab_reduceRow_apply {R : Type*} [CommRing R] {n : ℕ} (v : Fin (n + 1) → R)
    (b : Fin n → R) (i : Fin n) :
    vdkStab_reduceRow v b i = v (Fin.castSucc i) + b i * v (Fin.last n) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_reduceRow_apply

/-- A row `(v₀, …, v_{n-1}, c)` is **reducible** if `(vᵢ + bᵢ c)_{i < n}` is unimodular for some
`b ∈ Rⁿ`. -/
def vdkStab_IsReducible {R : Type*} [CommRing R] {n : ℕ} (v : Fin (n + 1) → R) : Prop :=
  ∃ b : Fin n → R, vdkStab_IsUnimodular (vdkStab_reduceRow v b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_IsReducible

/-- **Bass's stable range condition** `sr(R) ≤ r`: every unimodular row of length `n + 1` with
`n ≥ r` is reducible. -/
def vdkStab_StableRangeLE (R : Type*) [CommRing R] (r : ℕ) : Prop :=
  ∀ n : ℕ, r ≤ n → ∀ v : Fin (n + 1) → R, vdkStab_IsUnimodular v → vdkStab_IsReducible v

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_StableRangeLE

section Basic

variable {R : Type*} [CommRing R]

/-- Unimodularity is `1 ∈ span (range v)`. -/
theorem vdkStab_isUnimodular_iff {n : ℕ} (v : Fin n → R) :
    vdkStab_IsUnimodular v ↔ (1 : R) ∈ Ideal.span (Set.range v) := by
  rw [Ideal.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (Finset.sum_congr rfl fun i _ ↦ mul_comm (w i) (v i)).trans hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (Finset.sum_congr rfl fun i _ ↦ mul_comm (v i) (w i)).trans hw⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_isUnimodular_iff

theorem vdkStab_mem_span_range {n : ℕ} (v : Fin n → R) (i : Fin n) :
    v i ∈ Ideal.span (Set.range v) :=
  Ideal.subset_span (Set.mem_range_self i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_mem_span_range

theorem vdkStab_mem_span_of_eq {n : ℕ} {v : Fin n → R} {x : R} (i : Fin n) (h : v i = x) :
    x ∈ Ideal.span (Set.range v) :=
  h ▸ vdkStab_mem_span_range v i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_mem_span_of_eq

theorem vdkStab_span_range_le {m n : ℕ} {u : Fin m → R} {v : Fin n → R}
    (h : ∀ i, u i ∈ Ideal.span (Set.range v)) :
    Ideal.span (Set.range u) ≤ Ideal.span (Set.range v) :=
  Ideal.span_le.mpr (Set.range_subset_iff.mpr h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_span_range_le

/-- If every entry of a unimodular row `v` lies in the ideal spanned by `v'`, then `v'` is
unimodular. -/
theorem vdkStab_isUnimodular_of_forall_mem {m n : ℕ} {v : Fin m → R} {v' : Fin n → R}
    (hv : vdkStab_IsUnimodular v) (h : ∀ i, v i ∈ Ideal.span (Set.range v')) :
    vdkStab_IsUnimodular v' := by
  rw [vdkStab_isUnimodular_iff] at hv ⊢
  exact vdkStab_span_range_le h hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_isUnimodular_of_forall_mem

/-- Ring maps preserve unimodularity. -/
theorem vdkStab_isUnimodular_map {S : Type*} [CommRing S] (f : R →+* S) {n : ℕ}
    {v : Fin n → R} {v' : Fin n → S} (hv' : ∀ i, v' i = f (v i))
    (hv : vdkStab_IsUnimodular v) : vdkStab_IsUnimodular v' := by
  obtain ⟨w, hw⟩ := hv
  refine ⟨fun i ↦ f (w i), ?_⟩
  calc ∑ i, v' i * f (w i) = f (∑ i, v i * w i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [hv' i, map_mul]
    _ = 1 := by rw [hw, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_isUnimodular_map

/-- The stable range condition transports along ring isomorphisms. -/
theorem vdkStab_stableRangeLE_of_ringEquiv {S : Type*} [CommRing S] (e : R ≃+* S) {r : ℕ}
    (h : vdkStab_StableRangeLE R r) : vdkStab_StableRangeLE S r := by
  intro n hn v hv
  obtain ⟨b, hb⟩ := h n hn (fun i ↦ e.symm (v i))
    (vdkStab_isUnimodular_map (e.symm : S →+* R) (fun _ ↦ rfl) hv)
  refine ⟨fun i ↦ e (b i), vdkStab_isUnimodular_map (e : R →+* S) (fun i ↦ ?_) hb⟩
  simp [vdkStab_reduceRow_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_stableRangeLE_of_ringEquiv

/-- The stable range condition is monotone in `r`. -/
theorem vdkStab_stableRangeLE_mono {r r' : ℕ} (h : vdkStab_StableRangeLE R r) (hr : r ≤ r') :
    vdkStab_StableRangeLE R r' :=
  fun n hn v hv ↦ h n (hr.trans hn) v hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_stableRangeLE_mono

end Basic

end GroupApproximation.BooneHigman.Metabelian.ElemFP
