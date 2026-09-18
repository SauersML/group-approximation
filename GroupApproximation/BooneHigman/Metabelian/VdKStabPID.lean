import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Equiv
import GroupApproximation.BooneHigman.Metabelian.VdKStabRows
import GroupApproximation.Meta.AxiomGuard

/-!
# Stable range of fields and principal ideal domains

Lane `bh-met-90f`, part (A) in low dimension.

* `vdkStab_stableRangeLE_one_of_field`: `sr(K) ≤ 1` for a field `K`.
* `vdkStab_exists_isCoprime_add_mul`: in a PID, if no irreducible divides all of `a, g, c` and
  `g ≠ 0`, then `a + t c` is coprime to `g` for some `t` (take `t` = product of the prime
  factors of `g` not dividing `a`).
* `vdkStab_stableRangeLE_two_of_pid`: `sr(R) ≤ 2` for a PID `R`.
* `vdkStab_stableRangeLE_polyZero` / `vdkStab_stableRangeLE_polyOne`: the cases `k = 0, 1` of
  `sr(𝔽_p[x₁, …, x_k]) ≤ k + 1`.

Truth check: `scratchpad/vdkstab_check.py` runs the PID construction on random unimodular rows
over `𝔽_p[s]`, `p ∈ {2, 3, 5}` (about 8000 rows, no failure).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **`sr(K) ≤ 1` for a field.**  If `c = 0` take `b = 0`; otherwise take
`b = ((1 - v₀) c⁻¹, …)`, so that the first reduced entry is `1`. -/
theorem vdkStab_stableRangeLE_one_of_field (K : Type*) [Field K] :
    vdkStab_StableRangeLE K 1 := by
  intro n hn v hv
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases hc : v (Fin.last (m + 1)) = 0
  · refine ⟨0, vdkStab_isUnimodular_of_forall_mem hv fun i ↦ ?_⟩
    induction i using Fin.lastCases with
    | last => rw [hc]; exact Ideal.zero_mem _
    | cast i =>
      exact vdkStab_mem_span_of_eq i
        (by rw [vdkStab_reduceRow_apply, Pi.zero_apply, zero_mul, add_zero])
  · refine ⟨fun _ ↦ (1 - v (Fin.castSucc 0)) * (v (Fin.last (m + 1)))⁻¹, ?_⟩
    rw [vdkStab_isUnimodular_iff]
    exact vdkStab_mem_span_of_eq 0
      (by rw [vdkStab_reduceRow_apply, inv_mul_cancel_right₀ hc, add_sub_cancel])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_stableRangeLE_one_of_field

/-- In a PID, if `g ≠ 0` and no irreducible divides all of `a`, `g`, `c`, then `a + t c` is
coprime to `g` for `t` = the product of the (normalized) prime factors of `g` that do not
divide `a`. -/
theorem vdkStab_exists_isCoprime_add_mul {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {a g c : R} (hg : g ≠ 0)
    (h : ∀ z : R, Irreducible z → z ∣ a → z ∣ g → z ∣ c → False) :
    ∃ t : R, IsCoprime (a + t * c) g := by
  classical
  obtain ⟨F, hmem⟩ : ∃ F : Finset R,
      ∀ π, π ∈ F ↔ π ∈ UniqueFactorizationMonoid.factors g ∧ ¬π ∣ a :=
    ⟨(UniqueFactorizationMonoid.factors g).toFinset.filter fun π ↦ ¬π ∣ a,
      fun π ↦ by rw [Finset.mem_filter, Multiset.mem_toFinset]⟩
  refine ⟨∏ x ∈ F, x, isCoprime_of_irreducible_dvd (fun h0 ↦ hg h0.2) fun z hz hzs hzg ↦ ?_⟩
  by_cases hza : z ∣ a
  · have hztc : z ∣ (∏ x ∈ F, x) * c := (dvd_add_right hza).mp hzs
    rcases hz.prime.dvd_or_dvd hztc with hzt | hzc
    · obtain ⟨π, hπF, hzπ⟩ := hz.prime.exists_mem_finset_dvd hzt
      have hπ := (hmem π).mp hπF
      have hπz : π ∣ z :=
        (hz.associated_of_dvd (UniqueFactorizationMonoid.irreducible_of_factor π hπ.1)
          hzπ).symm.dvd
      exact hπ.2 (hπz.trans hza)
    · exact h z hz hza hzg hzc
  · obtain ⟨q, hq, hzq⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hg hz hzg
    have hqF : q ∈ F := (hmem q).mpr ⟨hq, fun hqa ↦ hza (hzq.dvd.trans hqa)⟩
    have hztc : z ∣ (∏ x ∈ F, x) * c :=
      (hzq.dvd.trans (Finset.dvd_prod_of_mem (fun x ↦ x) hqF)).mul_right c
    exact hza ((dvd_add_left hztc).mp hzs)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_exists_isCoprime_add_mul

/-- **`sr(R) ≤ 2` for a PID.**  Write the row as `(a, v₁, …, v_{m+1}, c)` and let `g` generate
`(v₁, …, v_{m+1})`.  If `g = 0` then `(a, c)` is unimodular and `b = (1, …, 1)` works.  Otherwise
pick `t` with `a + t c` coprime to `g` and take `b = (t, 0, …, 0)`. -/
theorem vdkStab_stableRangeLE_two_of_pid (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] : vdkStab_StableRangeLE R 2 := by
  intro n hn v hv
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨g, hgJ, hgdvd⟩ : ∃ g : R,
      g ∈ Ideal.span (Set.range fun j : Fin (m + 1) ↦ v (Fin.castSucc j.succ)) ∧
        ∀ j : Fin (m + 1), g ∣ v (Fin.castSucc j.succ) :=
    ⟨Submodule.IsPrincipal.generator
        (Ideal.span (Set.range fun j : Fin (m + 1) ↦ v (Fin.castSucc j.succ))),
      Submodule.IsPrincipal.generator_mem _, fun j ↦
        (Submodule.IsPrincipal.mem_iff_generator_dvd
          (Ideal.span (Set.range fun j : Fin (m + 1) ↦ v (Fin.castSucc j.succ)))).mp
          (vdkStab_mem_span_range (fun j : Fin (m + 1) ↦ v (Fin.castSucc j.succ)) j)⟩
  by_cases hg0 : g = 0
  · have hz : ∀ j : Fin (m + 1), v (Fin.castSucc j.succ) = 0 := by
      intro j
      have hj := hgdvd j
      rw [hg0, zero_dvd_iff] at hj
      exact hj
    have hc_mem : v (Fin.last (m + 2)) ∈
        Ideal.span (Set.range (vdkStab_reduceRow v fun _ ↦ (1 : R))) :=
      vdkStab_mem_span_of_eq (Fin.succ (0 : Fin (m + 1)))
        (by rw [vdkStab_reduceRow_apply, hz 0, zero_add, one_mul])
    have ha_mem : v (Fin.castSucc 0) ∈
        Ideal.span (Set.range (vdkStab_reduceRow v fun _ ↦ (1 : R))) := by
      have h0 := Ideal.sub_mem _
        (vdkStab_mem_span_range (vdkStab_reduceRow v fun _ ↦ (1 : R)) 0) hc_mem
      rwa [vdkStab_reduceRow_apply, one_mul, add_sub_cancel_right] at h0
    refine ⟨fun _ ↦ (1 : R), vdkStab_isUnimodular_of_forall_mem hv fun i ↦ ?_⟩
    induction i using Fin.lastCases with
    | last => exact hc_mem
    | cast i =>
      induction i using Fin.cases with
      | zero => exact ha_mem
      | succ j => rw [hz j]; exact Ideal.zero_mem _
  · have hno : ∀ z : R, Irreducible z → z ∣ v (Fin.castSucc 0) → z ∣ g →
        z ∣ v (Fin.last (m + 2)) → False := by
      intro z hz hza hzg hzc
      have hall : ∀ i, z ∣ v i := by
        intro i
        induction i using Fin.lastCases with
        | last => exact hzc
        | cast i =>
          induction i using Fin.cases with
          | zero => exact hza
          | succ j => exact hzg.trans (hgdvd j)
      obtain ⟨w, hw⟩ := hv
      have h1 : z ∣ ∑ i, v i * w i := Finset.dvd_sum fun i _ ↦ (hall i).mul_right (w i)
      rw [hw] at h1
      exact hz.not_isUnit (isUnit_of_dvd_one h1)
    obtain ⟨t, α, β, hαβ⟩ := vdkStab_exists_isCoprime_add_mul hg0 hno
    refine ⟨Pi.single 0 t, ?_⟩
    have hr0 : v (Fin.castSucc 0) + t * v (Fin.last (m + 2)) ∈
        Ideal.span (Set.range (vdkStab_reduceRow v (Pi.single 0 t))) :=
      vdkStab_mem_span_of_eq 0 (by rw [vdkStab_reduceRow_apply, Pi.single_eq_same])
    have hJ : Ideal.span (Set.range fun j : Fin (m + 1) ↦ v (Fin.castSucc j.succ)) ≤
        Ideal.span (Set.range (vdkStab_reduceRow v (Pi.single 0 t))) :=
      vdkStab_span_range_le fun j ↦ vdkStab_mem_span_of_eq j.succ (by
        rw [vdkStab_reduceRow_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero j), zero_mul,
          add_zero])
    rw [vdkStab_isUnimodular_iff, ← hαβ]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ α hr0) (Ideal.mul_mem_left _ β (hJ hgJ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_stableRangeLE_two_of_pid

/-- Case `k = 0` of part (A): `sr(𝔽_p[∅]) ≤ 1`, transported from the field `𝔽_p`. -/
theorem vdkStab_stableRangeLE_polyZero (p : ℕ) (hp : p.Prime) :
    vdkStab_StableRangeLE (MvPolynomial (Fin 0) (ZMod p)) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact vdkStab_stableRangeLE_of_ringEquiv (MvPolynomial.isEmptyRingEquiv (ZMod p) (Fin 0)).symm
    (vdkStab_stableRangeLE_one_of_field (ZMod p))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_stableRangeLE_polyZero

/-- Case `k = 1` of part (A): `sr(𝔽_p[x₁]) ≤ 2`, transported from the PID `𝔽_p[X]`. -/
theorem vdkStab_stableRangeLE_polyOne (p : ℕ) (hp : p.Prime) :
    vdkStab_StableRangeLE (MvPolynomial (Fin 1) (ZMod p)) 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact vdkStab_stableRangeLE_of_ringEquiv
    (MvPolynomial.uniqueAlgEquiv (ZMod p) (Fin 1)).toRingEquiv.symm
    (vdkStab_stableRangeLE_two_of_pid (Polynomial (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_stableRangeLE_polyOne

end GroupApproximation.BooneHigman.Metabelian.ElemFP
