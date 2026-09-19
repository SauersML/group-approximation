import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsAsymptotic
import GroupApproximation.Manuscript.SimpleKazhdanSofic.PeriodicMatrixUnits
import GroupApproximation.Manuscript.SimpleKazhdanSofic.RingGeneration
import GroupApproximation.Meta.AxiomGuard

/-!
# `simple_kazhdan_sofic_group.tex`, proof of `thm:main`: periodic approximations are matricial

`simple_kazhdan_sofic_group.tex` at 696c4b602, "Proof of Theorem~\ref{thm:main}", tex 257–271:

> Let $N_\ell$ be its least period, and on $\F_2^{\Z/N_\ell\Z}$ let $P\delta_t=\delta_{t+1}$. For $f$
> depending only on coordinates in $[-\ell,\ell]$ let $D_\ell(f)\delta_t=f(T^ty_\ell)\delta_t$, [...]
> Put $\varphi_\ell(\sum_jf_ju^j)=\sum_jD_\ell(f_j)P^j$ when every $f_j$ is of this kind, and
> $\varphi_\ell=0$ otherwise. Since $PD_\ell(f)P^{-1}=D_\ell(f\circ T^{-1})$ [...] for fixed $r,s\in R$
> the identities [...] hold for large $\ell$, and $\varphi_\ell(1)=I$. The shifts $T^ty_\ell$,
> $0\le t<N_\ell$, are distinct, so products of the $P^iD_\ell(e_a)P^{-i}$ give every diagonal matrix
> unit, and with $P$ every matrix unit. So $\varphi_\ell(S)$ generates $M_{N_\ell}(\F_2)$, and
> Theorem~\ref{thm:general} applies.

The models `D ℓ`, the recurrence positions and the least periods come from the absorbed
`AsymptoticModels` (ms-units).  This module proves:

* `cutoffModel`: the printed `φ_ℓ`, which is `Pestov91.periodicModel (D ℓ)` when every coefficient depends only
  on `[-ℓ, ℓ]`, and `0` otherwise; `eventually_cutoffModel_eq`, `cutoffModel_one`;
* `cutoffModel_unit_zpow`, `cutoffModel_letter`: `φ_ℓ(u^j) = P^j` and `φ_ℓ(e_a) = diag(1_{y_ℓ(t) = a})`;
* `translates_distinct_of_leastPeriod`: the shifts `T^t y_ℓ`, `0 ≤ t < N_ℓ`, are distinct;
* `exists_periodicMatricial`: for an infinite minimal subshift, there are sizes `N_ℓ ≥ 1` and maps
  `φ_ℓ : R → M_{N_ℓ}(F₂)` with `φ_ℓ(1) = I`, `φ_ℓ({1, u, u⁻¹} ∪ {e_a})` generating `M_{N_ℓ}(F₂)`, and
  additivity and multiplicativity for large `ℓ`, the body of ct-two-ended's `IsMatricialVia`.
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

open SymbolicDynamics.FullShift WordGraph Filter Matrix Pestov91 ClopenCrossedProduct
open Multiplicative (toAdd ofAdd)

section Cutoff

variable {A : Type} [TopologicalSpace A] {X : Set (ℤ → A)} {T : ↥X ≃ₜ ↥X}

/-- `f` depends only on the coordinates in `[-ℓ, ℓ]` (tex 258–259). -/
def DependsOnWindow (T : ↥X ≃ₜ ↥X) (ℓ : ℕ) (f : ClopenCoeff T (ZMod 2)) : Prop :=
  ∀ y z : ↥X, (∀ i : ℤ, |i| ≤ ℓ → y.1 i = z.1 i) →
    (ClopenCoeff.of T (ZMod 2)).symm f y = (ClopenCoeff.of T (ZMod 2)).symm f z

theorem DependsOnWindow.mono {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') {f : ClopenCoeff T (ZMod 2)}
    (hf : DependsOnWindow T ℓ f) : DependsOnWindow T ℓ' f :=
  fun y z hyz => hf y z fun i hi => hyz i (hi.trans (by exact_mod_cast h))

/-- **The printed `φ_ℓ`** (tex 261–263): `Σ_j D_ℓ(f_j) P^j` when every `f_j` depends only on
`[-ℓ, ℓ]`, and `0` otherwise. -/
noncomputable def cutoffModel {N : ℕ} [NeZero N] (D : ClopenCoeff T (ZMod 2) →+* (ZMod N → ZMod 2))
    (ℓ : ℕ) (r : ClopenCrossedProduct T (ZMod 2)) : Matrix (ZMod N) (ZMod N) (ZMod 2) := by
  classical
  exact if ∀ g ∈ SkewMonoidAlgebra.support r, DependsOnWindow T ℓ (SkewMonoidAlgebra.coeff r g)
    then periodicModel D r else 0

theorem cutoffModel_eq_of {N : ℕ} [NeZero N] (D : ClopenCoeff T (ZMod 2) →+* (ZMod N → ZMod 2))
    {ℓ : ℕ} {r : ClopenCrossedProduct T (ZMod 2)}
    (hr : ∀ g ∈ SkewMonoidAlgebra.support r, DependsOnWindow T ℓ (SkewMonoidAlgebra.coeff r g)) :
    cutoffModel D ℓ r = periodicModel D r := by
  unfold cutoffModel
  rw [if_pos hr]

/-- For fixed `r`, the cutoff is eventually the periodic model. -/
theorem eventually_cutoffModel_eq [DiscreteTopology A] [Finite A] (hXc : IsClosed X)
    {N : ℕ → ℕ} [∀ ℓ, NeZero (N ℓ)] (D : ∀ ℓ, ClopenCoeff T (ZMod 2) →+* (ZMod (N ℓ) → ZMod 2))
    (r : ClopenCrossedProduct T (ZMod 2)) :
    ∀ᶠ ℓ in atTop, cutoffModel (D ℓ) ℓ r = periodicModel (D ℓ) r := by
  choose rad hrad using fun f : ClopenCoeff T (ZMod 2) =>
    exists_radius hXc ((ClopenCoeff.of T (ZMod 2)).symm f)
  refine eventually_atTop.2 ⟨(SkewMonoidAlgebra.support r).sup fun g => rad (SkewMonoidAlgebra.coeff r g),
    fun ℓ hℓ => cutoffModel_eq_of (D ℓ) fun g hg => DependsOnWindow.mono ?_ (hrad _)⟩
  exact le_trans (Finset.le_sup (f := fun g => rad (SkewMonoidAlgebra.coeff r g)) hg) hℓ

/-- A coefficient that is `0` or `1` depends on every window. -/
theorem dependsOnWindow_zero_or_one {ℓ : ℕ} {f : ClopenCoeff T (ZMod 2)} (hf : f = 0 ∨ f = 1) :
    DependsOnWindow T ℓ f := by
  rcases hf with rfl | rfl <;> exact fun _ _ _ => rfl

theorem cutoffModel_single_const {N : ℕ} [NeZero N] (D : ClopenCoeff T (ZMod 2) →+* (ZMod N → ZMod 2))
    (ℓ : ℕ) (g : Multiplicative ℤ) :
    cutoffModel D ℓ (SkewMonoidAlgebra.single g (1 : ClopenCoeff T (ZMod 2))) =
      shiftMatrix (ZMod 2) N (toAdd g) := by
  classical
  rw [cutoffModel_eq_of D fun h _ => dependsOnWindow_zero_or_one (by
    rw [SkewMonoidAlgebra.coeff_single_apply]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl), periodicModel_single, map_one,
    show diagonal (1 : ZMod N → ZMod 2) = 1 from diagonal_one, one_mul]

/-- `φ_ℓ(1) = I` (tex 268). -/
theorem cutoffModel_one {N : ℕ} [NeZero N] (D : ClopenCoeff T (ZMod 2) →+* (ZMod N → ZMod 2)) (ℓ : ℕ) :
    cutoffModel D ℓ 1 = 1 := by
  rw [SkewMonoidAlgebra.one_def, cutoffModel_single_const, toAdd_one, shiftMatrix_zero]

/-- `φ_ℓ(u^j) = P^j`. -/
theorem cutoffModel_unit_zpow {N : ℕ} [NeZero N] (D : ClopenCoeff T (ZMod 2) →+* (ZMod N → ZMod 2))
    (ℓ : ℕ) (j : ℤ) :
    cutoffModel D ℓ ((unit T (ZMod 2) ^ j : (ClopenCrossedProduct T (ZMod 2))ˣ) :
      ClopenCrossedProduct T (ZMod 2)) = shiftMatrix (ZMod 2) N j := by
  rw [Pestov91.CrossedProduct.val_unit_zpow, cutoffModel_single_const, toAdd_ofAdd]

end Cutoff

section Translates

variable {A : Type*}

/-- tex 268: "The shifts $T^ty_\ell$, $0\le t<N_\ell$, are distinct": along a sequence whose least
period is `N`, the cyclic word `t ↦ y(t)` on `ZMod N` has pairwise distinct translates. -/
theorem translates_distinct_of_leastPeriod (y : ℤ → A) {N : ℕ} [NeZero N] (hN : leastPeriod y = N) :
    ∀ t t' : ZMod N, (∀ i : ZMod N, y ((t + i).val : ℕ) = y ((t' + i).val : ℕ)) → t = t' := by
  have hper : ∀ s : ℤ, y (N + s) = y s := by
    intro s
    rw [← hN]
    exact (isPeriodicPt_shift_iff y _).1 (Function.isPeriodicPt_minimalPeriod _ _) s
  have hcong : ∀ u v : ℤ, (u : ZMod N) = (v : ZMod N) → y u = y v := by
    intro u v huv
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub u v N).1 huv
    rw [show v = u + (N : ℤ) * q by linarith]
    exact (periodic_add_mul hper u q).symm
  intro t t' h
  have hall : ∀ s : ℤ, y ((t.val : ℕ) + s) = y ((t'.val : ℕ) + s) := by
    intro s
    have hs := h (s : ZMod N)
    refine (hcong _ _ ?_).trans (hs.trans (hcong _ _ ?_))
    · simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
    · simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
  set d : ℤ := ((t'.val : ℕ) : ℤ) - ((t.val : ℕ) : ℤ)
  have hd : ∀ u : ℤ, y (u + d) = y u := by
    intro u
    have h1 := hall (u - ((t.val : ℕ) : ℤ))
    rw [show ((t.val : ℕ) : ℤ) + (u - ((t.val : ℕ) : ℤ)) = u by ring,
      show ((t'.val : ℕ) : ℤ) + (u - ((t.val : ℕ) : ℤ)) = u + d by ring] at h1
    exact h1.symm
  have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have he : ∀ u : ℤ, y (u + d % N) = y u := by
    intro u
    have h2 := periodic_add_mul hper (u + d % N) (d / N)
    rw [show u + d % N + (N : ℤ) * (d / N) = u + d by rw [add_assoc, Int.emod_add_mul_ediv]] at h2
    rw [← h2]
    exact hd u
  have hzero : d % N = 0 := by
    by_contra hne
    have hlt := Int.emod_lt_of_pos d hNpos
    have hnn := Int.emod_nonneg d hNpos.ne'
    have hpos : 0 < (d % N).toNat := by omega
    have hpp : Function.IsPeriodicPt (shift (1 : ℤ)) (d % N).toNat y := by
      rw [isPeriodicPt_shift_iff]
      intro s
      rw [Int.toNat_of_nonneg hnn, add_comm]
      exact he s
    have hle := hpp.minimalPeriod_le hpos
    have hmin : Function.minimalPeriod (shift (1 : ℤ)) y = N := hN
    omega
  have hdvd : (N : ℤ) ∣ d := Int.dvd_of_emod_eq_zero hzero
  have hcast : (((t.val : ℕ) : ℤ) : ZMod N) = (((t'.val : ℕ) : ℤ) : ZMod N) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).2 hdvd
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hcast

end Translates

section Subshift

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A] [Finite A]

/-- The printed generators `S = {1, u, u⁻¹} ∪ {e_a : a ∈ A}` (tex 243–244). -/
noncomputable def printedGeneratorsSet (S : Subshift A ℤ) : Set (R S) :=
  insert 1 (ringGenerators S)

/-- **Periodic approximations make the subshift ring matricial** (tex 249–271): for an infinite
minimal subshift there are sizes `N_ℓ ≥ 1` and maps `φ_ℓ : R → M_{N_ℓ}(F₂)` with `φ_ℓ(1) = I`, the
images of `{1, u, u⁻¹} ∪ {e_a}` generating `M_{N_ℓ}(F₂)`, and additivity and multiplicativity for
fixed `r, s` and large `ℓ`. -/
theorem exists_periodicMatricial (S : Subshift A ℤ) (hinf : Infinite S.carrier) (hmin : IsMinimal S) :
    ∃ (N : ℕ → ℕ) (φ : ∀ k, R S → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)),
      (∀ k, 0 < N k) ∧ (∀ k, φ k 1 = 1) ∧
      (∀ k, Subring.closure (φ k '' printedGeneratorsSet S) = ⊤) ∧
      ∀ r s : R S, ∀ᶠ k in atTop, φ k (r + s) = φ k r + φ k s ∧ φ k (r * s) = φ k r * φ k s := by
  classical
  obtain ⟨⟨x, hx⟩⟩ := hinf.nonempty
  obtain ⟨m, N, hNz, D, hwords, hform, -, -, hmul⟩ :=
    exists_asymptoticModels S.isClosed S.mapsTo (Set.infinite_coe_iff.1 hinf) hmin (subshiftHomeo S)
      (fun _ => rfl) hx (ZMod 2)
  haveI : ∀ ℓ, NeZero (N ℓ) := hNz
  set e : ∀ ℓ, ZMod (N ℓ) ≃ Fin (N ℓ) := fun ℓ => (ZMod.finEquiv (N ℓ)).toEquiv.symm
  set ψ : ∀ ℓ, Matrix (ZMod (N ℓ)) (ZMod (N ℓ)) (ZMod 2) ≃+* Matrix (Fin (N ℓ)) (Fin (N ℓ)) (ZMod 2) :=
    fun ℓ => reindexRingEquiv (ZMod 2) (e ℓ)
  refine ⟨N, fun ℓ r => ψ ℓ (cutoffModel (D ℓ) ℓ r), fun ℓ => Nat.pos_of_ne_zero (NeZero.ne (N ℓ)),
    fun ℓ => by simp only [cutoffModel_one, map_one], fun ℓ => ?_, fun r s => ?_⟩
  · -- generation (tex 268–270)
    set c : ZMod (N ℓ) → A := fun t => periodicExt x (m ℓ) ((t.val : ℕ) : ℤ)
    have hpt : ∀ t : ℤ, ∃ z : ↥S.carrier, ∀ i : ℤ, |i| ≤ ℓ → z.1 i = periodicExt x (m ℓ) (t + i) := by
      intro t
      have hwin : word (periodicExt x (m ℓ)) (t - ℓ) (2 * ℓ + 1) ∈ language S.carrier (2 * ℓ + 1) := by
        rw [← (hwords ℓ).2.2.2]
        exact ⟨t - ℓ, rfl⟩
      obtain ⟨z0, hz0, hz0w⟩ := hwin
      refine ⟨⟨shift (ℓ : ℤ) z0, S.mapsTo ℓ hz0⟩, fun i hi => ?_⟩
      obtain ⟨hi1, hi2⟩ := abs_le.mp hi
      obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = ℓ + i := ⟨(ℓ + i).toNat, Int.toNat_of_nonneg (by omega)⟩
      have h := congrFun hz0w ⟨j, by omega⟩
      simp only [word_apply, zero_add] at h
      show z0 (ℓ + i) = _
      rw [← hj, h]
      congr 1
      omega
    have hletter : ∀ a : A, cutoffModel (D ℓ) ℓ (coeff (subshiftHomeo S) (ZMod 2) (letterIndicator S a)) =
        letterDiagonal c a := by
      intro a
      have hdep : DependsOnWindow (subshiftHomeo S) ℓ (ClopenCoeff.of _ (ZMod 2) (letterIndicator S a)) :=
        fun y z hyz => by
          show (if y.1 0 = a then (1 : ZMod 2) else 0) = if z.1 0 = a then 1 else 0
          rw [hyz 0 (by simp)]
      rw [coeff_apply, Pestov91.CrossedProduct.C_apply, cutoffModel_eq_of (D ℓ) fun g _ => by
        rw [SkewMonoidAlgebra.coeff_single_apply]
        split_ifs
        · exact hdep
        · exact dependsOnWindow_zero_or_one (Or.inl rfl), periodicModel_single, toAdd_one,
        shiftMatrix_zero, mul_one]
      refine congrArg diagonal (funext fun t => ?_)
      obtain ⟨z, hz⟩ := hpt ((t.val : ℕ) : ℤ)
      have hform' := hform ℓ _ hdep ((t.val : ℕ) : ℤ) z hz
      rw [Int.cast_natCast, ZMod.natCast_zmod_val] at hform'
      rw [hform']
      show (if z.1 0 = a then (1 : ZMod 2) else 0) = if c t = a then 1 else 0
      rw [hz 0 (by simp), add_zero]
    have hdist : ∀ t t' : ZMod (N ℓ), (∀ i : ZMod (N ℓ), c (t + i) = c (t' + i)) → t = t' :=
      translates_distinct_of_leastPeriod (periodicExt x (m ℓ)) (hwords ℓ).2.2.1.symm
    have hsub : periodicGenerators c ⊆ cutoffModel (D ℓ) ℓ '' printedGeneratorsSet S := by
      rintro _ (h | ⟨a, rfl⟩)
      · rcases h with rfl | rfl
        · refine ⟨((unit (subshiftHomeo S) (ZMod 2) : (R S)ˣ) : R S),
            Set.mem_insert_of_mem _ (Or.inl (Or.inl rfl)), ?_⟩
          simpa only [zpow_one] using cutoffModel_unit_zpow (D ℓ) ℓ 1
        · refine ⟨(((unit (subshiftHomeo S) (ZMod 2))⁻¹ : (R S)ˣ) : R S),
            Set.mem_insert_of_mem _ (Or.inl (Or.inr rfl)), ?_⟩
          simpa only [zpow_neg, zpow_one] using cutoffModel_unit_zpow (D ℓ) ℓ (-1)
      · exact ⟨_, Set.mem_insert_of_mem _ (Or.inr ⟨a, rfl⟩), hletter a⟩
    have htop : Subring.closure (cutoffModel (D ℓ) ℓ '' printedGeneratorsSet S) = ⊤ :=
      eq_top_iff.2 ((subring_closure_periodicGenerators_eq_top c hdist).ge.trans (Subring.closure_mono hsub))
    have himg : (fun r => ψ ℓ (cutoffModel (D ℓ) ℓ r)) '' printedGeneratorsSet S =
        ψ ℓ '' (cutoffModel (D ℓ) ℓ '' printedGeneratorsSet S) := (Set.image_image _ _ _).symm
    rw [himg]
    exact subring_closure_image_eq_top (ψ ℓ) htop
  · filter_upwards [eventually_cutoffModel_eq S.isClosed D r, eventually_cutoffModel_eq S.isClosed D s,
      eventually_cutoffModel_eq S.isClosed D (r + s), eventually_cutoffModel_eq S.isClosed D (r * s),
      hmul r s] with ℓ hr hs hrs hrms hm
    refine ⟨?_, ?_⟩
    · show ψ ℓ (cutoffModel (D ℓ) ℓ (r + s)) = ψ ℓ (cutoffModel (D ℓ) ℓ r) + ψ ℓ (cutoffModel (D ℓ) ℓ s)
      rw [hrs, hr, hs, map_add, map_add]
    · show ψ ℓ (cutoffModel (D ℓ) ℓ (r * s)) = ψ ℓ (cutoffModel (D ℓ) ℓ r) * ψ ℓ (cutoffModel (D ℓ) ℓ s)
      rw [hrms, hr, hs, hm, map_mul]

end Subshift

end SimpleKazhdanSofic

end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.translates_distinct_of_leastPeriod
#audit_axioms GroupApproximation.SimpleKazhdanSofic.exists_periodicMatricial
