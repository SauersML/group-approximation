import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Thin sets around a wandering clopen set, and room for commutators

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–315:

> For derived topological full groups, Matui showed by a similar argument that a nontrivial normal
> subgroup meets a simple union of products of alternating groups on towers
> [Matui, Lemma 3.4 and Theorem 4.9].

This file is the first step towards `D ≤ A` (`D = ⁅[[T]], [[T]]⁆`, `A = alternatingFullGroup T`),
following the Kakutani–Rokhlin arguments of Matui (Internat. J. Math. 2006, Lemma 3.4 and §4) and
Grigorchuk–Medynets (2014, §3).  Let `Y` be a clopen set with `Y ∩ T^j Y = ∅` for `0 < |j| ≤ L`
(`Wandering T Y L`), and let `thin T Y K = ⋃_{|k| ≤ K} T^{-k} Y` be the points within `K` steps of
`Y`.

* `exists_wandering`: for an infinite minimal system such a nonempty `Y` exists for every `L`;
* `isThreeCycleDatum_thin`: if `6K + 2 ≤ L`, the sets `Z`, `T^N Z`, `T^{2N} Z` are pairwise disjoint
  for `Z = thin T Y K` and `N = 2K + 1`;
* `commutatorElement_mem_of_supportedIn_thin`: then `⁅a, b⁆ ∈ A` for all `a, b ∈ [[T]]` supported in
  `Z`.  The three-cycle along `T^N` on `Z` lies in `A` and displaces `Z`, so this is the
  displacement step `commutatorElement_mem_of_displaced`.
-/

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

open scoped commutatorElement

variable {X : Type*}

/-- `Y` does not meet its translates `T^j Y` for `0 < |j| ≤ L`. -/
def Wandering [TopologicalSpace X] (T : X ≃ₜ X) (Y : Set X) (L : ℕ) : Prop :=
  ∀ j : ℤ, j ≠ 0 → -(L : ℤ) ≤ j → j ≤ L → ∀ y ∈ Y, (T ^ j) y ∉ Y

theorem Wandering.mono [TopologicalSpace X] {T : X ≃ₜ X} {Y : Set X} {L L' : ℕ}
    (h : Wandering T Y L) (hL : L' ≤ L) : Wandering T Y L' :=
  fun j hj h1 h2 => h j hj (by omega) (by omega)

/-- For an infinite minimal system every point has clopen neighbourhoods wandering up to `L`. -/
theorem exists_wandering [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallySeparatedSpace X] [Infinite X] (T : X ≃ₜ X)
    (hmin : SimpleKazhdanSofic.IsMinimalSystem T) (L : ℕ) :
    ∃ Y : Set X, IsClopen Y ∧ Y.Nonempty ∧ Wandering T Y L := by
  have hfree : ∀ j : ℤ, j ≠ 0 → ∀ y : X, (T ^ j) y ≠ y := fun j hj y =>
    SimpleKazhdanSofic.zpow_apply_ne_self T hmin hj y
  obtain ⟨y⟩ : Nonempty X := inferInstance
  obtain ⟨U, hU, hyU, hdis⟩ :=
    SimpleKazhdanSofic.exists_clopen_nbhd_disjoint_translates T hfree L y
  exact ⟨U, hU, ⟨y, hyU⟩, fun j hj h1 h2 x hx =>
    notMem_of_disjoint_zpow (hdis j hj (abs_le.mpr ⟨h1, h2⟩)) hx⟩

/-- The thin set `⋃_{|k| ≤ M} T^{-k} Y` of points within `M` steps of `Y`. -/
def thin [TopologicalSpace X] (T : X ≃ₜ X) (Y : Set X) (M : ℕ) : Set X :=
  ⋃ k ∈ Finset.Icc (-(M : ℤ)) M, ⇑(T ^ k) ⁻¹' Y

theorem mem_thin [TopologicalSpace X] {T : X ≃ₜ X} {Y : Set X} {M : ℕ} {x : X} :
    x ∈ thin T Y M ↔ ∃ k : ℤ, -(M : ℤ) ≤ k ∧ k ≤ M ∧ (T ^ k) x ∈ Y := by
  constructor
  · intro hx
    obtain ⟨k, hk, hkx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    exact ⟨k, h1, h2, hkx⟩
  · rintro ⟨k, h1, h2, hkx⟩
    exact Set.mem_iUnion₂.mpr ⟨k, Finset.mem_Icc.mpr ⟨h1, h2⟩, hkx⟩

theorem mem_thin_of [TopologicalSpace X] {T : X ≃ₜ X} {Y : Set X} {M : ℕ} {x : X} {k : ℤ}
    (h1 : -(M : ℤ) ≤ k) (h2 : k ≤ M) (hx : (T ^ k) x ∈ Y) : x ∈ thin T Y M :=
  mem_thin.mpr ⟨k, h1, h2, hx⟩

theorem isClopen_thin [TopologicalSpace X] {T : X ≃ₜ X} {Y : Set X} (hY : IsClopen Y) (M : ℕ) :
    IsClopen (thin T Y M) :=
  isClopen_biUnion_finset fun k _ => hY.preimage (T ^ k).continuous

theorem thin_mono [TopologicalSpace X] {T : X ≃ₜ X} {Y : Set X} {M M' : ℕ} (h : M ≤ M') :
    thin T Y M ⊆ thin T Y M' := fun x hx => by
  obtain ⟨k, h1, h2, hk⟩ := mem_thin.mp hx
  exact mem_thin_of (by omega) (by omega) hk

theorem self_mem_thin [TopologicalSpace X] {T : X ≃ₜ X} {Y : Set X} {y : X} (hy : y ∈ Y)
    (M : ℕ) : y ∈ thin T Y M :=
  mem_thin_of (k := 0) (by omega) (by omega) (by rwa [zpow_zero, Homeomorph.one_apply])

/-- A translate by `2K < d ≤ L - 2K` moves `thin T Y K` off itself. -/
theorem zpow_apply_notMem_thin [TopologicalSpace X] {T : X ≃ₜ X} {Y : Set X} {L K : ℕ}
    (hY : Wandering T Y L) {d : ℤ} (hd : 2 * (K : ℤ) < d) (hdL : d + 2 * (K : ℤ) ≤ L) {x : X}
    (hx : x ∈ thin T Y K) : (T ^ d) x ∉ thin T Y K := by
  intro hdx
  obtain ⟨k, hk1, hk2, hkx⟩ := mem_thin.mp hx
  obtain ⟨k', hk1', hk2', hkx'⟩ := mem_thin.mp hdx
  have e : (T ^ (k' + d - k)) ((T ^ k) x) = (T ^ k') ((T ^ d) x) := by
    rw [zpow_apply_zpow_apply, zpow_apply_zpow_apply, show k' + d - k + k = k' + d by ring]
  have hmem : (T ^ (k' + d - k)) ((T ^ k) x) ∈ Y := by
    rw [e]
    exact hkx'
  exact hY (k' + d - k) (by omega) (by omega) (by omega) _ hkx hmem

theorem toEquiv_zpow_mem_fullGroup [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (T : X ≃ₜ X) (d : ℤ) : (T ^ d).toEquiv ∈ fullGroup T :=
  mem_fullGroup.mpr ⟨fun _ => d, continuous_const, fun _ => rfl⟩

/-- `Z`, `T^N Z` and `T^{2N} Z` are pairwise disjoint for `Z = thin T Y K`, `N = 2K + 1`. -/
theorem isThreeCycleDatum_thin [TopologicalSpace X] {T : X ≃ₜ X} {Y : Set X} {L K : ℕ}
    (hY : Wandering T Y L) (hKL : 6 * K + 2 ≤ L) :
    IsThreeCycleDatum (T ^ ((2 * K + 1 : ℕ) : ℤ)).toEquiv (thin T Y K) := by
  refine ⟨fun x hx =>
    zpow_apply_notMem_thin hY (d := ((2 * K + 1 : ℕ) : ℤ)) (by omega) (by omega) hx,
    fun x hx => ?_⟩
  have e : (T ^ ((2 * K + 1 : ℕ) : ℤ)).toEquiv ((T ^ ((2 * K + 1 : ℕ) : ℤ)).toEquiv x) =
      (T ^ (((2 * K + 1 : ℕ) : ℤ) + ((2 * K + 1 : ℕ) : ℤ))) x :=
    zpow_apply_zpow_apply T _ _ x
  rw [e]
  exact zpow_apply_notMem_thin hY (d := ((2 * K + 1 : ℕ) : ℤ) + ((2 * K + 1 : ℕ) : ℤ))
    (by omega) (by omega) hx

/-- **Room on a thin set** (Matui 2006, Lemma 3.4; tex l.307–315): commutators of elements of
`[[T]]` supported in `thin T Y K` lie in `alternatingFullGroup T` when `6K + 2 ≤ L`. -/
theorem commutatorElement_mem_of_supportedIn_thin [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {T : X ≃ₜ X} {Y : Set X} (hYc : IsClopen Y) {L K : ℕ} (hY : Wandering T Y L)
    (hKL : 6 * K + 2 ≤ L) {a b : Equiv.Perm X} (ha : a ∈ fullGroup T) (hb : b ∈ fullGroup T)
    (haZ : HydeLodha.SupportedIn a (thin T Y K)) (hbZ : HydeLodha.SupportedIn b (thin T Y K)) :
    ⁅a, b⁆ ∈ alternatingFullGroup T := by
  have hdat := isThreeCycleDatum_thin hY hKL
  refine commutatorElement_mem_of_displaced (L := fullGroup T) (N := alternatingFullGroup T)
    (fun n hn g hg => conj_mem_alternatingFullGroup hg hn)
    (threeCycle_mem_alternatingFullGroup (toEquiv_zpow_mem_fullGroup T _) (isClopen_thin hYc K)
      hdat) (fun y hy => ?_) ha hb haZ hbZ
  rw [threeCycle_apply_of_mem hdat hy]
  exact hdat.1 y hy

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.exists_wandering
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.commutatorElement_mem_of_supportedIn_thin
