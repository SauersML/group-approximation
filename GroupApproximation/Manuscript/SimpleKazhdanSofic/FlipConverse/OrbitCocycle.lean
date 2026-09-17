import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.IntegerPaths
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.FullGroup

/-!
# Flip converse, part 3: orbit cocycles and the conjugacy map

Let `X` be compact Hausdorff and `T, R` aperiodic homeomorphisms with `T^k ∈ [[R]]` and
`R^j ∈ [[T]]` for all `j, k`, witnessed by continuous cocycles

* `c k : X → ℤ` with `T^k x = R^{c k x} x`, and
* `d j : X → ℤ` with `R^j x = T^{d j x} x`.

## Cocycle identities

By aperiodicity of `R`, exponents are determined by the points they produce, so
`c (k+1) x = c k (T x) + c 1 x` (`cocycle_add`) and `c (k+1) x = c 1 (T^k x) + c k x`
(`cocycle_add'`).  For fixed `x`, `k ↦ c k x` is injective (aperiodicity of `T`,
`cocycle_injective`) and surjective (`c (d j x) x = j`, `cocycle_surjective`).

## The conjugacy (`exists_conj_of_positiveWindow`)

Suppose moreover that `|c 1 x| ≤ N` for all `x` and that each path `σ_x = c (·) x` is a positive
window of half-width `L` (`IsPositiveWindow`).  Put
`a x = windowCount σ_x L 0 - L` and `φ x = R^{a x} x`.

* `a` is continuous: it is a finite sum of the continuous integer functions
  `x ↦ above 0 (c (i - L) x)`.  Hence `φ` is continuous (`continuous_hpow_apply`).
* Since `σ_{T x} k = σ_x (k+1) - σ_x 1`, `windowCount_cocycle` gives
  `a (T x) + c 1 x = a x + 1`, so
  `φ (T x) = R^{a (T x)} R^{c 1 x} x = R^{a x + 1} x = R (φ x)`.
* `φ` is surjective: `φ (T^{-a y} y) = R^{-a y} φ y = y`.
* `φ` is injective: if `φ x = φ y` then `y = R^j x = T^k x` for `k = d j x`, and
  `φ x = φ y = R^k φ x`, so `k = 0` and `y = x`.

A continuous bijection of a compact space onto a Hausdorff space is a homeomorphism, so `φ`
conjugates `T` to `R`.

Also: `minimal_invariant_closed` (a closed `T`-invariant set is empty or everything when `T` is
minimal) and `exists_bound_of_continuous` (continuous integer functions on compact spaces are
bounded).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

theorem exists_bound_of_continuous [CompactSpace X] {f : X → ℤ} (hf : Continuous f) :
    ∃ B : ℤ, 0 ≤ B ∧ ∀ x, -B ≤ f x ∧ f x ≤ B := by
  have hfin : (Set.range f).Finite := (isCompact_range hf).finite_of_discrete
  obtain ⟨U, hU⟩ := hfin.bddAbove
  obtain ⟨D, hD⟩ := hfin.bddBelow
  refine ⟨max (max U (-D)) 0, le_max_right _ _, fun x => ?_⟩
  have h1 : f x ≤ U := hU (Set.mem_range_self x)
  have h2 : D ≤ f x := hD (Set.mem_range_self x)
  have hm1 := le_max_left (max U (-D)) 0
  have hm3 := le_max_left U (-D)
  have hm4 := le_max_right U (-D)
  constructor <;> omega

section Cocycle

variable {T R : X ≃ₜ X} {c d : ℤ → X → ℤ}

theorem cocycle_add (hRa : IsAperiodic R) (hc : ∀ k x, (T ^ k) x = (R ^ c k x) x)
    (k : ℤ) (x : X) : c (k + 1) x = c k (T x) + c 1 x := by
  refine zpow_apply_injective hRa (x := x) ?_
  rw [← hc (k + 1) x, homeoPow_add T k 1 x, homeoPow_add R (c k (T x)) (c 1 x) x, ← hc 1 x,
    homeoPow_one T x, hc k (T x)]

theorem cocycle_add' (hRa : IsAperiodic R) (hc : ∀ k x, (T ^ k) x = (R ^ c k x) x)
    (k : ℤ) (x : X) : c (k + 1) x = c 1 ((T ^ k) x) + c k x := by
  refine zpow_apply_injective hRa (x := x) ?_
  rw [← hc (k + 1) x, show k + 1 = 1 + k by omega, homeoPow_add T 1 k x,
    homeoPow_add R (c 1 ((T ^ k) x)) (c k x) x, ← hc k x, ← hc 1 ((T ^ k) x)]

theorem cocycle_injective (hTa : IsAperiodic T) (hc : ∀ k x, (T ^ k) x = (R ^ c k x) x)
    (x : X) : Function.Injective fun k => c k x := by
  intro a b hab
  have hab' : c a x = c b x := hab
  refine zpow_apply_injective hTa (x := x) ?_
  rw [hc a x, hc b x, hab']

theorem cocycle_surjective (hRa : IsAperiodic R) (hc : ∀ k x, (T ^ k) x = (R ^ c k x) x)
    (hd : ∀ j x, (R ^ j) x = (T ^ d j x) x) (x : X) : Function.Surjective fun k => c k x := by
  intro j
  refine ⟨d j x, ?_⟩
  show c (d j x) x = j
  refine zpow_apply_injective hRa (x := x) ?_
  rw [← hc (d j x) x, ← hd j x]

end Cocycle

theorem minimal_invariant_closed {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {Q : Set X}
    (hQ : IsClosed Q) (hinv : ∀ x, x ∈ Q ↔ T x ∈ Q) : (∀ x, x ∈ Q) ∨ ∀ x, x ∉ Q := by
  by_cases hex : ∃ x, x ∈ Q
  · left
    obtain ⟨x, hx⟩ := hex
    have horb : ∀ n : ℤ, (T ^ n) x ∈ Q := by
      intro n
      induction n with
      | zero => rw [homeoPow_zero]; exact hx
      | succ i ih =>
        rw [show (i : ℤ) + 1 = 1 + (i : ℤ) by omega, homeoPow_add T 1 (i : ℤ), homeoPow_one]
        exact (hinv _).1 ih
      | pred i ih =>
        rw [show -(i : ℤ) - 1 = -1 + -(i : ℤ) by omega, homeoPow_add T (-1) (-(i : ℤ)),
          homeoPow_neg_one]
        refine (hinv _).2 ?_
        rw [Homeomorph.apply_symm_apply]
        exact ih
    have hsub : closure (Set.range fun n : ℤ => (T ^ n) x) ⊆ Q :=
      closure_minimal (by rintro _ ⟨n, rfl⟩; exact horb n) hQ
    intro y
    have hy : y ∈ closure (Set.range fun n : ℤ => (T ^ n) x) := by
      rw [(hT x).closure_eq]
      exact Set.mem_univ y
    exact hsub hy
  · right
    intro x hx
    exact hex ⟨x, hx⟩

theorem exists_conj_of_positiveWindow [CompactSpace X] [T2Space X] {T R : X ≃ₜ X}
    (hRa : IsAperiodic R) {c d : ℤ → X → ℤ} (hTa : IsAperiodic T)
    (hcont : ∀ k, Continuous (c k)) (hc : ∀ k x, (T ^ k) x = (R ^ c k x) x)
    (hd : ∀ j x, (R ^ j) x = (T ^ d j x) x) {N : ℤ} {L : ℕ}
    (h1 : ∀ x, -N ≤ c 1 x ∧ c 1 x ≤ N) (hw : ∀ x, IsPositiveWindow (fun k => c k x) N L) :
    ∃ φ : X ≃ₜ X, ∀ x, φ (T x) = R (φ x) := by
  obtain ⟨a, ha⟩ : ∃ a : X → ℤ, ∀ x, a x = windowCount (fun k => c k x) L 0 - L :=
    ⟨fun x => windowCount (fun k => c k x) L 0 - L, fun _ => rfl⟩
  have hacont : Continuous a := by
    rw [show a = fun x => windowCount (fun k => c k x) L 0 - L from funext ha]
    show Continuous fun x => (∑ i ∈ Finset.range (2 * L), above 0 (c ((i : ℤ) - L) x)) - (L : ℤ)
    exact (continuous_finsetSum (f := fun (i : ℕ) (x : X) => above 0 (c ((i : ℤ) - L) x))
      (Finset.range (2 * L)) fun i _ =>
        (continuous_of_discreteTopology (f := above 0)).comp (hcont ((i : ℤ) - L))).sub
      continuous_const
  have hkey : ∀ x, a (T x) + c 1 x = 1 + a x := by
    intro x
    have hcc := windowCount_cocycle (σ := fun k => c k x) (τ := fun k => c k (T x))
      (cocycle_injective hTa hc x) (cocycle_surjective hRa hc hd x) (hw x) (h1 x)
      (fun k => by
        have := cocycle_add hRa hc k x
        show c k (T x) = c (k + 1) x - c 1 x
        omega)
    beta_reduce at hcc
    rw [ha, ha]
    omega
  obtain ⟨φ, hφ⟩ : ∃ φ : X → X, ∀ x, φ x = (R ^ a x) x := ⟨fun x => (R ^ a x) x, fun _ => rfl⟩
  have hφcont : Continuous φ := by
    rw [show φ = fun x => (R ^ a x) x from funext hφ]
    exact continuous_hpow_apply R hacont
  have hsemi : ∀ x, φ (T x) = R (φ x) := by
    intro x
    rw [hφ, hφ]
    calc (R ^ a (T x)) (T x) = (R ^ a (T x)) ((R ^ c 1 x) x) := by
          rw [← hc 1 x, homeoPow_one]
      _ = (R ^ (a (T x) + c 1 x)) x := (homeoPow_add _ _ _ _).symm
      _ = (R ^ (1 + a x)) x := by rw [hkey x]
      _ = R ((R ^ a x) x) := by rw [homeoPow_add, homeoPow_one]
  have hsurj : Function.Surjective φ := by
    intro y
    refine ⟨(T ^ (-a y)) y, ?_⟩
    rw [apply_hpow_of_semiconj φ hsemi, hφ y, ← homeoPow_add, neg_add_cancel, homeoPow_zero]
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hy : (R ^ (-a y + a x)) x = y := by
      rw [homeoPow_add, ← hφ x, hxy, hφ y, ← homeoPow_add, neg_add_cancel, homeoPow_zero]
    rw [hd] at hy
    have hk : (R ^ d (-a y + a x) x) (φ x) = φ x := by
      rw [← apply_hpow_of_semiconj φ hsemi, hy, hxy]
    have hk0 := hRa _ _ hk
    rw [hk0, homeoPow_zero] at hy
    exact hy
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φ ⟨hinj, hsurj⟩) hφcont,
    hsemi⟩

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
