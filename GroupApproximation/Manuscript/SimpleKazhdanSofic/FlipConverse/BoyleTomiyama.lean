import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.OrbitCocycle

/-!
# Flip converse, part 4: the Boyle–Tomiyama step

**Theorem** (`exists_flip_of_mem_fullGroup`).  Let `X` be compact Hausdorff, `T` minimal and
aperiodic, `R` aperiodic, with `T ∈ [[R]]` and `R ∈ [[T]]`.  Then `T` is topologically conjugate
to `R` or to `R⁻¹` by a homeomorphism of `X`.

## Proof

Since full groups are subgroups, `T^k ∈ [[R]]` and `R^j ∈ [[T]]` for all `j, k`; choose continuous
cocycles `c k, d j : X → ℤ` with `T^k x = R^{c k x} x` and `R^j x = T^{d j x} x`.

1. *Bounds.*  By compactness `|c 1 x| ≤ N` for all `x`, and `|d j x| ≤ B j`.  Put
   `M = ∑_{|j| ≤ N} B j` and choose `L > M`.
2. *Paths.*  For fixed `x`, `σ_x = c (·) x : ℤ → ℤ` is a bijection (aperiodicity of `T` and `R`)
   with steps `|σ_x (k+1) - σ_x k| = |c 1 (T^k x)| ≤ N`.
3. *Outside the window the path is outside `[-N, N]`.*  Since `d (c k x) x = k`, if
   `|c k x| ≤ N` then `|k| ≤ B (c k x) ≤ M < L`.
4. *Orientation.*  By `orientation` (a pigeonhole count on the window `(-L, L)`), `σ_x` is a
   positive window of half-width `L` or its negative is.
5. *The orientation is constant.*  `Q = {x | N < c L x}` is closed (`c L` is continuous and
   integer-valued) and `T`-invariant: from `c (L+1) x = c L (T x) + c 1 x` and `|c 1 x| ≤ N`,
   the two orientations of `x` and of `T x` cannot differ.  By minimality `Q = X` or `Q = ∅`.
6. *Conclusion.*  If `Q = X`, every `σ_x` is a positive window and
   `exists_conj_of_positiveWindow` gives `φ ∘ T = R ∘ φ`.  If `Q = ∅`, every `-σ_x` is a
   positive window; the cocycles `-c k` and `d (-j)` witness `T ∈ [[R⁻¹]]`, `R⁻¹ ∈ [[T]]`, and the
   same lemma gives `φ ∘ T = R⁻¹ ∘ φ`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

theorem exists_flip_of_mem_fullGroup [CompactSpace X] [T2Space X] {T R : X ≃ₜ X}
    (hTmin : IsMinimalHomeo T) (hTa : IsAperiodic T) (hRa : IsAperiodic R)
    (hTR : T ∈ topologicalFullGroup R) (hRT : R ∈ topologicalFullGroup T) :
    ∃ φ : X ≃ₜ X, (∀ x, φ (T x) = R (φ x)) ∨ ∀ x, φ (T x) = R.symm (φ x) := by
  have hcex : ∀ k : ℤ, ∃ n : X → ℤ, Continuous n ∧ ∀ x, (T ^ k) x = (R ^ n x) x :=
    fun k => mem_topologicalFullGroup.1 (zpow_mem hTR k)
  have hdex : ∀ j : ℤ, ∃ n : X → ℤ, Continuous n ∧ ∀ x, (R ^ j) x = (T ^ n x) x :=
    fun j => mem_topologicalFullGroup.1 (zpow_mem hRT j)
  choose c hcont hc using hcex
  choose d hdcont hd using hdex
  obtain ⟨N, hN, h1⟩ := exists_bound_of_continuous (hcont 1)
  choose B hB0 hB using fun j : ℤ => exists_bound_of_continuous (hdcont j)
  have hMB : ∀ j : ℤ, -N ≤ j → j ≤ N → B j ≤ ∑ i ∈ Finset.Icc (-N) N, B i := fun j hj₁ hj₂ =>
    Finset.single_le_sum (f := B) (fun i _ => hB0 i) (Finset.mem_Icc.2 ⟨hj₁, hj₂⟩)
  obtain ⟨L, hL⟩ := exists_nat_gt (∑ i ∈ Finset.Icc (-N) N, B i)
  have hdk : ∀ k x, d (c k x) x = k := fun k x =>
    zpow_apply_injective hTa (x := x) (by rw [← hd (c k x) x, ← hc k x])
  have hout : ∀ x k, ((L : ℤ) ≤ k ∨ k ≤ -(L : ℤ)) → N < c k x ∨ c k x < -N := by
    intro x k hk
    by_contra hcon
    have hj₂ : c k x ≤ N := not_lt.1 fun h => hcon (Or.inl h)
    have hj₁ : -N ≤ c k x := not_lt.1 fun h => hcon (Or.inr h)
    have hbd := hB (c k x) x
    have hm := hMB (c k x) hj₁ hj₂
    rw [hdk k x] at hbd
    omega
  have hstep : ∀ x k, c (k + 1) x - c k x ≤ N ∧ c k x - c (k + 1) x ≤ N := by
    intro x k
    have hadd := cocycle_add' hRa hc k x
    have hb := h1 ((T ^ k) x)
    constructor <;> omega
  have hor : ∀ x, IsPositiveWindow (fun k => c k x) N L ∨
      IsPositiveWindow (fun k => -c k x) N L := fun x =>
    orientation (σ := fun k => c k x) (cocycle_surjective hRa hc hd x) hN (hstep x) (hout x)
  have hQ : IsClosed {x : X | N < c (L : ℤ) x} :=
    (isClosed_discrete {v : ℤ | N < v}).preimage (hcont (L : ℤ))
  have hinv : ∀ x, x ∈ {x : X | N < c (L : ℤ) x} ↔ T x ∈ {x : X | N < c (L : ℤ) x} := by
    intro x
    show N < c (L : ℤ) x ↔ N < c (L : ℤ) (T x)
    have hadd := cocycle_add hRa hc (L : ℤ) x
    have hb := h1 x
    have hx : (N < c (L : ℤ) x ∧ N < c ((L : ℤ) + 1) x) ∨
        (N < -c (L : ℤ) x ∧ N < -c ((L : ℤ) + 1) x) := by
      rcases hor x with hp | hn
      · exact Or.inl ⟨hp.1 (L : ℤ) le_rfl, hp.1 ((L : ℤ) + 1) (by omega)⟩
      · exact Or.inr ⟨hn.1 (L : ℤ) le_rfl, hn.1 ((L : ℤ) + 1) (by omega)⟩
    have hy : N < c (L : ℤ) (T x) ∨ N < -c (L : ℤ) (T x) := by
      rcases hor (T x) with hp | hn
      · exact Or.inl (hp.1 (L : ℤ) le_rfl)
      · exact Or.inr (hn.1 (L : ℤ) le_rfl)
    constructor
    · intro hq
      omega
    · intro hq
      omega
  rcases minimal_invariant_closed hTmin hQ hinv with hall | hnone
  · have hw : ∀ x, IsPositiveWindow (fun k => c k x) N L := by
      intro x
      rcases hor x with hp | hn
      · exact hp
      · exfalso
        have h2 : N < -c (L : ℤ) x := hn.1 (L : ℤ) le_rfl
        have h3 : N < c (L : ℤ) x := hall x
        omega
    obtain ⟨φ, hφ⟩ := exists_conj_of_positiveWindow hRa hTa hcont hc hd h1 hw
    exact ⟨φ, Or.inl hφ⟩
  · have hw : ∀ x, IsPositiveWindow (fun k => -c k x) N L := by
      intro x
      rcases hor x with hp | hn
      · exfalso
        exact hnone x (hp.1 (L : ℤ) le_rfl)
      · exact hn
    have hRa' : IsAperiodic R⁻¹ := by
      intro x p hp
      rw [inv_zpow'] at hp
      have hp0 := hRa x _ hp
      omega
    have hc' : ∀ k x, (T ^ k) x = (R⁻¹ ^ (-c k x)) x := by
      intro k x
      rw [inv_zpow', neg_neg]
      exact hc k x
    have hd' : ∀ j x, (R⁻¹ ^ j) x = (T ^ d (-j) x) x := by
      intro j x
      rw [inv_zpow']
      exact hd (-j) x
    have h1' : ∀ x, -N ≤ -c 1 x ∧ -c 1 x ≤ N := by
      intro x
      have hb := h1 x
      constructor <;> omega
    obtain ⟨φ, hφ⟩ := exists_conj_of_positiveWindow (c := fun k x => -c k x)
      (d := fun j x => d (-j) x) hRa' hTa (fun k => (hcont k).neg) hc' hd' h1' hw
    exact ⟨φ, Or.inr fun x => by rw [hφ x, Homeomorph.inv_apply]⟩

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
