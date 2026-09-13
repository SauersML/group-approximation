import GroupApproximation.Dynamics.ChainRecurrence
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Clopen
import Mathlib.Topology.Homeomorph.Defs

/-!
# Fresh return coordinates for `lem:involution-localization`

`non_mf_groups_exist.tex`, proof of `lem:involution-localization` (tex 1673–1686):

> Let $K\subset X\setminus Y$ contain the sources and ranges of a finite partial-shift description of
> $F$, and cover $K$ by $m$ wandering clopen sets.  Each orbit meets $K$ at most $m$ times.  If $H$
> bounds the return gaps, add arrows from every point of $K$ to its first $2m$ strictly future returns
> to $C$.  Their displacements are bounded by $2mH$ and have finitely many clopen domains.  [...]
> Each generated class contains an original point and its $2m$ distinct return points.  At least $m$
> of the latter lie in $C\setminus K$, enough to match every original coordinate to a fresh section
> coordinate.  Swap the matched pairs and fix the other coordinates.  The finite clopen partition
> makes these choices constant on each representative cell.

This module proves the matching with its clopen cells, for a homeomorphism `T` of any topological
space, a clopen `K` covered by `m` wandering clopen sets `W i`, and a clopen `C` that every point
reaches within `H` positive steps.

* `card_returns_ge`: a point has at least `r` returns to `C` at times in `[1, rH]`;
* `card_visits_le`: an orbit meets `K` at at most `m` times ("each orbit meets $K$ at most $m$
  times");
* `exists_returnPlacement`: clopen cells `A j h ⊆ K` and exponents `0 < h ≤ 2mH` such that the cells
  partition `K` and the fresh coordinates `T^h(A j h) ⊆ C ∖ K` are pairwise disjoint.

Construction order.  The printed proof reads the cells off the matrix-block construction of
`lem:transient-matrices` and matches inside each class.  Here `K` is cut into the pieces
`K ∩ W j ∖ ⋃_{i<j} W i`, which are matched one after another: a point of the `j`-th piece is sent
to the first of its first `2m` returns that lies in `C ∖ K` and outside the fresh coordinates
already used.  At most `m` returns lie in `K` and at most `j < m` in used coordinates, so one is
left.  The exponent is locally constant because `C`, `K` and the used coordinates are clopen.
-/

namespace GroupApproximation

namespace Dynamics

section Orbit

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)

/-- `Homeomorph.toEquiv` as a monoid homomorphism into `Equiv.Perm X`. -/
def homeomorphToPerm : (X ≃ₜ X) →* Equiv.Perm X where
  toFun h := h.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toEquiv_zpow_apply (j : ℤ) (x : X) : (T.toEquiv ^ j) x = (T ^ j) x :=
  (congrArg (fun p : Equiv.Perm X => p x) (map_zpow (homeomorphToPerm (X := X)) T j)).symm

theorem zpow_apply_zpow_apply (a b : ℤ) (x : X) : (T ^ a) ((T ^ b) x) = (T ^ (a + b)) x := by
  rw [zpow_add, Homeomorph.mul_apply]

/-- From `T^a x = T^b y`, `T^{b-a} y = x`. -/
theorem zpow_sub_apply_of_eq {a b : ℤ} {x y : X} (h : (T ^ a) x = (T ^ b) y) :
    (T ^ (b - a)) y = x := by
  have h2 : (T ^ (-a)) ((T ^ a) x) = (T ^ (-a)) ((T ^ b) y) := by rw [h]
  rwa [zpow_apply_zpow_apply, zpow_apply_zpow_apply, neg_add_cancel, zpow_zero,
    Homeomorph.one_apply, neg_add_eq_sub, eq_comm] at h2

theorem isClopen_zpow_image (g : ℤ) {A : Set X} (hA : IsClopen A) :
    IsClopen (⇑(T ^ g) '' A) := by
  rw [(T ^ g).image_eq_preimage_symm]
  exact hA.preimage (T ^ g).symm.continuous

/-- A point of a wandering set meets it only at time zero. -/
theorem eq_zero_of_isWandering {W : Set X} (hW : IsWandering T.toEquiv W) {y : X} {d : ℤ}
    (hy : y ∈ W) (hdy : (T ^ d) y ∈ W) : d = 0 := by
  by_contra hd
  refine Set.disjoint_left.1 (hW hd) ⟨y, hy, toEquiv_zpow_apply T d y⟩ ⟨(T ^ d) y, hdy, ?_⟩
  rw [zpow_zero, Equiv.Perm.one_apply]

end Orbit

section Pieces

variable {X : Type*} {m : ℕ} (W : Fin m → Set X) (K : Set X)

/-- The `j`-th piece `K ∩ W j ∖ ⋃_{i<j} W i` of the cover of `K` by the sets `W i`. -/
def coverPiece (j : Fin m) : Set X :=
  (K ∩ W j) \ ⋃ i ∈ Finset.univ.filter (· < j), W i

theorem coverPiece_subset (j : Fin m) : coverPiece W K j ⊆ K ∩ W j :=
  Set.sdiff_subset

theorem isClopen_coverPiece [TopologicalSpace X] (hK : IsClopen K) (hW : ∀ i, IsClopen (W i))
    (j : Fin m) : IsClopen (coverPiece W K j) :=
  (hK.inter (hW j)).diff (isClopen_biUnion_finset fun i _ => hW i)

theorem disjoint_coverPiece {i j : Fin m} (hij : i ≠ j) :
    Disjoint (coverPiece W K i) (coverPiece W K j) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨_, hxi⟩, hni⟩ ⟨⟨_, hxj⟩, hnj⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact hnj (Set.mem_iUnion₂.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, hxi⟩)
  · exact hni (Set.mem_iUnion₂.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, hxj⟩)

theorem exists_mem_coverPiece (hKW : K ⊆ ⋃ i, W i) {x : X} (hx : x ∈ K) :
    ∃ j, x ∈ coverPiece W K j := by
  classical
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hKW hx)
  have hne : (Finset.univ.filter fun i => x ∈ W i).Nonempty :=
    ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  refine ⟨(Finset.univ.filter fun i => x ∈ W i).min' hne,
    ⟨hx, (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2⟩, ?_⟩
  simp only [Set.mem_iUnion, not_exists]
  intro i' hi' hxi'
  exact absurd (Finset.min'_le _ i' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxi'⟩))
    (not_le.2 (Finset.mem_filter.1 hi').2)

end Pieces

section Placement

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) {m : ℕ} (W : Fin m → Set X)
  (K C : Set X) (H : ℕ)

/-- A placement of the pieces `j < n`: clopen cells `A j h` of each piece, with exponents
`0 < h ≤ 2mH`, whose fresh coordinates `T^h(A j h) ⊆ C ∖ K` are pairwise disjoint. -/
structure IsPlacement (n : ℕ) (A : Fin m → ℕ → Set X) : Prop where
  isClopen : ∀ j h, IsClopen (A j h)
  subset : ∀ j h, A j h ⊆ coverPiece W K j
  bounds : ∀ j h, (A j h).Nonempty → (j : ℕ) < n ∧ 0 < h ∧ h ≤ 2 * m * H
  cover : ∀ j : Fin m, (j : ℕ) < n → ∀ x ∈ coverPiece W K j, ∃ h, x ∈ A j h
  disjoint_same : ∀ j h h', h ≠ h' → Disjoint (A j h) (A j h')
  target : ∀ j (h : ℕ), ⇑(T ^ (h : ℤ)) '' A j h ⊆ C \ K
  disjoint_target : ∀ j (h : ℕ) j' (h' : ℕ), (j, h) ≠ (j', h') →
    Disjoint (⇑(T ^ (h : ℤ)) '' A j h) (⇑(T ^ (h' : ℤ)) '' A j' h')

theorem isPlacement_zero : IsPlacement T W K C H 0 fun _ _ => ∅ where
  isClopen _ _ := isClopen_empty
  subset _ _ := Set.empty_subset _
  bounds _ _ h := absurd h Set.not_nonempty_empty
  cover _ hj := absurd hj (Nat.not_lt_zero _)
  disjoint_same _ _ _ _ := by simp
  target _ _ := by simp
  disjoint_target _ _ _ _ _ := by simp

open Classical in
/-- "If $H$ bounds the return gaps": a point has at least `r` returns to `C` at times in
`[1, rH]`. -/
theorem card_returns_ge (hret : ∀ x, ∃ h : ℕ, 0 < h ∧ h ≤ H ∧ (T ^ (h : ℤ)) x ∈ C) (x : X)
    (r : ℕ) : r ≤ ((Finset.Icc 1 (r * H)).filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ C).card := by
  choose ρ hρpos hρle hρC using hret
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = i * H + ρ ((T ^ ((i * H : ℕ) : ℤ)) x) :=
    ⟨_, fun _ => rfl⟩
  have hmaps : Set.MapsTo f (Finset.range r : Set ℕ)
      (((Finset.Icc 1 (r * H)).filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ C : Finset ℕ) : Set ℕ) := by
    intro i hi
    have hi' : i < r := Finset.mem_range.1 hi
    have h1 := hρpos ((T ^ ((i * H : ℕ) : ℤ)) x)
    have h2 := hρle ((T ^ ((i * H : ℕ) : ℤ)) x)
    have h3 := hρC ((T ^ ((i * H : ℕ) : ℤ)) x)
    have hmul : (i + 1) * H ≤ r * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt hi')
    have hsucc : (i + 1) * H = i * H + H := Nat.succ_mul i H
    refine Finset.mem_coe.2 (Finset.mem_filter.2
      ⟨Finset.mem_Icc.2 ⟨by rw [hf]; omega, by rw [hf]; omega⟩, ?_⟩)
    rw [hf, Nat.cast_add, add_comm, ← zpow_apply_zpow_apply]
    exact h3
  have hinj : Set.InjOn f (Finset.range r : Set ℕ) := by
    have key : ∀ a b : ℕ, a < b → f a < f b := fun a b hab => by
      have hmul : (a + 1) * H ≤ b * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt hab)
      have hsucc : (a + 1) * H = a * H + H := Nat.succ_mul a H
      have h2 := hρle ((T ^ ((a * H : ℕ) : ℤ)) x)
      have h1 := hρpos ((T ^ ((b * H : ℕ) : ℤ)) x)
      rw [hf, hf]
      omega
    intro i _ i' _ heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (key i i' h).ne heq
    · exact (key i' i h).ne heq.symm
  calc r = (Finset.range r).card := (Finset.card_range r).symm
    _ ≤ _ := Finset.card_le_card_of_injOn f hmaps hinj

open Classical in
/-- "Each orbit meets $K$ at most $m$ times", at the level of times. -/
theorem card_visits_le (hWw : ∀ i, IsWandering T.toEquiv (W i)) (hKW : K ⊆ ⋃ i, W i) (x : X)
    (s : Finset ℕ) : (s.filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ K).card ≤ m := by
  have hsel : ∀ h ∈ s.filter (fun h : ℕ => (T ^ (h : ℤ)) x ∈ K),
      ∃ i : ℕ, ∃ hi : i < m, (T ^ (h : ℤ)) x ∈ W ⟨i, hi⟩ := fun h hh => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hKW (Finset.mem_filter.1 hh).2)
    exact ⟨i, i.2, hi⟩
  choose! ι hι using hsel
  have hinj : Set.InjOn ι (s.filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ K : Set ℕ) := by
    intro h hh h' hh' heq
    obtain ⟨hlt, h1⟩ := hι h hh
    obtain ⟨hlt', h2⟩ := hι h' hh'
    have hfin : (⟨ι h, hlt⟩ : Fin m) = ⟨ι h', hlt'⟩ := Fin.ext heq
    rw [hfin] at h1
    have hmem : (T ^ ((h : ℤ) - h')) ((T ^ (h' : ℤ)) x) ∈ W ⟨ι h', hlt'⟩ := by
      rwa [zpow_apply_zpow_apply, sub_add_cancel]
    have hd := eq_zero_of_isWandering T (hWw _) h2 hmem
    omega
  calc (s.filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ K).card ≤ (Finset.range m).card :=
        Finset.card_le_card_of_injOn ι
          (fun h hh => Finset.mem_coe.2 (Finset.mem_range.2 (hι h hh).1)) hinj
    _ = m := Finset.card_range m

open Classical in
/-- The fresh coordinates already used by the pieces `j < n` meet an orbit at at most `n`
times. -/
theorem card_target_visits_le {n : ℕ} {A : Fin m → ℕ → Set X} (hA : IsPlacement T W K C H n A)
    (hWw : ∀ i, IsWandering T.toEquiv (W i)) {B : Set X}
    (hB : B ⊆ ⋃ (j : Fin m) (g : ℕ), ⇑(T ^ (g : ℤ)) '' A j g) (x : X) (s : Finset ℕ) :
    (s.filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ B).card ≤ n := by
  have hsel : ∀ h ∈ s.filter (fun h : ℕ => (T ^ (h : ℤ)) x ∈ B),
      ∃ jg : ℕ × ℕ, ∃ hj : jg.1 < m, (T ^ (h : ℤ)) x ∈ ⇑(T ^ (jg.2 : ℤ)) '' A ⟨jg.1, hj⟩ jg.2 :=
    fun h hh => by
      obtain ⟨j, g, hjg⟩ := Set.mem_iUnion₂.1 (hB (Finset.mem_filter.1 hh).2)
      exact ⟨((j : ℕ), g), j.2, hjg⟩
  choose! σ hσ using hsel
  have hinj : Set.InjOn (fun h => (σ h).1)
      (s.filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ B : Set ℕ) := by
    intro h hh h' hh' heq
    obtain ⟨hj, y, hy, hyx⟩ := hσ h hh
    obtain ⟨hj', y', hy', hyx'⟩ := hσ h' hh'
    have hfin : (⟨(σ h').1, hj'⟩ : Fin m) = ⟨(σ h).1, hj⟩ := Fin.ext heq.symm
    rw [hfin] at hy'
    have hx : (T ^ (((σ h).2 : ℤ) - h)) y = x := zpow_sub_apply_of_eq T hyx.symm
    have hy'x : (T ^ ((σ h').2 : ℤ)) y' = (T ^ ((h' : ℤ) + (((σ h).2 : ℤ) - h))) y := by
      rw [hyx', ← hx, zpow_apply_zpow_apply]
    have hd : (T ^ ((h' : ℤ) + (((σ h).2 : ℤ) - h) - (σ h').2)) y = y' :=
      zpow_sub_apply_of_eq T hy'x
    have hyW := (coverPiece_subset W K _ (hA.subset _ _ hy)).2
    have hy'W := (coverPiece_subset W K _ (hA.subset _ _ hy')).2
    have hmem : (T ^ ((h' : ℤ) + (((σ h).2 : ℤ) - h) - (σ h').2)) y ∈ W ⟨(σ h).1, hj⟩ := by
      rw [hd]
      exact hy'W
    have hd0 := eq_zero_of_isWandering T (hWw _) hyW hmem
    have hyy' : y = y' := by rw [← hd, hd0, zpow_zero, Homeomorph.one_apply]
    have hg : (σ h).2 = (σ h').2 := by
      by_contra hne
      exact Set.disjoint_left.1 (hA.disjoint_same _ _ _ hne) hy (by rw [hyy']; exact hy')
    omega
  calc (s.filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ B).card ≤ (Finset.range n).card :=
        Finset.card_le_card_of_injOn (fun h => (σ h).1) (fun h hh => by
          obtain ⟨hj, y, hy, _⟩ := hσ h hh
          exact Finset.mem_coe.2 (Finset.mem_range.2 (hA.bounds _ _ ⟨y, hy⟩).1)) hinj
    _ = n := Finset.card_range n

/-- One step of the matching: the next piece is matched to its first free fresh coordinate. -/
theorem isPlacement_succ (hK : IsClopen K) (hC : IsClopen C) (hW : ∀ i, IsClopen (W i))
    (hWw : ∀ i, IsWandering T.toEquiv (W i)) (hKW : K ⊆ ⋃ i, W i)
    (hret : ∀ x, ∃ h : ℕ, 0 < h ∧ h ≤ H ∧ (T ^ (h : ℤ)) x ∈ C) {n : ℕ} (hn : n < m)
    {A : Fin m → ℕ → Set X} (hA : IsPlacement T W K C H n A) :
    ∃ A' : Fin m → ℕ → Set X, IsPlacement T W K C H (n + 1) A' := by
  classical
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin m, (j₀ : ℕ) = n := ⟨⟨n, hn⟩, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set X, B = ⋃ (j : Fin m) (g : ℕ), ⇑(T ^ (g : ℤ)) '' A j g := ⟨_, rfl⟩
  have hBclopen : IsClopen B := by
    have hBeq : B = ⋃ (j : Fin m), ⋃ g ∈ Finset.range (2 * m * H + 1),
        ⇑(T ^ (g : ℤ)) '' A j g := by
      rw [hB]
      ext y
      simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
      constructor
      · rintro ⟨j, g, hg⟩
        have hne : (A j g).Nonempty := by
          obtain ⟨z, hz, _⟩ := hg
          exact ⟨z, hz⟩
        have := (hA.bounds j g hne).2.2
        exact ⟨j, g, by omega, hg⟩
      · rintro ⟨j, g, _, hg⟩
        exact ⟨j, g, hg⟩
    rw [hBeq]
    exact isClopen_iUnion_of_finite fun j =>
      isClopen_biUnion_finset fun g _ => isClopen_zpow_image T (g : ℤ) (hA.isClopen j g)
  have hG : IsClopen (C \ (K ∪ B)) := hC.diff (hK.union hBclopen)
  obtain ⟨good, hgood⟩ : ∃ good : ℕ → Set X, ∀ g, good g =
      if 0 < g ∧ g ≤ 2 * m * H then ⇑(T ^ (g : ℤ)) ⁻¹' (C \ (K ∪ B)) else ∅ :=
    ⟨_, fun _ => rfl⟩
  have hgood_clopen : ∀ g, IsClopen (good g) := fun g => by
    rw [hgood]
    split_ifs
    · exact hG.preimage (T ^ (g : ℤ)).continuous
    · exact isClopen_empty
  have mem_good : ∀ g x, x ∈ good g ↔
      0 < g ∧ g ≤ 2 * m * H ∧ (T ^ (g : ℤ)) x ∈ C \ (K ∪ B) := fun g x => by
    rw [hgood]
    split_ifs with hg
    · exact ⟨fun h => ⟨hg.1, hg.2, h⟩, fun h => h.2.2⟩
    · exact ⟨fun h => False.elim h, fun h => absurd ⟨h.1, h.2.1⟩ hg⟩
  have hexists : ∀ x ∈ coverPiece W K j₀, ∃ g, x ∈ good g := by
    intro x _
    obtain ⟨R, hR⟩ : ∃ R : Finset ℕ,
        R = (Finset.Icc 1 (2 * m * H)).filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ C := ⟨_, rfl⟩
    have hR1 : 2 * m ≤ R.card := by
      rw [hR]
      exact card_returns_ge T C H hret x (2 * m)
    have hR2 := card_visits_le T W K hWw hKW x R
    have hR3 := card_target_visits_le T W K C H hA hWw hB.le x R
    by_contra hno
    have hsub : R ⊆ (R.filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ K) ∪
        (R.filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ B) := by
      intro g hg
      have hg' := hg
      rw [hR] at hg'
      obtain ⟨hgI, hgC⟩ := Finset.mem_filter.1 hg'
      obtain ⟨hg1, hg2⟩ := Finset.mem_Icc.1 hgI
      by_cases hgK : (T ^ (g : ℤ)) x ∈ K
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hg, hgK⟩)
      · by_cases hgB : (T ^ (g : ℤ)) x ∈ B
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hg, hgB⟩)
        · refine absurd ⟨g, (mem_good g x).2 ⟨hg1, hg2, (Set.mem_sdiff _).2 ⟨hgC, ?_⟩⟩⟩ hno
          exact fun hKB => ((Set.mem_union _ _ _).1 hKB).elim hgK hgB
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (R.filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ K)
      (R.filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ B)
    omega
  obtain ⟨A', hA'⟩ : ∃ A' : Fin m → ℕ → Set X, ∀ j g, A' j g =
      if j = j₀ then coverPiece W K j₀ ∩ good g ∩ ⋂ g' ∈ Finset.range g, (good g')ᶜ
      else A j g :=
    ⟨_, fun _ _ => rfl⟩
  refine ⟨A', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j g
    rw [hA']
    split_ifs
    · exact ((isClopen_coverPiece W K hK hW j₀).inter (hgood_clopen g)).inter
        (isClopen_biInter_finset fun g' _ => (hgood_clopen g').compl)
    · exact hA.isClopen j g
  · intro j g
    rw [hA']
    split_ifs with hj
    · rw [hj]
      exact fun x hx => hx.1.1
    · exact hA.subset j g
  · intro j g hne
    rw [hA'] at hne
    split_ifs at hne with hj
    · obtain ⟨x, ⟨_, hxg⟩, _⟩ := hne
      obtain ⟨h1, h2, _⟩ := (mem_good g x).1 hxg
      refine ⟨?_, h1, h2⟩
      rw [hj, hj₀]
      omega
    · obtain ⟨h1, h2, h3⟩ := hA.bounds j g hne
      exact ⟨by omega, h2, h3⟩
  · intro j hj x hx
    by_cases hjj : j = j₀
    · have hx₀ : x ∈ coverPiece W K j₀ := hjj ▸ hx
      have hex : ∃ g, x ∈ good g := hexists x hx₀
      refine ⟨Nat.find hex, ?_⟩
      rw [hA', if_pos hjj]
      refine ⟨⟨hx₀, Nat.find_spec hex⟩, ?_⟩
      simp only [Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range]
      exact fun g' hg' => Nat.find_min hex hg'
    · have hjn : (j : ℕ) < n := by
        have : (j : ℕ) ≠ n := fun h => hjj (Fin.ext (h.trans hj₀.symm))
        omega
      obtain ⟨g, hg⟩ := hA.cover j hjn x hx
      exact ⟨g, by rw [hA', if_neg hjj]; exact hg⟩
  · intro j g g' hgg'
    rw [hA', hA']
    split_ifs with hj
    · rw [Set.disjoint_left]
      rintro x ⟨⟨_, hxg⟩, hxI⟩ ⟨⟨_, hxg'⟩, hxI'⟩
      rcases lt_or_gt_of_ne hgg' with h | h
      · exact (Set.mem_iInter₂.1 hxI' g (Finset.mem_range.2 h)) hxg
      · exact (Set.mem_iInter₂.1 hxI g' (Finset.mem_range.2 h)) hxg'
    · exact hA.disjoint_same j g g' hgg'
  · intro j g
    rw [hA']
    split_ifs
    · rintro _ ⟨x, ⟨⟨_, hxg⟩, _⟩, rfl⟩
      obtain ⟨_, _, hxG⟩ := (mem_good g x).1 hxg
      obtain ⟨hxC, hxKB⟩ := (Set.mem_sdiff _).1 hxG
      exact (Set.mem_sdiff _).2 ⟨hxC, fun hxK => hxKB (Set.mem_union_left _ hxK)⟩
    · exact hA.target j g
  · intro j g j' g' hne
    rw [hA', hA']
    by_cases hj : j = j₀ <;> by_cases hj' : j' = j₀
    · rw [if_pos hj, if_pos hj', Set.disjoint_left]
      have hgg : g ≠ g' := fun h => hne (by rw [hj, hj', h])
      rintro _ ⟨x, ⟨⟨hxP, _⟩, _⟩, rfl⟩ ⟨x', ⟨⟨hx'P, _⟩, _⟩, hxx'⟩
      have hd : (T ^ ((g : ℤ) - g')) x = x' := zpow_sub_apply_of_eq T hxx'
      have hxW := (coverPiece_subset W K j₀ hxP).2
      have hx'W := (coverPiece_subset W K j₀ hx'P).2
      have hmem : (T ^ ((g : ℤ) - g')) x ∈ W j₀ := by
        rw [hd]
        exact hx'W
      have := eq_zero_of_isWandering T (hWw j₀) hxW hmem
      exact hgg (by omega)
    · rw [if_pos hj, if_neg hj', Set.disjoint_left]
      rintro _ ⟨x, ⟨⟨_, hxg⟩, _⟩, rfl⟩ hmemB
      obtain ⟨_, _, hxG⟩ := (mem_good g x).1 hxg
      refine ((Set.mem_sdiff _).1 hxG).2 (Set.mem_union_right _ ?_)
      rw [hB]
      exact Set.mem_iUnion₂.2 ⟨j', g', hmemB⟩
    · rw [if_neg hj, if_pos hj', Set.disjoint_left]
      rintro _ hmemB ⟨x, ⟨⟨_, hxg⟩, _⟩, hxeq⟩
      obtain ⟨_, _, hxG⟩ := (mem_good g' x).1 hxg
      refine ((Set.mem_sdiff _).1 hxG).2 (Set.mem_union_right _ ?_)
      rw [hB, hxeq]
      exact Set.mem_iUnion₂.2 ⟨j, g, hmemB⟩
    · rw [if_neg hj, if_neg hj']
      exact hA.disjoint_target j g j' g' hne

theorem exists_isPlacement (hK : IsClopen K) (hC : IsClopen C) (hW : ∀ i, IsClopen (W i))
    (hWw : ∀ i, IsWandering T.toEquiv (W i)) (hKW : K ⊆ ⋃ i, W i)
    (hret : ∀ x, ∃ h : ℕ, 0 < h ∧ h ≤ H ∧ (T ^ (h : ℤ)) x ∈ C) :
    ∀ n ≤ m, ∃ A : Fin m → ℕ → Set X, IsPlacement T W K C H n A := by
  intro n hn
  induction n with
  | zero => exact ⟨_, isPlacement_zero T W K C H⟩
  | succ n ih =>
    obtain ⟨A, hA⟩ := ih (Nat.le_of_succ_le hn)
    exact isPlacement_succ T W K C H hK hC hW hWw hKW hret (Nat.lt_of_succ_le hn) hA

variable {T W K C H}

theorem IsPlacement.subset_K {n : ℕ} {A : Fin m → ℕ → Set X} (hA : IsPlacement T W K C H n A)
    (j : Fin m) (g : ℕ) : A j g ⊆ K :=
  fun _ hx => (coverPiece_subset W K j (hA.subset j g hx)).1

theorem IsPlacement.disjoint_source {n : ℕ} {A : Fin m → ℕ → Set X}
    (hA : IsPlacement T W K C H n A) {j j' : Fin m} {g g' : ℕ} (hne : (j, g) ≠ (j', g')) :
    Disjoint (A j g) (A j' g') := by
  by_cases hj : j = j'
  · subst hj
    exact hA.disjoint_same j g g' fun h => hne (by rw [h])
  · exact (disjoint_coverPiece W K hj).mono (hA.subset j g) (hA.subset j' g')

theorem IsPlacement.exists_mem {A : Fin m → ℕ → Set X} (hA : IsPlacement T W K C H m A)
    (hKW : K ⊆ ⋃ i, W i) {x : X} (hx : x ∈ K) : ∃ j g, x ∈ A j g := by
  obtain ⟨j, hj⟩ := exists_mem_coverPiece W K hKW hx
  obtain ⟨g, hg⟩ := hA.cover j j.2 x hj
  exact ⟨j, g, hg⟩

variable (T W K C H)

/-- **Fresh return coordinates** (tex 1673–1686): if `K` is covered by `m` wandering clopen sets
and every point reaches `C` within `H` positive steps, then `K` splits into clopen cells `A j h`
with exponents `0 < h ≤ 2mH` whose fresh coordinates `T^h(A j h) ⊆ C ∖ K` are pairwise disjoint. -/
theorem exists_returnPlacement (hK : IsClopen K) (hC : IsClopen C) (hW : ∀ i, IsClopen (W i))
    (hWw : ∀ i, IsWandering T.toEquiv (W i)) (hKW : K ⊆ ⋃ i, W i)
    (hret : ∀ x, ∃ h : ℕ, 0 < h ∧ h ≤ H ∧ (T ^ (h : ℤ)) x ∈ C) :
    ∃ A : Fin m → ℕ → Set X, IsPlacement T W K C H m A :=
  exists_isPlacement T W K C H hK hC hW hWw hKW hret m le_rfl

end Placement

end Dynamics

end GroupApproximation

#audit_axioms GroupApproximation.Dynamics.card_returns_ge
#audit_axioms GroupApproximation.Dynamics.card_visits_le
#audit_axioms GroupApproximation.Dynamics.exists_returnPlacement
#audit_axioms GroupApproximation.Dynamics.IsPlacement.disjoint_source
