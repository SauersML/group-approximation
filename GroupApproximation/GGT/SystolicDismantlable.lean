import GroupApproximation.GGT.SystolicDefs
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Lattice

/-!
# Dismantlable vertex sets, invariant cliques and finite balls

The graph-theoretic half of the fixed-clique theorem for systolic complexes (CCKW T6).

* `Dismantlable G s`: the finite vertex set `s` shrinks to a single vertex by repeatedly deleting
  a vertex `u` dominated inside the current set by another vertex `w` of it: every vertex of the
  set equal or adjacent to `u` is equal or adjacent to `w`.
* `Dismantlable.erase_of_dominated`: any dominated vertex of a dismantlable set can be deleted
  first.
* `Dismantlable.sdiff_of_dominated`: so can a set `D` of vertices, each dominated by a vertex
  outside `D`.
* `Dismantlable.exists_invariantClique` (Polat, Ginsburg): a group of graph automorphisms mapping a
  dismantlable set into itself preserves a nonempty clique inside it.
* `finite_setOf_dist_le`: balls in a locally finite graph are finite.

## Proof of `exists_invariantClique`

Strong induction on `s`.  The strictly dominated vertices of `s` form an invariant set `D`.  If
`D` is nonempty, each vertex of `D` is dominated by a dominator with the largest closed
neighbourhood, which lies outside `D`; so `s \ D` is dismantlable, invariant and smaller.  If `D`
is empty, all domination inside `s` is mutual, and the deletion order shows that `s` is a clique.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the Kotowski--Ollivier
route (CCKW Theorem 3.1(ii)); certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace Systolic

section Domination

variable {V : Type*}

/-- A graph automorphism `f` with `f⁻¹` mapping `s` into `s` carries domination inside `s` to
domination inside `s`. -/
theorem dominated_iso_map {G : SimpleGraph V} {s : Finset V} (f : G ≃g G)
    (hf : ∀ y ∈ s, f⁻¹ y ∈ s) {u w : V}
    (hdom : ∀ x ∈ s, (x = u ∨ G.Adj u x) → x = w ∨ G.Adj w x) :
    ∀ x ∈ s, (x = f u ∨ G.Adj (f u) x) → x = f w ∨ G.Adj (f w) x := by
  intro y hy hyu
  obtain ⟨x, rfl⟩ : ∃ x, f x = y := ⟨f⁻¹ y, RelIso.apply_inv_self f y⟩
  have hx : x ∈ s := by
    have h := hf (f x) hy
    rwa [RelIso.inv_apply_self] at h
  have hxu : x = u ∨ G.Adj u x := by
    rcases hyu with h | h
    · exact Or.inl (f.injective h)
    · exact Or.inr (f.map_adj_iff.1 h)
  rcases hdom x hx hxu with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (f.map_adj_iff.2 h)

/-- **Balls in a locally finite graph are finite.** -/
theorem finite_setOf_dist_le {G : SimpleGraph V} (hfin : ∀ v, (G.neighborSet v).Finite)
    (o : V) (R : ℕ) : {x | G.Reachable o x ∧ G.dist o x ≤ R}.Finite := by
  have hwalk : ∀ (n : ℕ) (v : V), {x | ∃ p : G.Walk v x, p.length ≤ n}.Finite := by
    intro n
    induction n with
    | zero =>
      intro v
      refine (Set.finite_singleton v).subset ?_
      rintro x ⟨p, hp⟩
      cases p with
      | nil => exact Set.mem_singleton _
      | cons _ _ =>
        rw [SimpleGraph.Walk.length_cons] at hp
        omega
    | succ n ih =>
      intro v
      refine ((Set.finite_singleton v).union ((hfin v).biUnion fun y _ => ih y)).subset ?_
      rintro x ⟨p, hp⟩
      cases p with
      | nil => exact Or.inl (Set.mem_singleton _)
      | @cons _ y _ h q =>
        rw [SimpleGraph.Walk.length_cons] at hp
        exact Or.inr (Set.mem_biUnion (show y ∈ G.neighborSet v from h) ⟨q, by omega⟩)
  refine (hwalk R o).subset ?_
  rintro x ⟨hr, hd⟩
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  exact ⟨p, hp.le.trans hd⟩

end Domination

section Dismantling

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- **Dismantlable finite vertex sets.**  A singleton is dismantlable, and so is a finite set `s`
with a vertex `u ∈ s` dominated inside `s` by a vertex `w ∈ s`, `w ≠ u` (every vertex of `s`
equal or adjacent to `u` is equal or adjacent to `w`), such that `s.erase u` is dismantlable. -/
inductive Dismantlable : Finset V → Prop
  | single (v : V) : Dismantlable {v}
  | erase {s : Finset V} {u w : V} (hu : u ∈ s) (hw : w ∈ s) (hwu : w ≠ u)
      (hdom : ∀ x ∈ s, (x = u ∨ G.Adj u x) → x = w ∨ G.Adj w x)
      (h : Dismantlable (s.erase u)) : Dismantlable s

variable {G}

namespace Dismantlable

/-- A dismantlable set is nonempty. -/
theorem nonempty {s : Finset V} (hs : Dismantlable G s) : s.Nonempty := by
  cases hs with
  | single v => exact Finset.singleton_nonempty v
  | @erase _ u _ hu _ _ _ _ => exact ⟨u, hu⟩

/-- Dismantlability transports along a permutation of the vertices preserving adjacency on `s`. -/
theorem map_equiv {s : Finset V} (hs : Dismantlable G s) (φ : V ≃ V)
    (hφ : ∀ x ∈ s, ∀ y ∈ s, (G.Adj (φ x) (φ y) ↔ G.Adj x y)) :
    Dismantlable G (s.map φ.toEmbedding) := by
  revert hφ
  induction hs with
  | single v =>
    intro _
    rw [Finset.map_singleton]
    exact Dismantlable.single _
  | @erase s u w hu hw hwu hdom _ ih =>
    intro hφ
    refine Dismantlable.erase (u := φ u) (w := φ w) ?_ ?_ (φ.injective.ne hwu) ?_ ?_
    · rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hu
    · rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hw
    · intro y hy hyu
      obtain ⟨x, rfl⟩ : ∃ x, φ x = y := ⟨φ.symm y, φ.apply_symm_apply y⟩
      rw [Finset.mem_map_equiv, Equiv.symm_apply_apply] at hy
      have hxu : x = u ∨ G.Adj u x := by
        rcases hyu with h | h
        · exact Or.inl (φ.injective h)
        · exact Or.inr ((hφ u hu x hy).1 h)
      rcases hdom x hy hxu with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr ((hφ w hw x hy).2 h)
    · show Dismantlable G ((s.map φ.toEmbedding).erase (φ.toEmbedding u))
      rw [← Finset.map_erase]
      exact ih fun x hx y hy => hφ x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)

/-- **Deleting a dominated vertex.**  If `s` is dismantlable and `u ∈ s` is dominated inside `s`
by `w ∈ s`, `w ≠ u`, then `s.erase u` is dismantlable. -/
theorem erase_of_dominated {s : Finset V} (hs : Dismantlable G s) :
    ∀ {u w : V}, u ∈ s → w ∈ s → w ≠ u →
      (∀ x ∈ s, (x = u ∨ G.Adj u x) → x = w ∨ G.Adj w x) → Dismantlable G (s.erase u) := by
  induction hs with
  | single v =>
    intro u w hu hw hwu _
    rw [Finset.mem_singleton] at hu hw
    exact absurd (hw.trans hu.symm) hwu
  | @erase s u₀ w₀ hu₀ hw₀ hwu₀ hdom₀ h₀ ih =>
    intro u w hu hw hwu hdom
    by_cases huu₀ : u = u₀
    · rw [huu₀]
      exact h₀
    have hu₁ : u ∈ s.erase u₀ := Finset.mem_erase.2 ⟨huu₀, hu⟩
    have hu₀₁ : u₀ ∈ s.erase u := Finset.mem_erase.2 ⟨Ne.symm huu₀, hu₀⟩
    have restrict : ∀ {t : Finset V} {a b : V}, t ⊆ s →
        (∀ x ∈ s, (x = a ∨ G.Adj a x) → x = b ∨ G.Adj b x) →
          ∀ x ∈ t, (x = a ∨ G.Adj a x) → x = b ∨ G.Adj b x :=
      fun hts hab x hx => hab x (hts hx)
    by_cases hw₀u : w₀ = u
    · rw [hw₀u] at hdom₀
      by_cases hwu₀' : w = u₀
      · -- `u` and `u₀` are twins in `s`: transport `s.erase u₀` along their swap
        rw [hwu₀'] at hdom
        have twin : ∀ t ∈ s, t ≠ u → t ≠ u₀ → (G.Adj u₀ t ↔ G.Adj u t) := fun t ht htu htu₀ =>
          ⟨fun hadj => (hdom₀ t ht (Or.inr hadj)).resolve_left htu,
            fun hadj => (hdom t ht (Or.inr hadj)).resolve_left htu₀⟩
        have hmap : (s.erase u₀).map (Equiv.swap u u₀).toEmbedding = s.erase u := by
          ext y
          rw [Finset.mem_map_equiv, Equiv.symm_swap, Finset.mem_erase, Finset.mem_erase]
          by_cases hyu : y = u
          · rw [hyu, Equiv.swap_apply_left]
            exact iff_of_false (fun h => h.1 rfl) (fun h => h.1 rfl)
          · by_cases hyu₀ : y = u₀
            · rw [hyu₀, Equiv.swap_apply_right]
              exact ⟨fun _ => ⟨Ne.symm huu₀, hu₀⟩, fun _ => ⟨huu₀, hu⟩⟩
            · rw [Equiv.swap_apply_of_ne_of_ne hyu hyu₀]
              exact ⟨fun hy => ⟨hyu, hy.2⟩, fun hy => ⟨hyu₀, hy.2⟩⟩
        rw [← hmap]
        refine h₀.map_equiv (Equiv.swap u u₀) fun x hx y hy => ?_
        have hx₀ : x ≠ u₀ := Finset.ne_of_mem_erase hx
        have hy₀ : y ≠ u₀ := Finset.ne_of_mem_erase hy
        by_cases hxu : x = u
        · by_cases hyu : y = u
          · rw [hxu, hyu, Equiv.swap_apply_left]
            exact iff_of_false G.irrefl G.irrefl
          · rw [hxu, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hyu hy₀]
            exact twin y (Finset.mem_of_mem_erase hy) hyu hy₀
        · rw [Equiv.swap_apply_of_ne_of_ne hxu hx₀]
          by_cases hyu : y = u
          · rw [hyu, Equiv.swap_apply_left]
            have htw := twin x (Finset.mem_of_mem_erase hx) hxu hx₀
            exact ⟨fun hadj => (htw.1 hadj.symm).symm, fun hadj => (htw.2 hadj.symm).symm⟩
          · rw [Equiv.swap_apply_of_ne_of_ne hyu hy₀]
      · -- `u₀` is dominated by `w` inside `s.erase u`
        refine Dismantlable.erase hu₀₁ (Finset.mem_erase.2 ⟨hwu, hw⟩) hwu₀' ?_ ?_
        · intro x hx hxu₀
          have hxs := Finset.mem_of_mem_erase hx
          exact hdom x hxs (hdom₀ x hxs hxu₀)
        · rw [Finset.erase_right_comm]
          exact ih hu₁ (Finset.mem_erase.2 ⟨hwu₀', hw⟩) hwu
            (restrict (Finset.erase_subset _ _) hdom)
    · -- delete `u₀` first, dominated by `w₀ ≠ u`
      refine Dismantlable.erase hu₀₁ (Finset.mem_erase.2 ⟨hw₀u, hw₀⟩) hwu₀
        (restrict (Finset.erase_subset _ _) hdom₀) ?_
      rw [Finset.erase_right_comm]
      by_cases hwu₀' : w = u₀
      · rw [hwu₀'] at hdom
        have hdom' : ∀ x ∈ s, (x = u ∨ G.Adj u x) → x = w₀ ∨ G.Adj w₀ x :=
          fun x hx hxu => hdom₀ x hx (hdom x hx hxu)
        exact ih hu₁ (Finset.mem_erase.2 ⟨hwu₀, hw₀⟩) hw₀u
          (restrict (Finset.erase_subset _ _) hdom')
      · exact ih hu₁ (Finset.mem_erase.2 ⟨hwu₀', hw⟩) hwu
          (restrict (Finset.erase_subset _ _) hdom)

/-- **Deleting dominated vertices.**  If `s` is dismantlable and every vertex of `D` is dominated
inside `s` by a vertex of `s` outside `D`, then `s \ D` is dismantlable. -/
theorem sdiff_of_dominated {s : Finset V} (hs : Dismantlable G s) (D : Finset V)
    (hD : ∀ u ∈ D, ∃ w ∈ s, w ∉ D ∧ ∀ x ∈ s, (x = u ∨ G.Adj u x) → x = w ∨ G.Adj w x) :
    Dismantlable G (s \ D) := by
  revert hD
  induction D using Finset.induction_on with
  | empty =>
    intro _
    rwa [Finset.sdiff_empty]
  | @insert a D ha ih =>
    intro hD
    rw [Finset.sdiff_insert]
    have hD' : Dismantlable G (s \ D) := ih fun u hu => by
      obtain ⟨w, hw, hwD, hdom⟩ := hD u (Finset.mem_insert_of_mem hu)
      exact ⟨w, hw, fun h => hwD (Finset.mem_insert_of_mem h), hdom⟩
    by_cases has : a ∈ s
    · obtain ⟨w, hw, hwD, hdom⟩ := hD a (Finset.mem_insert_self a D)
      rw [Finset.mem_insert, not_or] at hwD
      exact hD'.erase_of_dominated (Finset.mem_sdiff.2 ⟨has, ha⟩) (Finset.mem_sdiff.2 ⟨hw, hwD.2⟩)
        hwD.1 fun x hx => hdom x (Finset.mem_sdiff.1 hx).1
    · rwa [Finset.erase_eq_of_notMem fun h => has (Finset.mem_sdiff.1 h).1]

/-- A dismantlable set in which domination is always mutual is a clique. -/
theorem isClique_of_dominated_symm {s : Finset V} (hs : Dismantlable G s)
    (hsymm : ∀ u ∈ s, ∀ w ∈ s, (∀ x ∈ s, (x = u ∨ G.Adj u x) → x = w ∨ G.Adj w x) →
      ∀ x ∈ s, (x = w ∨ G.Adj w x) → x = u ∨ G.Adj u x) :
    G.IsClique (s : Set V) := by
  revert hsymm
  induction hs with
  | single v =>
    intro _
    simp
  | @erase s u w hu hw hwu hdom _ ih =>
    intro hsymm
    have hwu' : ∀ x ∈ s, (x = w ∨ G.Adj w x) → x = u ∨ G.Adj u x := hsymm u hu w hw hdom
    have hw₁ : w ∈ s.erase u := Finset.mem_erase.2 ⟨hwu, hw⟩
    have hclique : G.IsClique ((s.erase u : Finset V) : Set V) := by
      refine ih fun x hx y hy hxy => ?_
      have hxs := Finset.mem_of_mem_erase hx
      have hys := Finset.mem_of_mem_erase hy
      -- domination inside `s.erase u` lifts to `s`, since `u` and `w` see the same vertices
      have hxy' : ∀ z ∈ s, (z = x ∨ G.Adj x z) → z = y ∨ G.Adj y z := by
        intro z hz hzx
        by_cases hzu : z = u
        · rw [hzu] at hzx ⊢
          have hxu : G.Adj x u := hzx.resolve_left (Ne.symm (Finset.ne_of_mem_erase hx))
          have hwx : w = x ∨ G.Adj x w := by
            rcases hdom x hxs (Or.inr hxu.symm) with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          have hyw : y = w ∨ G.Adj w y := by
            rcases hxy w hw₁ hwx with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          exact Or.inr ((hwu' y hys hyw).resolve_left (Finset.ne_of_mem_erase hy)).symm
        · exact hxy z (Finset.mem_erase.2 ⟨hzu, hz⟩) hzx
      exact fun z hz => hsymm x hxs y hys hxy' z (Finset.mem_of_mem_erase hz)
    rw [← Finset.insert_erase hu, Finset.coe_insert, SimpleGraph.isClique_insert]
    refine ⟨hclique, fun b hb hub => ?_⟩
    have hb' : b ∈ s.erase u := Finset.mem_coe.1 hb
    have hbw : b = w ∨ G.Adj w b := by
      by_cases hbw : b = w
      · exact Or.inl hbw
      · exact Or.inr (hclique (Finset.mem_coe.2 hw₁) hb (Ne.symm hbw))
    exact (hwu' b (Finset.mem_of_mem_erase hb') hbw).resolve_left (Ne.symm hub)

/-- **Invariant cliques in dismantlable sets** (Polat; Ginsburg).  A group of graph automorphisms
mapping a dismantlable finite set `s` into itself preserves a nonempty clique contained in `s`. -/
theorem exists_invariantClique {s : Finset V} (hs : Dismantlable G s) {Γ : Type*} [Group Γ]
    (ρ : Γ →* (G ≃g G)) (hinv : ∀ γ : Γ, ∀ x ∈ s, ρ γ x ∈ s) :
    ∃ σ : Finset V, σ.Nonempty ∧ σ ⊆ s ∧ G.IsClique (σ : Set V) ∧
      ∀ γ : Γ, ∀ x ∈ σ, ρ γ x ∈ σ := by
  classical
  revert hs hinv
  induction s using Finset.strongInduction with
  | H s ih =>
    intro hs hinv
    have key : ∀ g : Γ, ∀ y ∈ s, (ρ g)⁻¹ y ∈ s := fun g y hy => by
      rw [← map_inv ρ g]
      exact hinv g⁻¹ y hy
    -- the strictly dominated vertices of `s`
    obtain ⟨D, hD⟩ : ∃ D : Finset V, ∀ u, u ∈ D ↔ u ∈ s ∧ ∃ w ∈ s,
        (∀ x ∈ s, (x = u ∨ G.Adj u x) → x = w ∨ G.Adj w x) ∧
          ¬ ∀ x ∈ s, (x = w ∨ G.Adj w x) → x = u ∨ G.Adj u x :=
      ⟨s.filter fun u => ∃ w ∈ s, (∀ x ∈ s, (x = u ∨ G.Adj u x) → x = w ∨ G.Adj w x) ∧
          ¬ ∀ x ∈ s, (x = w ∨ G.Adj w x) → x = u ∨ G.Adj u x, fun _ => Finset.mem_filter⟩
    rcases D.eq_empty_or_nonempty with hD0 | hDne
    · -- all domination inside `s` is mutual, so `s` is a clique
      refine ⟨s, hs.nonempty, Finset.Subset.refl s, hs.isClique_of_dominated_symm ?_, hinv⟩
      intro u hu w hw huw
      by_contra hwu
      have hmem : u ∈ D := (hD u).2 ⟨hu, w, hw, huw, hwu⟩
      rw [hD0] at hmem
      exact Finset.notMem_empty u hmem
    · have hDs : D ⊆ s := fun u hu => ((hD u).1 hu).1
      -- a dominator of `u` with the largest closed neighbourhood is not strictly dominated
      have hdomD : ∀ u ∈ D, ∃ w ∈ s, w ∉ D ∧
          ∀ x ∈ s, (x = u ∨ G.Adj u x) → x = w ∨ G.Adj w x := by
        intro u hu
        have hne : (s.filter fun w => ∀ x ∈ s, (x = u ∨ G.Adj u x) → x = w ∨ G.Adj w x).Nonempty :=
          ⟨u, Finset.mem_filter.2 ⟨hDs hu, fun _ _ h => h⟩⟩
        obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image _
          (fun w => (s.filter fun x => x = w ∨ G.Adj w x).card) hne
        rw [Finset.mem_filter] at hw
        refine ⟨w, hw.1, fun hwD => ?_, hw.2⟩
        obtain ⟨-, w', hw', hww', hw'w⟩ := (hD w).1 hwD
        have hle := hmax w' (Finset.mem_filter.2 ⟨hw', fun x hx hxu => hww' x hx (hw.2 x hx hxu)⟩)
        have hss : (s.filter fun x => x = w ∨ G.Adj w x) ⊂
            (s.filter fun x => x = w' ∨ G.Adj w' x) := by
          refine ssubset_of_subset_not_superset (fun x hx => ?_) fun hsub => hw'w fun x hx hxw' => ?_
          · rw [Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, hww' x hx.1 hx.2⟩
          · exact (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨hx, hxw'⟩))).2
        exact absurd hle (not_le.2 (Finset.card_lt_card hss))
      -- `s \ D` is invariant
      have hinvD : ∀ γ : Γ, ∀ x ∈ s \ D, ρ γ x ∈ s \ D := by
        intro γ x hx
        rw [Finset.mem_sdiff] at hx ⊢
        refine ⟨hinv γ x hx.1, fun hγx => hx.2 ((hD x).2 ⟨hx.1, ?_⟩)⟩
        obtain ⟨-, w, hw, hdom, hndom⟩ := (hD (ρ γ x)).1 hγx
        have hx' : ρ γ⁻¹ (ρ γ x) = x := by rw [map_inv, RelIso.inv_apply_self]
        have hw' : ρ γ (ρ γ⁻¹ w) = w := by rw [map_inv, RelIso.apply_inv_self]
        refine ⟨ρ γ⁻¹ w, hinv γ⁻¹ w hw, ?_, fun h => hndom ?_⟩
        · have h := dominated_iso_map (ρ γ⁻¹) (key γ⁻¹) hdom
          rwa [hx'] at h
        · have h' := dominated_iso_map (ρ γ) (key γ) h
          rwa [hw'] at h'
      obtain ⟨σ, hσ, hσs, hσc, hσinv⟩ :=
        ih (s \ D) (Finset.sdiff_ssubset hDs hDne) (hs.sdiff_of_dominated D hdomD) hinvD
      exact ⟨σ, hσ, fun x hx => (Finset.mem_sdiff.1 (hσs hx)).1, hσc, hσinv⟩

end Dismantlable

end Dismantling

end Systolic
end GroupApproximation

#audit_axioms GroupApproximation.Systolic.finite_setOf_dist_le
#audit_axioms GroupApproximation.Systolic.Dismantlable.erase_of_dominated
#audit_axioms GroupApproximation.Systolic.Dismantlable.exists_invariantClique
