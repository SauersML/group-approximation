import GroupApproximation.GGT.VanKampen.CyclicFaceBoundary
import GroupApproximation.GGT.VanKampen.OneFaceWordTrivial
import GroupApproximation.Meta.AxiomGuard

/-!
# Face cycles of a combinatorial map

A face cycle is a nonempty duplicate-free list of darts that follows the face
rotation and closes up.  It is a `FaceBoundary` without the face index in its
type, which is the form that transports across operations changing the dart
type, such as edge deletion (`EdgeDeletion.toCombMap`), with no casts.  It is
the vocabulary of the planar van Kampen induction (`PlanarVanKampen`).

* `CombMap.IsFaceCycle`, with `FaceBoundary.isFaceCycle` and
  `CombMap.IsFaceCycle.toFaceBoundary`;
* `CombMap.exists_isFaceCycle_head`: every dart heads a face cycle;
* `CombMap.IsFaceCycle.exists_rotate_cons`: a face cycle rotates to start at any
  of its darts;
* `CombMap.IsFaceCycle.exists_rotate_eq`: two face cycles of one face are
  rotations of each other.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv

universe u

/-! ## Walks with distinct points -/

/-- A walk whose powers are pairwise distinct has no repeated point. -/
theorem nodup_orbitWalk_of_ne {D : Type u} (p : Perm D) (x : D) :
    ∀ n : ℕ, (∀ i j, i < j → j < n → (p ^ i) x ≠ (p ^ j) x) →
      (orbitWalk p x n).Nodup
  | 0, _ => by simp [orbitWalk_zero]
  | n + 1, h => by
    rw [orbitWalk_succ' p x n, List.nodup_append]
    refine ⟨nodup_orbitWalk_of_ne p x n (fun i j hij hj => h i j hij (by omega)),
      by simp, ?_⟩
    intro y hy z hz
    rw [List.mem_singleton] at hz
    obtain ⟨j, hj, rfl⟩ := (mem_orbitWalk p).mp hy
    subst hz
    exact h j n hj (by omega)

namespace CombMap

variable (M : CombMap.{u})

/-- **A face cycle**: a nonempty duplicate-free list of darts following the face
rotation and closing up. -/
structure IsFaceCycle (l : List M.Dart) : Prop where
  ne_nil : l ≠ []
  nodup : l.Nodup
  chain : l.IsChain fun d e => M.facePerm d = e
  closes : M.facePerm (l.getLast ne_nil) = l.head ne_nil

variable {M}

namespace IsFaceCycle

variable {l : List M.Dart}

/-- A face cycle enumerates exactly the face of its head. -/
theorem mem_iff (hl : M.IsFaceCycle l) (d : M.Dart) :
    d ∈ l ↔ M.faceOf d = M.faceOf (l.head hl.ne_nil) := by
  rw [FaceBoundary.cyclic_mem_iff_sameCycle M.facePerm l hl.ne_nil hl.chain hl.closes,
    M.faceOf_eq_iff]
  exact Perm.sameCycle_comm

/-- The face boundary a face cycle enumerates. -/
noncomputable def toFaceBoundary (hl : M.IsFaceCycle l) :
    FaceBoundary M (M.faceOf (l.head hl.ne_nil)) :=
  FaceBoundary.ofCyclicList M l hl.ne_nil hl.nodup hl.chain hl.closes

theorem toFaceBoundary_darts (hl : M.IsFaceCycle l) : hl.toFaceBoundary.darts = l := rfl

/-- The length of a face cycle is the degree of its face. -/
theorem length_eq (hl : M.IsFaceCycle l) :
    l.length = M.faceDegree (M.faceOf (l.head hl.ne_nil)) :=
  hl.toFaceBoundary.length_eq_degree

/-- A rotated face cycle is a face cycle. -/
theorem rotate (hl : M.IsFaceCycle l) (k : ℕ) : M.IsFaceCycle (l.rotate k) :=
  let B := hl.toFaceBoundary.rotate k
  ⟨B.nonempty, B.nodup, B.chain, B.closes⟩

/-- A face cycle rotates to start at any of its darts. -/
theorem exists_rotate_cons (_hl : M.IsFaceCycle l) {a : M.Dart} (ha : a ∈ l) :
    ∃ (k : ℕ) (rest : List M.Dart), k ≤ l.length ∧ l.rotate k = a :: rest := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  refine ⟨s.length, t ++ s, by simp only [List.length_append, List.length_cons]; omega, ?_⟩
  exact (List.rotate_append_length_eq s (a :: t)).trans (List.cons_append a t s)

/-- Two face cycles of one face are rotations of each other. -/
theorem exists_rotate_eq {l₁ l₂ : List M.Dart} (h₁ : M.IsFaceCycle l₁)
    (h₂ : M.IsFaceCycle l₂)
    (hface : M.faceOf (l₁.head h₁.ne_nil) = M.faceOf (l₂.head h₂.ne_nil)) :
    ∃ k ≤ l₁.length, l₁.rotate k = l₂ := by
  have hmem : l₂.head h₂.ne_nil ∈ l₁ := (h₁.mem_iff _).mpr hface.symm
  obtain ⟨k, rest, hk, hrot⟩ := h₁.exists_rotate_cons hmem
  refine ⟨k, hk, ?_⟩
  have e₁ := eq_orbitWalk_of_isChain M.facePerm (l₁.rotate k) (l₂.head h₂.ne_nil)
    (h₁.rotate k).chain (by simp [hrot])
  have e₂ := eq_orbitWalk_of_isChain M.facePerm l₂ (l₂.head h₂.ne_nil) h₂.chain
    (List.head?_eq_head h₂.ne_nil)
  have hlen : (l₁.rotate k).length = l₂.length := by
    rw [List.length_rotate, h₁.length_eq, h₂.length_eq, hface]
  rw [e₁, hlen]
  exact e₂.symm

end IsFaceCycle

/-- **Every dart heads a face cycle.** -/
theorem exists_isFaceCycle_head (M : CombMap.{u}) (x : M.Dart) :
    ∃ (l : List M.Dart) (hl : M.IsFaceCycle l), l.head hl.ne_nil = x := by
  classical
  have hper : ∃ k, 0 < k ∧ (M.facePerm ^ k) x = x := by
    obtain ⟨n, hn⟩ :=
      (Perm.SameCycle.rfl (f := M.facePerm) (x := x)).apply_left.exists_nat_pow_eq
    exact ⟨n + 1, Nat.succ_pos n, by rw [pow_succ, Perm.mul_apply, hn]⟩
  obtain ⟨k, hk, hmin⟩ : ∃ k, (0 < k ∧ (M.facePerm ^ k) x = x) ∧
      ∀ m, 0 < m → m < k → (M.facePerm ^ m) x ≠ x :=
    ⟨Nat.find hper, Nat.find_spec hper, fun m hm hmk heq => Nat.find_min hper hmk ⟨hm, heq⟩⟩
  have hdistinct : ∀ i j, i < j → j < k → (M.facePerm ^ i) x ≠ (M.facePerm ^ j) x := by
    intro i j hij hjk heq
    apply hmin (j - i) (by omega) (by omega)
    apply (M.facePerm ^ i).injective
    rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le, heq]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hne : orbitWalk M.facePerm x (m + 1) ≠ [] := by
    rw [orbitWalk_succ]
    exact List.cons_ne_nil _ _
  refine ⟨orbitWalk M.facePerm x (m + 1),
    ⟨hne, nodup_orbitWalk_of_ne M.facePerm x (m + 1) hdistinct,
      isChain_orbitWalk M.facePerm x (m + 1), ?_⟩, rfl⟩
  rw [getLast_orbitWalk M.facePerm x m hne, ← Perm.mul_apply, ← pow_succ', hk.2]
  rfl

end CombMap

/-- Every face boundary is a face cycle. -/
theorem FaceBoundary.isFaceCycle {M : CombMap.{u}} {f : M.Face} (B : FaceBoundary M f) :
    M.IsFaceCycle B.darts :=
  ⟨B.nonempty, B.nodup, B.chain, B.closes⟩

/-- The head of a face boundary lies on its face. -/
theorem FaceBoundary.faceOf_head {M : CombMap.{u}} {f : M.Face} (B : FaceBoundary M f) :
    M.faceOf (B.darts.head B.nonempty) = f :=
  (B.mem_iff _).mp (List.head_mem _)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.IsFaceCycle.exists_rotate_eq
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.exists_isFaceCycle_head
