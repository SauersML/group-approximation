import GroupApproximation.Sofic.GreendlingerCombinatorics
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Relation

/-!
# Labelled combinatorial maps (lane NN07a, milestone 1 of L7)

Combinatorial substrate for the classical `C'(1/6)` Greendlinger lemma, which is
`SmallCancellationRouter.GreendlingerGate` (quarantined gate, `non_mf_group_notes.tex`,
`thm:torsionfree`, milestone 1 of the L7 route).

A labelled map is a finite set of darts with
* a fixed-point-free involution `opp` (the two orientations of an edge), which inverts labels;
* a permutation `next` (face successor) with inverse `prev`.

Faces are `next`-orbits and vertices are orbits of `rot d = next (opp d)`.  Euler's formula
`V - E + F = 2` is recorded without quotients as `Σ_d (1/|face d| + 1/|vertex d|) = |darts|/2 + 2`.

Face words are read by `run`.  An arc of `k` consecutive darts of one face is *glued* when the
mirrored darts run consecutively backwards along a single neighbouring face (the interior
vertices of the arc have degree two).  This file proves the word-level facts about glued arcs
that the Greendlinger assembly needs:
* `invRev_run_of_glued`: the inverse of a glued arc is the arc read on the neighbouring face;
* `run_prefix_mirror`: a glued arc is a common prefix of the face word and of the inverted
  neighbouring face word, so it is a piece in the sense of `SmallCancellationRouter.IsPiece`.
-/

namespace GroupApproximation.Full.NN07a

open GroupApproximation.SmallCancellationRouter

universe u

/-- Formal inversion preserves contiguous subwords. -/
theorem invRev_infix {β : Type*} {L₁ L₂ : List (β × Bool)} (h : L₁ <:+: L₂) :
    FreeGroup.invRev L₁ <:+: FreeGroup.invRev L₂ := by
  obtain ⟨A, B, rfl⟩ := h
  exact ⟨FreeGroup.invRev B, FreeGroup.invRev A, by
    rw [FreeGroup.invRev_append, FreeGroup.invRev_append, List.append_assoc]⟩

/-- A finite labelled combinatorial map (Lyndon–Schupp, Ch. V §1, in dart form). -/
structure LabelledMap (α : Type u) where
  /-- The darts (oriented edges). -/
  Dart : Type
  /-- Finitely many darts. -/
  instFintype : Fintype Dart
  /-- The label of a dart: a letter with its exponent sign. -/
  label : Dart → α × Bool
  /-- Reversal of the orientation of an edge. -/
  opp : Dart → Dart
  /-- The successor of a dart along its face. -/
  next : Dart → Dart
  /-- The predecessor of a dart along its face. -/
  prev : Dart → Dart
  opp_opp : ∀ d, opp (opp d) = d
  opp_ne : ∀ d, opp d ≠ d
  next_prev : ∀ d, next (prev d) = d
  prev_next : ∀ d, prev (next d) = d
  label_opp : ∀ d, label (opp d) = ((label d).1, !(label d).2)

attribute [instance] LabelledMap.instFintype

namespace LabelledMap

variable {α : Type u} (M : LabelledMap α)

/-- Rotation around the origin vertex of a dart. -/
def rot (d : M.Dart) : M.Dart := M.next (M.opp d)

/-- The length of the face through `d`. -/
def flen (d : M.Dart) : ℕ := Function.minimalPeriod M.next d

/-- The degree of the origin vertex of `d`. -/
def vdeg (d : M.Dart) : ℕ := Function.minimalPeriod M.rot d

/-- The underlying graph of the map is connected. -/
def IsConnected : Prop :=
  ∀ d d' : M.Dart, Relation.ReflTransGen (fun x y => y = M.next x ∨ y = M.opp x) d d'

/-- Euler's formula `V - E + F = 2`, counted over darts. -/
def IsSpherical : Prop :=
  (∑ d : M.Dart, ((1 : ℚ) / (M.flen d : ℚ) + 1 / (M.vdeg d : ℚ))) =
    (Fintype.card M.Dart : ℚ) / 2 + 2

/-- The word spelled by `k` consecutive darts of a face, starting at `d`. -/
def run : M.Dart → ℕ → List (α × Bool)
  | _, 0 => []
  | d, k + 1 => M.label d :: run (M.next d) k

/-- The boundary word of the face through `d`, read from `d`. -/
def wordFrom (d : M.Dart) : List (α × Bool) := M.run d (M.flen d)

/-- `d` lies on the face through `o`. -/
def OnFace (o d : M.Dart) : Prop := ∃ n : ℕ, M.next^[n] o = d

/-- The first `k` darts from `y` are glued to one neighbouring face, consecutively backwards. -/
def IsGlued (y : M.Dart) (k : ℕ) : Prop :=
  ∀ i, i < k → M.next^[i] (M.opp (M.next^[i] y)) = M.opp y

/-- Reducedness of the diagram away from the outer face through `o`: two interior faces
meeting along an edge are never mirror images of each other across that edge. -/
def IsReducedAway (o : M.Dart) : Prop :=
  ∀ d, ¬ M.OnFace o d → ¬ M.OnFace o (M.opp d) →
    M.wordFrom d ≠ FreeGroup.invRev (M.wordFrom (M.next (M.opp d)))

/-- A glued arc from `x` whose mirror lies on the outer face through `o`, inside one traversal
of that face starting at `o`. -/
def IsOuterRun (o x : M.Dart) (k : ℕ) : Prop :=
  M.IsGlued x k ∧ ∃ m : ℕ, m < M.flen o ∧ k ≤ m + 1 ∧ M.opp x = M.next^[m] o

/-- A glued arc from `y` whose neighbouring face is interior. -/
def IsInteriorRun (o y : M.Dart) (k : ℕ) : Prop :=
  M.IsGlued y k ∧ (0 < k → ¬ M.OnFace o (M.opp y))

/-- A shell: an interior face whose boundary is one outer arc followed by at most three
interior arcs (Lyndon–Schupp, Ch. V, Thm. 4.3). -/
def IsShell (o x : M.Dart) : Prop :=
  ¬ M.OnFace o x ∧ ∃ k k₁ k₂ k₃ : ℕ, k + k₁ + k₂ + k₃ = M.flen x ∧ M.IsOuterRun o x k ∧
    M.IsInteriorRun o (M.next^[k] x) k₁ ∧ M.IsInteriorRun o (M.next^[k + k₁] x) k₂ ∧
    M.IsInteriorRun o (M.next^[k + k₁ + k₂] x) k₃

theorem next_injective : Function.Injective M.next :=
  Function.LeftInverse.injective M.prev_next

theorem opp_injective : Function.Injective M.opp :=
  Function.LeftInverse.injective M.opp_opp

theorem mem_periodicPts (d : M.Dart) : d ∈ Function.periodicPts M.next :=
  M.next_injective.mem_periodicPts d

theorem flen_pos (d : M.Dart) : 0 < M.flen d :=
  Function.minimalPeriod_pos_of_mem_periodicPts (M.mem_periodicPts d)

theorem iterate_flen (d : M.Dart) : M.next^[M.flen d] d = d :=
  Function.iterate_minimalPeriod (f := M.next) (x := d)

theorem flen_iterate (d : M.Dart) (n : ℕ) : M.flen (M.next^[n] d) = M.flen d :=
  Function.minimalPeriod_apply_iterate (M.mem_periodicPts d) n

theorem run_succ (d : M.Dart) (k : ℕ) :
    M.run d (k + 1) = M.label d :: M.run (M.next d) k := rfl

theorem length_run (d : M.Dart) (k : ℕ) : (M.run d k).length = k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih => rw [M.run_succ d k, List.length_cons, ih]

theorem length_wordFrom (d : M.Dart) : (M.wordFrom d).length = M.flen d :=
  M.length_run d _

theorem run_add (d : M.Dart) (a b : ℕ) :
    M.run d (a + b) = M.run d a ++ M.run (M.next^[a] d) b := by
  induction a generalizing d with
  | zero =>
    show M.run d (0 + b) = [] ++ M.run d b
    rw [Nat.zero_add, List.nil_append]
  | succ a ih =>
    have h : a + 1 + b = (a + b) + 1 := by omega
    rw [h, M.run_succ d (a + b), ih (M.next d)]
    rfl

theorem isGlued_mono {y : M.Dart} {k l : ℕ} (h : M.IsGlued y k) (hl : l ≤ k) :
    M.IsGlued y l :=
  fun i hi => h i (lt_of_lt_of_le hi hl)

theorem onFace_of_onFace_next {o d : M.Dart} (h : M.OnFace o (M.next d)) : M.OnFace o d := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero =>
    refine ⟨M.flen o - 1, M.next_injective ?_⟩
    have e : M.flen o - 1 + 1 = M.flen o := by
      have := M.flen_pos o
      omega
    calc M.next (M.next^[M.flen o - 1] o) = M.next^[M.flen o - 1 + 1] o :=
          (Function.iterate_succ_apply' M.next _ o).symm
      _ = M.next^[M.flen o] o := by rw [e]
      _ = o := M.iterate_flen o
      _ = M.next d := hn
  | succ n =>
    exact ⟨n, M.next_injective ((Function.iterate_succ_apply' M.next n o).symm.trans hn)⟩

theorem onFace_of_onFace_iterate {o d : M.Dart} (n : ℕ) (h : M.OnFace o (M.next^[n] d)) :
    M.OnFace o d := by
  induction n generalizing d with
  | zero => exact h
  | succ n ih => exact M.onFace_of_onFace_next (ih (d := M.next d) h)

/-- The inverse of a glued arc is the mirrored arc on the neighbouring face. -/
theorem invRev_run_of_glued (y : M.Dart) (k : ℕ) (h : M.IsGlued y (k + 1)) :
    FreeGroup.invRev (M.run y (k + 1)) = M.run (M.opp (M.next^[k] y)) (k + 1) := by
  induction k with
  | zero =>
    show FreeGroup.invRev [M.label y] = [M.label (M.opp y)]
    rw [M.label_opp]
    rfl
  | succ k ih =>
    have h' : M.IsGlued y (k + 1) := M.isGlued_mono h (by omega)
    have h1 : M.next^[k + 1] (M.opp (M.next^[k + 1] y)) = M.opp y := h (k + 1) (by omega)
    have h2 : M.next^[k] (M.opp (M.next^[k] y)) = M.opp y := h k (by omega)
    have h3 : M.next^[k] (M.next (M.opp (M.next^[k + 1] y))) =
        M.next^[k] (M.opp (M.next^[k] y)) := by
      rw [h2]
      exact h1
    have hstep : M.next (M.opp (M.next^[k + 1] y)) = M.opp (M.next^[k] y) :=
      M.next_injective.iterate k h3
    rw [M.run_add y (k + 1) 1, FreeGroup.invRev_append, ih h',
      M.run_succ (M.opp (M.next^[k + 1] y)) (k + 1), hstep, M.label_opp]
    rfl

/-- A glued arc cannot be longer than the neighbouring face. -/
theorem le_flen_opp_of_glued {y : M.Dart} {k : ℕ} (h : M.IsGlued y k) (hk : k ≤ M.flen y) :
    k ≤ M.flen (M.opp y) := by
  rcases Nat.lt_or_ge (M.flen (M.opp y)) k with hlt | hge
  · exfalso
    have h1 : M.next^[M.flen (M.opp y)] (M.opp (M.next^[M.flen (M.opp y)] y)) = M.opp y :=
      h (M.flen (M.opp y)) hlt
    have hz : M.flen (M.opp (M.next^[M.flen (M.opp y)] y)) = M.flen (M.opp y) := by
      calc M.flen (M.opp (M.next^[M.flen (M.opp y)] y))
          = M.flen (M.next^[M.flen (M.opp y)] (M.opp (M.next^[M.flen (M.opp y)] y))) :=
            (M.flen_iterate _ _).symm
        _ = M.flen (M.opp y) := by rw [h1]
    have h2 : M.opp (M.next^[M.flen (M.opp y)] y) = M.opp y := by
      have e := M.iterate_flen (M.opp (M.next^[M.flen (M.opp y)] y))
      rw [hz] at e
      exact e.symm.trans h1
    have h3 : M.next^[M.flen (M.opp y)] y = y := M.opp_injective h2
    have hpos : 0 < M.flen (M.opp y) := M.flen_pos _
    have h4 : M.flen y ≤ M.flen (M.opp y) := Function.IsPeriodicPt.minimalPeriod_le hpos h3
    omega
  · exact hge

/-- A glued arc from `y` is a prefix of the inverted word of the neighbouring face. -/
theorem run_prefix_mirror {y : M.Dart} {k : ℕ} (h : M.IsGlued y (k + 1))
    (hk : k + 1 ≤ M.flen y) :
    M.run y (k + 1) <+: FreeGroup.invRev (M.wordFrom (M.next (M.opp y))) := by
  have hglue : M.next^[k] (M.opp (M.next^[k] y)) = M.opp y := h k (by omega)
  have hz : M.next^[k + 1] (M.opp (M.next^[k] y)) = M.next (M.opp y) :=
    (Function.iterate_succ_apply' M.next k (M.opp (M.next^[k] y))).trans (congrArg M.next hglue)
  have hper : M.flen (M.next (M.opp y)) = M.flen (M.opp (M.next^[k] y)) :=
    (congrArg M.flen hz).symm.trans (M.flen_iterate _ _)
  have hp1 : M.flen (M.next (M.opp y)) = M.flen (M.opp y) := M.flen_iterate (M.opp y) 1
  have hkp : k + 1 ≤ M.flen (M.next (M.opp y)) := by
    rw [hp1]
    exact M.le_flen_opp_of_glued h hk
  have e3 : M.next^[M.flen (M.next (M.opp y)) - (k + 1)] (M.next (M.opp y)) =
      M.opp (M.next^[k] y) := by
    calc M.next^[M.flen (M.next (M.opp y)) - (k + 1)] (M.next (M.opp y))
        = M.next^[M.flen (M.next (M.opp y)) - (k + 1)]
            (M.next^[k + 1] (M.opp (M.next^[k] y))) := by rw [hz]
      _ = M.next^[M.flen (M.next (M.opp y)) - (k + 1) + (k + 1)] (M.opp (M.next^[k] y)) :=
          (Function.iterate_add_apply M.next _ _ _).symm
      _ = M.next^[M.flen (M.opp (M.next^[k] y))] (M.opp (M.next^[k] y)) := by
          rw [Nat.sub_add_cancel hkp, hper]
      _ = M.opp (M.next^[k] y) := M.iterate_flen _
  have hsplit : M.wordFrom (M.next (M.opp y)) =
      M.run (M.next (M.opp y)) (M.flen (M.next (M.opp y)) - (k + 1)) ++
        M.run (M.opp (M.next^[k] y)) (k + 1) := by
    have e4 : M.wordFrom (M.next (M.opp y)) =
        M.run (M.next (M.opp y)) (M.flen (M.next (M.opp y)) - (k + 1) + (k + 1)) := by
      show M.run _ (M.flen (M.next (M.opp y))) = _
      rw [Nat.sub_add_cancel hkp]
    rw [e4, M.run_add (M.next (M.opp y)) (M.flen (M.next (M.opp y)) - (k + 1)) (k + 1), e3]
  rw [hsplit, FreeGroup.invRev_append, ← M.invRev_run_of_glued y k h, FreeGroup.invRev_invRev]
  exact List.prefix_append _ _

end LabelledMap

end GroupApproximation.Full.NN07a
