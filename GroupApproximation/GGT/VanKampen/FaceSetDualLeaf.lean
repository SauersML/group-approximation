import GroupApproximation.GGT.VanKampen.CombMap

/-!
# A finite connected carrier has a removable point

The extremal-face argument needs one purely finite fact about the selected-face
dual graph: a finite connected carrier with more than one point has a point
whose deletion leaves every other point still connected to a fixed root.  That
is the leaf of a spanning tree, and the proof here is the usual one without any
tree: take a point at maximal distance from the root.  A shortest walk to any
other point cannot pass through it, because the prefix of that walk would reach
it sooner than its own distance.

Nothing here mentions maps, faces or darts.  `ReachIn s r n a b` is reachability
from `a` to `b` in at most `n` steps of `r`, with every intermediate point
required to lie in the carrier `s`, so deleting a point from `s` genuinely
forbids walks through it.  The relation `r` is arbitrary; the selected-face dual
`SelectedFaceAdjacency` is symmetric, but symmetry is not needed for this
statement.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

universe u

/-- Reachability inside a finite carrier in at most `n` steps.  Every point
entered along the way is required to lie in the carrier. -/
def ReachIn {α : Type u} (s : Finset α) (r : α → α → Prop) :
    ℕ → α → α → Prop
  | 0, a, b => a = b
  | n + 1, a, b =>
      ReachIn s r n a b ∨ ∃ c, c ∈ s ∧ ReachIn s r n a c ∧ r c b

theorem reachIn_zero_iff {α : Type u} {s : Finset α} {r : α → α → Prop}
    {a b : α} : ReachIn s r 0 a b ↔ a = b := by
  simp only [ReachIn]

theorem reachIn_succ_iff {α : Type u} {s : Finset α} {r : α → α → Prop}
    {n : ℕ} {a b : α} :
    ReachIn s r (n + 1) a b ↔
      ReachIn s r n a b ∨ ∃ c, c ∈ s ∧ ReachIn s r n a c ∧ r c b := by
  simp only [ReachIn]

/-- Every point reaches itself in no steps. -/
theorem reachIn_refl {α : Type u} (s : Finset α) (r : α → α → Prop) (a : α) :
    ReachIn s r 0 a a := reachIn_zero_iff.mpr rfl

/-- Reachability in at most `n` steps is monotone in `n`. -/
theorem ReachIn.mono {α : Type u} {s : Finset α} {r : α → α → Prop}
    {a b : α} {n : ℕ} (h : ReachIn s r n a b) :
    ∀ m : ℕ, n ≤ m → ReachIn s r m a b := by
  intro m
  induction m with
  | zero =>
      intro hnm
      have hn : n = 0 := Nat.le_zero.mp hnm
      rw [hn] at h
      exact h
  | succ m ih =>
      intro hnm
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · exact reachIn_succ_iff.mpr (Or.inl (ih (by omega)))
      · have hn : n = m + 1 := by omega
        rw [hn] at h
        exact h

/-- A finite carrier in which every point is reachable from a root, and which
has more than one point, has a point other than the root whose deletion leaves
every other point reachable from the root.  This is the spanning-tree leaf used
by the extremal-face argument. -/
theorem exists_erase_reachable {α : Type u} [DecidableEq α]
    (s : Finset α) (r : α → α → Prop) (root : α) (hroot : root ∈ s)
    (hreach : ∀ b ∈ s, ∃ n, ReachIn s r n root b)
    (hcard : 1 < s.card) :
    ∃ f, f ∈ s ∧ f ≠ root ∧
      ∀ b ∈ s, b ≠ f → ∃ n, ReachIn (s.erase f) r n root b := by
  classical
  have hex : ∀ b : α, ∃ n : ℕ, ReachIn s r n root b ∨ b ∉ s := by
    intro b
    by_cases hb : b ∈ s
    · obtain ⟨n, hn⟩ := hreach b hb
      exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr hb⟩
  have hspec : ∀ b ∈ s, ReachIn s r (Nat.find (hex b)) root b := by
    intro b hb
    rcases Nat.find_spec (hex b) with h | h
    · exact h
    · exact absurd hb h
  have hle : ∀ (b : α) (n : ℕ), ReachIn s r n root b →
      Nat.find (hex b) ≤ n := by
    intro b n h
    exact Nat.find_le (Or.inl h)
  have hpos : ∀ b ∈ s, b ≠ root → 0 < Nat.find (hex b) := by
    intro b hb hbroot
    rcases Nat.eq_zero_or_pos (Nat.find (hex b)) with h0 | hp
    · exfalso
      have hz := hspec b hb
      rw [h0] at hz
      exact hbroot (reachIn_zero_iff.mp hz).symm
    · exact hp
  obtain ⟨f, hfs, hfmax⟩ :=
    Finset.exists_max_image s (fun b => Nat.find (hex b)) ⟨root, hroot⟩
  have hrootzero : Nat.find (hex root) = 0 :=
    Nat.le_zero.mp (hle root 0 (reachIn_refl s r root))
  have hfpos : 0 < Nat.find (hex f) := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
    by_cases haroot : a = root
    · have hbroot : b ≠ root := by
        rw [← haroot]
        exact fun hcon => hab hcon.symm
      exact lt_of_lt_of_le (hpos b hb hbroot) (hfmax b hb)
    · exact lt_of_lt_of_le (hpos a ha haroot) (hfmax a ha)
  have hfroot : f ≠ root := by
    intro hcon
    rw [hcon, hrootzero] at hfpos
    omega
  refine ⟨f, hfs, hfroot, ?_⟩
  have key : ∀ n : ℕ, ∀ b ∈ s, b ≠ f → Nat.find (hex b) = n →
      ∃ m, ReachIn (s.erase f) r m root b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro b hb hbf hDb
      rcases n with _ | m
      · have hz : ReachIn s r 0 root b := by
          have h := hspec b hb
          rw [hDb] at h
          exact h
        exact ⟨0, reachIn_zero_iff.mpr (reachIn_zero_iff.mp hz)⟩
      · have hsucc : ReachIn s r (m + 1) root b := by
          have h := hspec b hb
          rw [hDb] at h
          exact h
        have hnot : ¬ ReachIn s r m root b := by
          intro hcon
          have hlem := hle b m hcon
          omega
        obtain ⟨c, hcs, hcr, hcb⟩ :
            ∃ c, c ∈ s ∧ ReachIn s r m root c ∧ r c b := by
          rcases reachIn_succ_iff.mp hsucc with h | h
          · exact absurd h hnot
          · exact h
        have hDc : Nat.find (hex c) ≤ m := hle c m hcr
        have hcf : c ≠ f := by
          intro hcon
          rw [hcon] at hDc
          have hmaxb := hfmax b hb
          omega
        obtain ⟨p, hp⟩ := ih (Nat.find (hex c)) (by omega) c hcs hcf rfl
        exact ⟨p + 1, reachIn_succ_iff.mpr
          (Or.inr ⟨c, Finset.mem_erase.mpr ⟨hcf, hcs⟩, hp, hcb⟩)⟩
  intro b hb hbf
  exact key (Nat.find (hex b)) b hb hbf rfl

end Embedded
end VanKampen
end GGT
end GroupApproximation
