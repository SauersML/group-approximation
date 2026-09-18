import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiTowerCoords
import GroupApproximation.Meta.AxiomGuard

/-!
# Selection sort on Kakutani–Rokhlin towers: the invariant

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–315 (Matui, Lemma 3.4 and Theorem 4.9).

Let `g ∈ [[T]]` move points by at most `M` along their orbits, and let `Y` be a clopen set met by
every orbit with bounded gaps. Outside the thin set `thin T Y M`, `g` preserves every
Kakutani–Rokhlin tower over `Y` (`isCoord_zpow_of_notMem_thin`). We multiply `g` on the left by
level transpositions of towers (`MatuiLevelSwaps`) until it fixes every point outside the thin set.
Levels `m = 0, 1, …` are sorted in turn, and at level `m` the target levels `J = 0, 1, …` are
handled one at a time. This is the combinatorial core of the tower arguments of Matui (Internat. J.
Math. 2006, Lemma 3.4, §4) and Grigorchuk–Medynets (2014, §3).

`SortInv T Y M m J g` says, for points `x ∉ thin T Y M`:
1. `g x` stays in the tower of `x`;
2. `g x = x` if `x` sits at a level `< m`;
3. if `x` sits at level `m`, then `g x = x` or `g x` sits at a level `≥ J`.

* `sortInv_start`: the invariant holds for `m = J = 0`;
* `sortInv_step`: a level transposition `m ↔ J` over the bases where `g` sends level `m` to
  level `J` moves `J` to `J + 1`;
* `sortInv_succ_of_eq`, `sortInv_terminal`: the trivial steps `J = m` and `J = H + 1`;
* `supportedIn_of_sortInv`: at `m = H + 1`, `g` is supported in the thin set.
-/

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {Y : Set X} {M : ℕ}

/-- The selection-sort invariant on tower coordinates (see the module docstring). -/
def SortInv (T : X ≃ₜ X) (Y : Set X) (M m J : ℕ) (g : Equiv.Perm X) : Prop :=
  (∀ x, x ∉ thin T Y M → ∀ y a, IsCoord T Y y a x → ∃ b, IsCoord T Y y b (g x)) ∧
  (∀ x, x ∉ thin T Y M → ∀ y a, IsCoord T Y y a x → a < m → g x = x) ∧
  (∀ x, x ∉ thin T Y M → ∀ y, IsCoord T Y y m x → g x = x ∨ ∀ b, IsCoord T Y y b (g x) → J ≤ b)

theorem sortInv_start {g : Equiv.Perm X}
    (hg : ∀ x, ∃ k : ℤ, -(M : ℤ) ≤ k ∧ k ≤ M ∧ g x = (T ^ k) x) : SortInv T Y M 0 0 g := by
  refine ⟨fun x hx y a hc => ?_, fun _ _ _ a _ ha => absurd ha (Nat.not_lt_zero a),
    fun _ _ _ _ => Or.inr fun b _ => Nat.zero_le b⟩
  obtain ⟨k, hk1, hk2, hk⟩ := hg x
  rw [hk]
  exact isCoord_zpow_of_notMem_thin hx hc hk1 hk2

theorem sortInv_succ_of_eq {m : ℕ} {g : Equiv.Perm X} (h : SortInv T Y M m m g) :
    SortInv T Y M m (m + 1) g := by
  refine ⟨h.1, h.2.1, fun x hx y hc => ?_⟩
  rcases h.2.2 x hx y hc with hgx | hB
  · exact Or.inl hgx
  · by_cases hgx : g x = x
    · exact Or.inl hgx
    · refine Or.inr fun b hb => ?_
      have hbm := hB b hb
      have hne : b ≠ m := by
        intro hbm'
        apply hgx
        rw [← hb.2.2, hbm', hc.2.2]
      omega

theorem sortInv_terminal {H m : ℕ} (hret : ∀ x : X, ∃ j : ℕ, j ≤ H ∧ (T ^ (-(j : ℤ))) x ∈ Y)
    {g : Equiv.Perm X} (h : SortInv T Y M m (H + 1) g) : SortInv T Y M (m + 1) 0 g := by
  refine ⟨h.1, fun x hx y a hc ha => ?_, fun _ _ _ _ => Or.inr fun b _ => Nat.zero_le b⟩
  by_cases ham : a < m
  · exact h.2.1 x hx y a hc ham
  · have e : a = m := by omega
    rw [e] at hc
    rcases h.2.2 x hx y hc with hgx | hB
    · exact hgx
    · obtain ⟨b, hb⟩ := h.1 x hx y m hc
      have h1 := hB b hb
      have h2 := hb.2.1.le_of_ret hret
      omega

theorem supportedIn_of_sortInv {H : ℕ} (hret : ∀ x : X, ∃ j : ℕ, j ≤ H ∧ (T ^ (-(j : ℤ))) x ∈ Y)
    {g : Equiv.Perm X} (h : SortInv T Y M (H + 1) 0 g) :
    HydeLodha.SupportedIn g (thin T Y M) := fun x hx => by
  obtain ⟨y, a, ha, hc⟩ := exists_isCoord hret x
  exact h.2.1 x hx y a hc (by omega)

section LevelSwap

variable {m J : ℕ} {t : Equiv.Perm X} {W : Set X}

/-- A level transposition `m ↔ J` over `W` fixes the points off the levels `m`, `J` over `W`. -/
theorem levelSwap_apply_of_isCoord (hcm : ∀ y ∈ W, IsCoord T Y y m ((T ^ (m : ℤ)) y))
    (hcJ : ∀ y ∈ W, IsCoord T Y y J ((T ^ (J : ℤ)) y))
    (ht2 : ∀ z, (∀ y ∈ W, z ≠ (T ^ (m : ℤ)) y ∧ z ≠ (T ^ (J : ℤ)) y) → t z = z) {z y : X}
    {c : ℕ} (hz : IsCoord T Y y c z) (hc : y ∉ W ∨ (c ≠ m ∧ c ≠ J)) : t z = z := by
  refine ht2 z fun y' hy' => ⟨fun he => ?_, fun he => ?_⟩
  · have hu := isCoord_unique hz (show IsCoord T Y y' m z by rw [he]; exact hcm y' hy')
    rcases hc with hc | hc
    · exact hc (by rw [hu.2]; exact hy')
    · exact hc.1 hu.1
  · have hu := isCoord_unique hz (show IsCoord T Y y' J z by rw [he]; exact hcJ y' hy')
    rcases hc with hc | hc
    · exact hc (by rw [hu.2]; exact hy')
    · exact hc.2 hu.1

/-- A level transposition over `W` preserves every tower. -/
theorem levelSwap_isCoord (hcm : ∀ y ∈ W, IsCoord T Y y m ((T ^ (m : ℤ)) y))
    (hcJ : ∀ y ∈ W, IsCoord T Y y J ((T ^ (J : ℤ)) y))
    (ht1 : ∀ y ∈ W, t ((T ^ (m : ℤ)) y) = (T ^ (J : ℤ)) y ∧ t ((T ^ (J : ℤ)) y) = (T ^ (m : ℤ)) y)
    (ht2 : ∀ z, (∀ y ∈ W, z ≠ (T ^ (m : ℤ)) y ∧ z ≠ (T ^ (J : ℤ)) y) → t z = z) {z y : X}
    {c : ℕ} (hz : IsCoord T Y y c z) : ∃ c', IsCoord T Y y c' (t z) := by
  by_cases hyW : y ∈ W
  · by_cases hcm' : c = m
    · have e : z = (T ^ (m : ℤ)) y := by rw [← hz.2.2, hcm']
      exact ⟨J, by rw [e, (ht1 y hyW).1]; exact hcJ y hyW⟩
    · by_cases hcJ' : c = J
      · have e : z = (T ^ (J : ℤ)) y := by rw [← hz.2.2, hcJ']
        exact ⟨m, by rw [e, (ht1 y hyW).2]; exact hcm y hyW⟩
      · exact ⟨c, by rw [levelSwap_apply_of_isCoord hcm hcJ ht2 hz (Or.inr ⟨hcm', hcJ'⟩)]; exact hz⟩
  · exact ⟨c, by rw [levelSwap_apply_of_isCoord hcm hcJ ht2 hz (Or.inl hyW)]; exact hz⟩

/-- **Sorting step** (Matui 2006, Lemma 3.4, §4; tex l.307–315): composing with the level
transposition `m ↔ J` over the bases where `g` sends level `m` to level `J` advances `J`. -/
theorem sortInv_step (hJm : J ≠ m) {g : Equiv.Perm X} (h : SortInv T Y M m J g)
    (hW : ∀ y, y ∈ W ↔ y ∈ Y ∧ NoReturn T Y y m ∧ NoReturn T Y y J ∧
      (T ^ (m : ℤ)) y ∉ thin T Y M ∧ g ((T ^ (m : ℤ)) y) = (T ^ (J : ℤ)) y)
    (ht1 : ∀ y ∈ W, t ((T ^ (m : ℤ)) y) = (T ^ (J : ℤ)) y ∧ t ((T ^ (J : ℤ)) y) = (T ^ (m : ℤ)) y)
    (ht2 : ∀ z, (∀ y ∈ W, z ≠ (T ^ (m : ℤ)) y ∧ z ≠ (T ^ (J : ℤ)) y) → t z = z) :
    SortInv T Y M m (J + 1) (t * g) := by
  have hcm : ∀ y ∈ W, IsCoord T Y y m ((T ^ (m : ℤ)) y) := fun y hy =>
    ⟨((hW y).mp hy).1, ((hW y).mp hy).2.1, rfl⟩
  have hcJ : ∀ y ∈ W, IsCoord T Y y J ((T ^ (J : ℤ)) y) := fun y hy =>
    ⟨((hW y).mp hy).1, ((hW y).mp hy).2.2.1, rfl⟩
  refine ⟨fun x hx y a hc => ?_, fun x hx y a hc ha => ?_, fun x hx y hc => ?_⟩
  · obtain ⟨b, hb⟩ := h.1 x hx y a hc
    exact levelSwap_isCoord hcm hcJ ht1 ht2 hb
  · have hgx := h.2.1 x hx y a hc ha
    show t (g x) = x
    rw [hgx]
    refine levelSwap_apply_of_isCoord hcm hcJ ht2 hc ?_
    by_cases hyW : y ∈ W
    · refine Or.inr ⟨by omega, fun haJ => ?_⟩
      have e : (T ^ (m : ℤ)) y = x := by
        apply g.injective
        rw [((hW y).mp hyW).2.2.2.2, hgx, ← hc.2.2, haJ]
      have hu := isCoord_unique (hcm y hyW)
        (show IsCoord T Y y a ((T ^ (m : ℤ)) y) by rw [e]; exact hc)
      have hma := hu.1
      omega
    · exact Or.inl hyW
  · rcases h.2.2 x hx y hc with hgx | hB
    · refine Or.inl ?_
      show t (g x) = x
      rw [hgx]
      refine levelSwap_apply_of_isCoord hcm hcJ ht2 hc (Or.inl fun hyW => hJm ?_)
      have e : (T ^ (J : ℤ)) y = (T ^ (m : ℤ)) y := by
        rw [← ((hW y).mp hyW).2.2.2.2, hc.2.2, hgx]
      exact (isCoord_unique (hcJ y hyW)
        (show IsCoord T Y y m ((T ^ (J : ℤ)) y) by rw [e]; exact hcm y hyW)).1
    · obtain ⟨b0, hb0⟩ := h.1 x hx y m hc
      by_cases hyW : y ∈ W
      · refine Or.inl ?_
        show t (g x) = x
        rw [← hc.2.2, ((hW y).mp hyW).2.2.2.2, (ht1 y hyW).2]
      · have hb0J : b0 ≠ J := by
          intro hbJ
          refine hyW ((hW y).mpr ⟨hc.1, hc.2.1, by rw [← hbJ]; exact hb0.2.1,
            by rw [hc.2.2]; exact hx, by rw [hc.2.2, ← hb0.2.2, hbJ]⟩)
        have htg : t (g x) = g x := levelSwap_apply_of_isCoord hcm hcJ ht2 hb0 (Or.inl hyW)
        refine Or.inr fun b hb => ?_
        have hb' : IsCoord T Y y b (g x) := by
          rw [← htg]
          exact hb
        have h1 := (isCoord_unique hb' hb0).1
        have h2 := hB b hb'
        omega

end LevelSwap

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.sortInv_start
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.sortInv_step
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.sortInv_terminal
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.supportedIn_of_sortInv
