import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.Passages
import GroupApproximation.Meta.AxiomGuard

/-!
# Two passages: a non-first turn is not crossed

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane ms-nm-uncond-b; the paper proof is
lane nm-gl03d's.  Steps (b) and (c) of `P10RosePassages/Passages`:

* `p10RP_not_turnCrossed`: at a vertex where at most two darts of the boundary cycle end, a
  non-first turn is not crossed;
* `p10RP_firstTurns_of_atMostTwo`: if every vertex carries at most two passages, the rose premise
  `p10FM_AllCrossed` forces first-turn order;
* `p10RP_not_atMostTwo`: under the premises of `p10FM_QuadrantMoveStatement` (not in first-turn
  order, every non-first turn crossed), some vertex carries at least three passages.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams, residual 10).  It certifies
no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages

universe v

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

open scoped Classical

variable {M : CombMap.{v}} {F : Finset M.Face}

/-- **(b) Two passages.**  If at most two darts of the boundary cycle end at any vertex, a
non-first turn `d₀ → next d₀` is not crossed. -/
theorem p10RP_not_turnCrossed (c : BoundaryCycle M F) (hw : IsClosedDartWalk M c.cycle)
    (htwo : p10RP_AtMostTwoPassages M c.cycle) {d₀ : M.Dart} (hd₀ : d₀ ∈ c.cycle)
    (hnf : P10FilterMoveExists.p10FM_NonFirstTurn M c.cycle d₀ hd₀) :
    ¬ P10FilterMoveExists.p10FM_TurnCrossed M c.cycle d₀ hd₀ := by
  rintro ⟨d₁, hd₁, hne, hsame, hiff⟩
  have he₀ : c.cycle.next d₀ hd₀ ∈ c.cycle := List.next_mem _ _ _
  have he₁ : c.cycle.next d₁ hd₁ ∈ c.cycle := List.next_mem _ _ _
  have hv₀ : M.sigma.SameCycle (M.alpha d₀) (c.cycle.next d₀ hd₀) :=
    p10RP_sameCycle_next c hw hd₀
  have hv₁ : M.sigma.SameCycle (M.alpha d₀) (c.cycle.next d₁ hd₁) :=
    hsame.trans (p10RP_sameCycle_next c hw hd₁)
  have hα : M.alpha d₀ ≠ M.alpha d₁ := fun h => hne (M.alpha.injective h).symm
  have hne₀₁ : c.cycle.next d₀ hd₀ ≠ c.cycle.next d₁ hd₁ := by
    intro h
    have hkey : ∀ (a b : M.Dart) (ha : a ∈ c.cycle) (hb : b ∈ c.cycle), a = b →
        c.cycle.prev a ha = c.cycle.prev b hb := by
      rintro a b ha hb rfl
      rfl
    have h1 := List.prev_next c.cycle c.cycle_nodup d₀ hd₀
    have h2 := List.prev_next c.cycle c.cycle_nodup d₁ hd₁
    exact hne (h2.symm.trans ((hkey _ _ _ _ h).symm.trans h1))
  have hnot : ∀ x ∈ c.cycle, ∀ y ∈ c.cycle, x ≠ M.alpha y := fun x hx y hy h =>
    p10RP_alpha_not_mem c hy (by rw [← h]; exact hx)
  have wk_e₀ := p10RP_walkKeep_of_mem he₀
  have wk_e₁ := p10RP_walkKeep_of_mem he₁
  have wk_a₀ := p10RP_walkKeep_alpha_of_mem hd₀
  have wk_a₁ := p10RP_walkKeep_alpha_of_mem hd₁
  have hsc : ∀ {x y : M.Dart}, M.sigma.SameCycle (M.alpha d₀) x →
      M.sigma.SameCycle (M.alpha d₀) y → ∃ n : ℕ, (M.sigma ^ n) x = y :=
    fun hx hy => (hx.symm.trans hy).exists_nat_pow_eq
  -- the first edge darts after the four edge darts at the vertex
  obtain ⟨a₀, z₀, hF₀⟩ := p10RP_exists_firstEdge wk_e₀
  obtain ⟨a₁, z₁, hF₁⟩ := p10RP_exists_firstEdge wk_e₁
  obtain ⟨b₀, o₀, hG₀⟩ := p10RP_exists_firstEdge wk_a₀
  obtain ⟨b₁, o₁, hG₁⟩ := p10RP_exists_firstEdge wk_a₁
  -- after `e₀` comes `α d₁`: the turn at `d₀` is not first
  obtain ⟨ha₀, hz₀, -, hav₀⟩ := id hF₀
  have hz₀eq : z₀ = M.alpha d₁ := by
    have hmem := p10RP_alpha_mem_of_firstEdge_out c he₀ hF₀
    have hv : M.sigma.SameCycle (M.alpha d₀) z₀ := by
      rw [← hz₀]
      exact p10RP_sameCycle_pow hv₀ a₀
    rcases p10RP_alphaIn_eq htwo hd₀ hd₁ hne hsame hmem hv with h | h
    · exact (hnf (FirstTurn.reverse_map_alpha_iff.mpr ⟨a₀, ha₀, hz₀.trans h, hav₀⟩)).elim
    · exact h
  -- after `e₁` comes `α d₀` or `α d₁`
  obtain ⟨-, hz₁, -, -⟩ := id hF₁
  have hz₁cases : z₁ = M.alpha d₀ ∨ z₁ = M.alpha d₁ := by
    have hmem := p10RP_alpha_mem_of_firstEdge_out c he₁ hF₁
    have hv : M.sigma.SameCycle (M.alpha d₀) z₁ := by
      rw [← hz₁]
      exact p10RP_sameCycle_pow hv₁ a₁
    exact p10RP_alphaIn_eq htwo hd₀ hd₁ hne hsame hmem hv
  -- after `α d₀` and after `α d₁` comes `e₀` or `e₁`
  obtain ⟨-, ho₀, -, -⟩ := id hG₀
  have ho₀cases : o₀ = c.cycle.next d₀ hd₀ ∨ o₀ = c.cycle.next d₁ hd₁ := by
    have hmem := p10RP_mem_of_firstEdge_alpha c hd₀ hG₀
    have hv : M.sigma.SameCycle (M.alpha d₀) o₀ := by
      rw [← ho₀]
      exact p10RP_sameCycle_pow Equiv.Perm.SameCycle.rfl b₀
    exact p10RP_out_eq c hw htwo hd₀ hd₁ hne hsame hmem hv
  obtain ⟨-, ho₁, -, -⟩ := id hG₁
  have ho₁cases : o₁ = c.cycle.next d₀ hd₀ ∨ o₁ = c.cycle.next d₁ hd₁ := by
    have hmem := p10RP_mem_of_firstEdge_alpha c hd₁ hG₁
    have hv : M.sigma.SameCycle (M.alpha d₀) o₁ := by
      rw [← ho₁]
      exact p10RP_sameCycle_pow hsame b₁
    exact p10RP_out_eq c hw htwo hd₀ hd₁ hne hsame hmem hv
  rcases hz₁cases with hz₁eq | hz₁eq
  · rcases ho₀cases with ho₀eq | ho₀eq
    · -- the sector from `α d₀` to `e₀` holds no edge dart
      obtain ⟨hb₀, hob₀, -, hbav⟩ := id hG₀
      rw [ho₀eq] at hob₀
      have hno : ∀ z, walkKeep M c.cycle z →
          ¬ RotationBetween M (M.alpha d₀) (c.cycle.next d₀ hd₀) z :=
        fun z hz => p10RP_not_rotationBetween_of_first hb₀ hob₀
          (fun b hb hbl heq => hbav b hb hbl (by rw [heq]; exact hz))
      exact hiff ⟨fun h => absurd h (hno _ wk_a₁), fun h => absurd h (hno _ wk_e₁)⟩
    · -- `{α d₀, e₁}` is closed under first-edge steps, but `e₀` is at the vertex
      exfalso
      have hS : ∀ y, (y = M.alpha d₀ ∨ y = c.cycle.next d₁ hd₁) →
          ∃ a z, p10RP_FirstEdge M c.cycle y z a ∧
            (z = M.alpha d₀ ∨ z = c.cycle.next d₁ hd₁) := by
        rintro y (rfl | rfl)
        · exact ⟨b₀, o₀, hG₀, Or.inr ho₀eq⟩
        · exact ⟨a₁, z₁, hF₁, Or.inl hz₁eq⟩
      obtain ⟨n, hn⟩ := hsc Equiv.Perm.SameCycle.rfl hv₀
      have hmem : (M.sigma ^ n) (M.alpha d₀) = M.alpha d₀ ∨
          (M.sigma ^ n) (M.alpha d₀) = c.cycle.next d₁ hd₁ :=
        p10RP_mem_of_closed (C := c.cycle)
          (S := fun y => y = M.alpha d₀ ∨ y = c.cycle.next d₁ hd₁) (Or.inl rfl) hS n
          (by rw [hn]; exact wk_e₀)
      rw [hn] at hmem
      rcases hmem with h | h
      · exact hnot _ he₀ _ hd₀ h
      · exact hne₀₁ h
  · -- `{e₀, α d₁, e₁}` is closed under first-edge steps, but `α d₀` is at the vertex
    exfalso
    have hS : ∀ y, (y = c.cycle.next d₀ hd₀ ∨ y = M.alpha d₁ ∨ y = c.cycle.next d₁ hd₁) →
        ∃ a z, p10RP_FirstEdge M c.cycle y z a ∧
          (z = c.cycle.next d₀ hd₀ ∨ z = M.alpha d₁ ∨ z = c.cycle.next d₁ hd₁) := by
      rintro y (rfl | rfl | rfl)
      · exact ⟨a₀, z₀, hF₀, Or.inr (Or.inl hz₀eq)⟩
      · rcases ho₁cases with h | h
        · exact ⟨b₁, o₁, hG₁, Or.inl h⟩
        · exact ⟨b₁, o₁, hG₁, Or.inr (Or.inr h)⟩
      · exact ⟨a₁, z₁, hF₁, Or.inr (Or.inl hz₁eq)⟩
    obtain ⟨n, hn⟩ := hsc hv₀ Equiv.Perm.SameCycle.rfl
    have hmem : (M.sigma ^ n) (c.cycle.next d₀ hd₀) = c.cycle.next d₀ hd₀ ∨
        (M.sigma ^ n) (c.cycle.next d₀ hd₀) = M.alpha d₁ ∨
          (M.sigma ^ n) (c.cycle.next d₀ hd₀) = c.cycle.next d₁ hd₁ :=
      p10RP_mem_of_closed (C := c.cycle)
        (S := fun y => y = c.cycle.next d₀ hd₀ ∨ y = M.alpha d₁ ∨ y = c.cycle.next d₁ hd₁)
        (Or.inl rfl) hS n (by rw [hn]; exact wk_a₀)
    rw [hn] at hmem
    rcases hmem with h | h | h
    · exact hnot _ he₀ _ hd₀ h.symm
    · exact hα h
    · exact hnot _ he₁ _ hd₀ h.symm

/-- **(c)** If every vertex carries at most two passages of the boundary cycle, the rose premise
forces first-turn order. -/
theorem p10RP_firstTurns_of_atMostTwo (c : BoundaryCycle M F) (hw : IsClosedDartWalk M c.cycle)
    (htwo : p10RP_AtMostTwoPassages M c.cycle)
    (hcross : P10FilterMoveExists.p10FM_AllCrossed M c.cycle) :
    P10FilterMoveExists.p10FM_FirstTurns M c.cycle c.cycle_nonempty := by
  refine OuterPinchIsolated.isChain_of_rel_next c.cycle_nonempty c.cycle_nodup
    (R := fun d e => FirstTurn M (c.cycle.reverse.map M.alpha) (M.alpha e) (M.alpha d))
    fun d₀ hd₀ => ?_
  by_contra hnf
  exact p10RP_not_turnCrossed c hw htwo hd₀ hnf (hcross d₀ hd₀ hnf)

/-- **Under the rose premises some vertex carries at least three passages.**  A boundary cycle
in walk order that is not in first-turn order and whose non-first turns are all crossed (the
premises of `p10FM_QuadrantMoveStatement`) has three distinct darts ending at one vertex. -/
theorem p10RP_not_atMostTwo (c : BoundaryCycle M F) (hw : IsClosedDartWalk M c.cycle)
    (hnf : ¬ P10FilterMoveExists.p10FM_FirstTurns M c.cycle c.cycle_nonempty)
    (hcross : P10FilterMoveExists.p10FM_AllCrossed M c.cycle) :
    ¬ p10RP_AtMostTwoPassages M c.cycle := fun htwo =>
  hnf (p10RP_firstTurns_of_atMostTwo c hw htwo hcross)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.p10RP_not_turnCrossed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.p10RP_firstTurns_of_atMostTwo
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.p10RP_not_atMostTwo
