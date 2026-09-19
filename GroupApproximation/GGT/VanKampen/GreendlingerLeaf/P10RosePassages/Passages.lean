import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.Basic
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.Residual
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketClosedWalkNoncrossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchIsolated
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchFirstTurn
import GroupApproximation.Meta.AxiomGuard

/-!
# In the rose configuration some vertex carries at least three passages

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane ms-nm-uncond-b formalizes this
sub-step of the quadrant move (`P10FilterMoveExists.p10FM_QuadrantMoveStatement`, lane gl-p10-91 of
the other session).  Lane nm-gl03d named it and gave the paper proof.

Let `c` be the boundary cycle of a face set `F`, in walk order.  At a vertex `v`, the *outs* are the
darts of `c` that start at `v`, and the *ins* are the darts of `c` that end at `v`.

* **(a) Alternation.**
  - Rotating from an out `e`, the first dart on an edge of `c` is the reversal of an in
    (`p10RP_alpha_mem_of_firstEdge_out`). The face of `σ e` is the face of `α e`, which is off `F`,
    and darts off the edges of `c` keep the corners off `F` (`p10RP_faceOf_sigma_pow_not_mem`).
  - Rotating from the reversal of an in, the first such dart is an out
    (`p10RP_mem_of_firstEdge_alpha`, from `BoundaryCycle.turn_mem_cycle`).
* **(b) Two passages** (`p10RP_not_turnCrossed`). Suppose at most two darts of `c` end at the
  vertex of a non-first turn `d₀ → e₀`. Then the turn is not crossed:
  - The first edge dart after `e₀` is `α d₁`, where `d₁` is the other in.
  - If the first edge dart after `α d₀` were not `e₀`, the first-edge steps would close up on a
    proper subset of the four edge darts at `v`. That is impossible, since rotation reaches every
    edge dart of the vertex (`p10RP_mem_of_closed`).
  - So the sector from `α d₀` to `e₀` holds no edge dart; in particular it holds neither `α d₁`
    nor `e₁`.
* **(c) Conclusion.**
  - If every vertex carries at most two passages, the rose premise `p10FM_AllCrossed` gives
    first-turn order (`p10RP_firstTurns_of_atMostTwo`).
  - So under the premises of the quadrant move, some vertex carries at least three passages
    (`p10RP_not_atMostTwo`).

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams, residual 10).  It certifies
no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages

universe v

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

open scoped Classical

variable {M : CombMap.{v}} {F : Finset M.Face}

/-- The reversal of a boundary dart is not a boundary dart. -/
theorem p10RP_alpha_not_mem (c : BoundaryCycle M F) {x : M.Dart} (hx : x ∈ c.cycle) :
    M.alpha x ∉ c.cycle := fun hax => by
  have h1 : M.faceOf x ∈ F ∧ M.faceOf (M.alpha x) ∉ F := (c.cycle_mem_iff x).mp hx
  have h2 : M.faceOf (M.alpha x) ∈ F ∧ M.faceOf (M.alpha (M.alpha x)) ∉ F :=
    (c.cycle_mem_iff _).mp hax
  exact h1.2 h2.1

/-- **(a), outs.**  Rotating from a boundary dart `e` past darts off the edges of the cycle stays
in faces off `F`. -/
theorem p10RP_faceOf_sigma_pow_not_mem (c : BoundaryCycle M F) {e : M.Dart} (he : e ∈ c.cycle) :
    ∀ k : ℕ, 0 < k → (∀ j, 0 < j → j < k → ¬ walkKeep M c.cycle ((M.sigma ^ j) e)) →
      M.faceOf ((M.sigma ^ k) e) ∉ F := by
  intro k
  induction k with
  | zero => intro hk; exact absurd hk (Nat.lt_irrefl 0)
  | succ k ih =>
      intro _ havoid
      have hstep : (M.sigma ^ (k + 1)) e = M.facePerm (M.alpha ((M.sigma ^ k) e)) := by
        change (M.sigma ^ (k + 1)) e = M.sigma (M.alpha (M.alpha ((M.sigma ^ k) e)))
        rw [M.alpha_involutive ((M.sigma ^ k) e), pow_succ', Perm.mul_apply]
      rw [hstep, M.faceOf_facePerm]
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [pow_zero, Perm.one_apply]
        have hb : M.faceOf e ∈ F ∧ M.faceOf (M.alpha e) ∉ F := (c.cycle_mem_iff e).mp he
        exact hb.2
      · have hy : M.faceOf ((M.sigma ^ k) e) ∉ F :=
          ih hpos fun j hj hjk => havoid j hj (Nat.lt_succ_of_lt hjk)
        have hoff : ¬ walkKeep M c.cycle ((M.sigma ^ k) e) := havoid k hpos (Nat.lt_succ_self k)
        intro hin
        have hb : M.faceOf (M.alpha ((M.sigma ^ k) e)) ∈ F ∧
            M.faceOf (M.alpha (M.alpha ((M.sigma ^ k) e))) ∉ F := by
          refine ⟨hin, ?_⟩
          rw [M.alpha_involutive]
          exact hy
        exact hoff (show (M.sigma ^ k) e ∈ c.cycle ∨ M.alpha ((M.sigma ^ k) e) ∈ c.cycle from
          Or.inr ((c.cycle_mem_iff _).mpr hb))

/-- **(a), outs.**  The first edge dart after a boundary dart is the reversal of a boundary
dart. -/
theorem p10RP_alpha_mem_of_firstEdge_out (c : BoundaryCycle M F) {e z : M.Dart} {a : ℕ}
    (he : e ∈ c.cycle) (h : p10RP_FirstEdge M c.cycle e z a) : M.alpha z ∈ c.cycle := by
  obtain ⟨ha, rfl, hk, hav⟩ := h
  have hface := p10RP_faceOf_sigma_pow_not_mem c he a ha hav
  have hk' : (M.sigma ^ a) e ∈ c.cycle ∨ M.alpha ((M.sigma ^ a) e) ∈ c.cycle := hk
  rcases hk' with hmem | hrev
  · have hb : M.faceOf ((M.sigma ^ a) e) ∈ F ∧ M.faceOf (M.alpha ((M.sigma ^ a) e)) ∉ F :=
      (c.cycle_mem_iff _).mp hmem
    exact absurd hb.1 hface
  · exact hrev

/-- **(a), ins.**  The first edge dart after the reversal of a boundary dart is a boundary
dart. -/
theorem p10RP_mem_of_firstEdge_alpha (c : BoundaryCycle M F) {d z : M.Dart} {a : ℕ}
    (hd : d ∈ c.cycle) (h : p10RP_FirstEdge M c.cycle (M.alpha d) z a) : z ∈ c.cycle := by
  obtain ⟨ha, rfl, hk, hav⟩ := h
  exact c.turn_mem_cycle hd a ha hk hav

/-- In walk order, a dart ends where the next one starts. -/
theorem p10RP_sameCycle_next (c : BoundaryCycle M F) (hw : IsClosedDartWalk M c.cycle)
    {d : M.Dart} (hd : d ∈ c.cycle) : M.sigma.SameCycle (M.alpha d) (c.cycle.next d hd) := by
  obtain ⟨hne, hchain, hclose⟩ := hw
  have h := OuterPinchIsolated.rel_next_of_isChain
    (R := fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) hne c.cycle_nodup hchain hclose hd
  exact (M.vertexOf_eq_iff _ _).mp h

/-- With at most two passages, an out at the vertex of two distinct ins is the successor of one
of them. -/
theorem p10RP_out_eq (c : BoundaryCycle M F) (hw : IsClosedDartWalk M c.cycle)
    (htwo : p10RP_AtMostTwoPassages M c.cycle) {d₀ d₁ : M.Dart} (hd₀ : d₀ ∈ c.cycle)
    (hd₁ : d₁ ∈ c.cycle) (hne : d₁ ≠ d₀) (hsame : M.sigma.SameCycle (M.alpha d₀) (M.alpha d₁))
    {o : M.Dart} (ho : o ∈ c.cycle) (hvo : M.sigma.SameCycle (M.alpha d₀) o) :
    o = c.cycle.next d₀ hd₀ ∨ o = c.cycle.next d₁ hd₁ := by
  have hp : c.cycle.prev o ho ∈ c.cycle := List.prev_mem _ _ _
  have hnp : c.cycle.next (c.cycle.prev o ho) hp = o := List.next_prev _ c.cycle_nodup _ _
  have hvp : M.sigma.SameCycle (M.alpha d₀) (M.alpha (c.cycle.prev o ho)) := by
    have h := p10RP_sameCycle_next c hw hp
    rw [hnp] at h
    exact hvo.trans h.symm
  have hkey : ∀ (a b : M.Dart) (ha : a ∈ c.cycle) (hb : b ∈ c.cycle), a = b →
      c.cycle.next a ha = c.cycle.next b hb := by
    rintro a b ha hb rfl
    rfl
  rcases htwo d₀ hd₀ d₁ hd₁ (c.cycle.prev o ho) hp hsame hvp with h | h | h
  · exact absurd h.symm hne
  · left
    rw [← hnp]
    exact hkey _ _ _ _ h.symm
  · right
    rw [← hnp]
    exact hkey _ _ _ _ h.symm

/-- With at most two passages, the reversal of an in at the vertex of two distinct ins is the
reversal of one of them. -/
theorem p10RP_alphaIn_eq {C : List M.Dart} (htwo : p10RP_AtMostTwoPassages M C)
    {d₀ d₁ : M.Dart} (hd₀ : d₀ ∈ C) (hd₁ : d₁ ∈ C) (hne : d₁ ≠ d₀)
    (hsame : M.sigma.SameCycle (M.alpha d₀) (M.alpha d₁)) {y : M.Dart} (hy : M.alpha y ∈ C)
    (hvy : M.sigma.SameCycle (M.alpha d₀) y) : y = M.alpha d₀ ∨ y = M.alpha d₁ := by
  have hvy' : M.sigma.SameCycle (M.alpha d₀) (M.alpha (M.alpha y)) := by
    rw [M.alpha_involutive]
    exact hvy
  rcases htwo d₀ hd₀ d₁ hd₁ (M.alpha y) hy hsame hvy' with h | h | h
  · exact absurd h.symm hne
  · left
    rw [h, M.alpha_involutive]
  · right
    rw [h, M.alpha_involutive]

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.p10RP_alpha_mem_of_firstEdge_out
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.p10RP_mem_of_firstEdge_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.p10RP_out_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.p10RP_alphaIn_eq
