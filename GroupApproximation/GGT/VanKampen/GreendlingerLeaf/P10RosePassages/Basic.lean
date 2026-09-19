import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEulerNoninterleaving
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Rotation around a vertex: first edge darts

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane ms-nm-uncond-b.  This is the
vocabulary for `P10RosePassages/Passages`, a sub-step of the quadrant move
(`P10FilterMoveExists.p10FM_QuadrantMoveStatement`) named by lane nm-gl03d.

* `p10RP_FirstEdge M C y z a`: rotating `a > 0` steps from `y` reaches the first dart `z` on an
  edge of `C`.  It exists from every edge dart (`p10RP_exists_firstEdge`) and is unique
  (`p10RP_firstEdge_unique`).
* `p10RP_mem_of_closed`: a set of edge darts closed under first-edge steps holds every edge dart
  met rotating from any of its members.  So a proper subset of the edge darts at a vertex is never
  closed.
* `p10RP_AtMostTwoPassages`: at most two darts of `C` end at any vertex.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams, residual 10).  It certifies
no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages

universe v

open Equiv SimpleClosedWalkSides

open scoped Classical

section Vocabulary

variable (M : CombMap.{v})

/-- **The first edge dart after `y`.**  Rotating `a > 0` steps from `y` reaches `z`, a dart on an
edge of `C`, and no earlier step is on an edge of `C`. -/
def p10RP_FirstEdge (C : List M.Dart) (y z : M.Dart) (a : ℕ) : Prop :=
  0 < a ∧ (M.sigma ^ a) y = z ∧ walkKeep M C z ∧
    ∀ t, 0 < t → t < a → ¬ walkKeep M C ((M.sigma ^ t) y)

/-- **At most two passages at every vertex**: of any three darts of `C` ending at one vertex, two
are equal. -/
def p10RP_AtMostTwoPassages (C : List M.Dart) : Prop :=
  ∀ d₁ ∈ C, ∀ d₂ ∈ C, ∀ d₃ ∈ C, M.sigma.SameCycle (M.alpha d₁) (M.alpha d₂) →
    M.sigma.SameCycle (M.alpha d₁) (M.alpha d₃) → d₁ = d₂ ∨ d₁ = d₃ ∨ d₂ = d₃

end Vocabulary

section Rotation

variable {M : CombMap.{v}}

/-- The first edge dart is unique. -/
theorem p10RP_firstEdge_unique {C : List M.Dart} {y z z' : M.Dart} {a a' : ℕ}
    (h : p10RP_FirstEdge M C y z a) (h' : p10RP_FirstEdge M C y z' a') : a = a' ∧ z = z' := by
  obtain ⟨ha, hz, hk, hav⟩ := h
  obtain ⟨ha', hz', hk', hav'⟩ := h'
  have haa : a = a' := by
    rcases lt_trichotomy a a' with hlt | heq | hgt
    · exact ((hav' a ha hlt) (by rw [hz]; exact hk)).elim
    · exact heq
    · exact ((hav a' ha' hgt) (by rw [hz']; exact hk')).elim
  subst haa
  exact ⟨rfl, hz.symm.trans hz'⟩

/-- Rotating from a dart on an edge of `C` meets a first edge dart. -/
theorem p10RP_exists_firstEdge {C : List M.Dart} {y : M.Dart} (hy : walkKeep M C y) :
    ∃ a z, p10RP_FirstEdge M C y z a := by
  classical
  have hex : ∃ a, 0 < a ∧ walkKeep M C ((M.sigma ^ a) y) := by
    refine ⟨orderOf M.sigma, orderOf_pos _, ?_⟩
    rw [pow_orderOf_eq_one, Perm.one_apply]
    exact hy
  refine ⟨Nat.find hex, _, (Nat.find_spec hex).1, rfl, (Nat.find_spec hex).2,
    fun t ht hta hk => ?_⟩
  exact Nat.find_min hex hta ⟨ht, hk⟩

/-- **Closed first-edge steps cover the vertex.**  If a set `S` of darts contains `x`, and the
first edge dart after each member of `S` is again in `S`, then every edge dart met rotating
from `x` is in `S`. -/
theorem p10RP_mem_of_closed {C : List M.Dart} {S : M.Dart → Prop} {x : M.Dart} (hx : S x)
    (hS : ∀ y, S y → ∃ a z, p10RP_FirstEdge M C y z a ∧ S z) :
    ∀ k, walkKeep M C ((M.sigma ^ k) x) → S ((M.sigma ^ k) x) := by
  have hinv : ∀ k, ∃ j ≤ k, S ((M.sigma ^ j) x) ∧
      ∀ t, j < t → t ≤ k → ¬ walkKeep M C ((M.sigma ^ t) x) := by
    intro k
    induction k with
    | zero =>
        refine ⟨0, le_refl 0, ?_, fun t h1 h2 => absurd (lt_of_lt_of_le h1 h2) (lt_irrefl 0)⟩
        rw [pow_zero, Perm.one_apply]
        exact hx
    | succ k ih =>
        obtain ⟨j, hjk, hSj, hgap⟩ := ih
        by_cases hk : walkKeep M C ((M.sigma ^ (k + 1)) x)
        · refine ⟨k + 1, le_refl _, ?_, fun t h1 h2 => absurd h2 (not_le.mpr h1)⟩
          obtain ⟨a, z, hfe, hSz⟩ := hS _ hSj
          have hfe' : p10RP_FirstEdge M C ((M.sigma ^ j) x) ((M.sigma ^ (k + 1)) x)
              (k + 1 - j) := by
            refine ⟨by omega, ?_, hk, fun t ht htk => ?_⟩
            · rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (by omega : j ≤ k + 1)]
            · rw [← Perm.mul_apply, ← pow_add]
              exact hgap (t + j) (by omega) (by omega)
          obtain ⟨-, hzeq⟩ := p10RP_firstEdge_unique hfe hfe'
          rw [← hzeq]
          exact hSz
        · refine ⟨j, by omega, hSj, fun t h1 h2 => ?_⟩
          rcases Nat.lt_or_ge t (k + 1) with hlt | hge
          · exact hgap t h1 (by omega)
          · have ht : t = k + 1 := by omega
            subst ht
            exact hk
  intro k hk
  obtain ⟨j, hjk, hSj, hgap⟩ := hinv k
  rcases Nat.lt_or_ge j k with hlt | hge
  · exact absurd hk (hgap k hlt le_rfl)
  · have hj : j = k := by omega
    subst hj
    exact hSj

/-- **A dart outside a sector** (as `NoncrossingClosedWalkEulerNoninterleavingModels`). -/
theorem p10RP_not_rotationBetween_of_first {x y z : M.Dart} {a₀ : ℕ} (ha₀ : 0 < a₀)
    (h : (M.sigma ^ a₀) x = y) (hz : ∀ b, 0 < b → b < a₀ → (M.sigma ^ b) x ≠ z) :
    ¬ RotationBetween M x y z := by
  rintro ⟨a, ha, hza, hb⟩
  rcases Nat.lt_or_ge a a₀ with hlt | hge
  · exact hz a ha hlt hza
  · exact hb a₀ ha₀ hge h

/-- Rotation stays at the vertex. -/
theorem p10RP_sameCycle_pow {x y : M.Dart} (h : M.sigma.SameCycle x y) (n : ℕ) :
    M.sigma.SameCycle x ((M.sigma ^ n) y) := by
  rw [← M.vertexOf_eq_iff, FirstTurnWalk.vertexOf_sigma_pow, M.vertexOf_eq_iff]
  exact h

theorem p10RP_walkKeep_of_mem {C : List M.Dart} {x : M.Dart} (hx : x ∈ C) : walkKeep M C x :=
  show x ∈ C ∨ M.alpha x ∈ C from Or.inl hx

theorem p10RP_walkKeep_alpha_of_mem {C : List M.Dart} {x : M.Dart} (hx : x ∈ C) :
    walkKeep M C (M.alpha x) :=
  show M.alpha x ∈ C ∨ M.alpha (M.alpha x) ∈ C from
    Or.inr (by rw [M.alpha_involutive]; exact hx)

end Rotation

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.p10RP_mem_of_closed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.p10RP_exists_firstEdge
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.p10RP_firstEdge_unique
