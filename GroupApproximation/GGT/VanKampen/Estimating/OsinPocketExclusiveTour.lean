import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketExclusiveTurns
import GroupApproximation.Meta.AxiomGuard

/-!
# The complement side of the exclusive pocket as one tour

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.7(b).  Route
`research/nm-exclusive-pocket-first-turns.md`.

Let `U` be the face set `x ∪ y ∪ {Π, exterior}`.  The complement spelling of the exclusive pocket
walk runs along `U`: along `x`'s inner side, the gap arc of `∂Π`, `y`'s inner side and the stretch
of `∂Δ`.  Between two consecutive darts it walks around `U`, and at a junction it crosses edges
internal to `U` (a source-arc edge `x | Π`, a target-arc edge `y | exterior`, and so on).  So the
complement spelling is a boundary walk of `U`, and each of its turns is a first turn
(`FirstTurn.of_boundaryWalk`).

This module proves the tour algebra, for any face set `U` and any predicate `B` marking the darts
kept in the spelling.

* `ExclusiveTour.boundaryWalk_mono`: a boundary walk of a subset of `U` is one of `U`.
* `ExclusiveTour.boundaryWalk_of_facePerm`: a face step is a boundary walk.
* `ExclusiveTour.boundaryWalk_trans_internal`: a boundary walk onto an internal dart `b`, then one
  from `alpha b`, is a boundary walk.
* `ExclusiveTour.Hop`: one step of the tour, either a boundary walk onto a kept dart or a jump
  across an internal dart onto a dart that is not kept.
* `ExclusiveTour.hop_skip`: two hops through a dart that is not kept make one hop.
* `ExclusiveTour.isChain_filter_of_skip`: a chain stays a chain after removing elements through
  which the relation composes.
* `ExclusiveTour.isChain_filter_hop`: the kept darts of a tour are a chain of boundary walks of
  `U`.
* `ExclusiveTour.isChain_hop_of_stretch`, `ExclusiveTour.isChain_append_overlap`: a tour is
  assembled from stretches glued at shared darts.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

namespace ExclusiveTour

/-- **Removing elements through which a relation composes keeps a chain.**  If `R a b`, `R b c`
and `¬ B b` give `R a c`, then the elements of a chain satisfying `B` form a chain. -/
theorem isChain_filter_of_skip {α : Type*} {R : α → α → Prop} (B : α → Prop) [DecidablePred B]
    (hskip : ∀ a b c, R a b → ¬ B b → R b c → R a c) :
    ∀ l : List α, l.IsChain R → (l.filter fun a => decide (B a)).IsChain R := by
  have hhead : ∀ (l : List α) (a : α), (a :: l).IsChain R →
      ∀ b ∈ (l.filter fun a => decide (B a)).head?, R a b := by
    intro l
    induction l with
    | nil => intro a _ b hb; simp at hb
    | cons c l ih =>
      intro a h b hb
      obtain ⟨hac, hcl⟩ := List.isChain_cons_cons.mp h
      by_cases hc : B c
      · have hc' : decide (B c) = true := by simpa using hc
        rw [List.filter_cons_of_pos (p := fun a => decide (B a)) (a := c) hc'] at hb
        obtain rfl : b = c := by simpa using hb
        exact hac
      · have hc' : ¬ decide (B c) = true := by simpa using hc
        rw [List.filter_cons_of_neg (p := fun a => decide (B a)) (a := c) hc'] at hb
        refine ih a ?_ b hb
        cases l with
        | nil => exact List.isChain_singleton a
        | cons d l =>
          obtain ⟨hcd, hdl⟩ := List.isChain_cons_cons.mp hcl
          exact List.isChain_cons_cons.mpr ⟨hskip a c d hac hc hcd, hdl⟩
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    have hl : l.IsChain R := by
      cases l with
      | nil => simp
      | cons c l => exact (List.isChain_cons_cons.mp h).2
    by_cases ha : B a
    · have ha' : decide (B a) = true := by simpa using ha
      rw [List.filter_cons_of_pos (p := fun a => decide (B a)) (a := a) ha']
      have hih := ih hl
      cases hfl : l.filter (fun a => decide (B a)) with
      | nil => exact List.isChain_singleton a
      | cons b m =>
        have hb : b ∈ (l.filter fun a => decide (B a)).head? := by rw [hfl]; simp
        rw [hfl] at hih
        exact List.isChain_cons_cons.mpr ⟨hhead l a h b hb, hih⟩
    · have ha' : ¬ decide (B a) = true := by simpa using ha
      rw [List.filter_cons_of_neg (p := fun a => decide (B a)) (a := a) ha']
      exact ih hl

variable {M : CombMap.{u}}

/-- A boundary walk of a subset of `U` is a boundary walk of `U`. -/
theorem boundaryWalk_mono {R U : Finset M.Face} (hRU : R ⊆ U) {a b : M.Dart}
    (h : BoundaryWalk M R a b) : BoundaryWalk M U a b := by
  refine Relation.ReflTransGen.mono ?_ h
  rintro x y ⟨⟨h1, h2⟩, hs⟩
  exact ⟨⟨hRU h1, hRU h2⟩, hs⟩

/-- A face step is a boundary walk. -/
theorem boundaryWalk_of_facePerm {U : Finset M.Face} {a b : M.Dart} (h : M.facePerm a = b) :
    BoundaryWalk M U a b := by
  subst h
  exact Relation.ReflTransGen.refl

/-- **A boundary walk through an internal dart.**  A boundary walk onto an internal dart `b` of
`U`, then a boundary walk from `alpha b`, is one boundary walk: rotating past `b` is the face step
from `alpha b`. -/
theorem boundaryWalk_trans_internal {U : Finset M.Face} {a b e : M.Dart}
    (h₁ : BoundaryWalk M U a b) (hb : InternalDart M U b) (h₂ : BoundaryWalk M U (M.alpha b) e) :
    BoundaryWalk M U a e := by
  refine Relation.ReflTransGen.trans h₁ (Relation.ReflTransGen.head ⟨hb, ?_⟩ h₂)
  show M.sigma b = M.sigma (M.alpha (M.alpha b))
  rw [M.alpha_involutive b]

/-- **One step of the tour.**  Either a boundary walk of `U` onto a kept dart, or a boundary walk
onto an internal dart `b` of `U` followed by the jump to `alpha b`, which is not kept. -/
def Hop (U : Finset M.Face) (B : M.Dart → Prop) (p q : M.Dart) : Prop :=
  (BoundaryWalk M U p q ∧ B q) ∨
    ∃ b, BoundaryWalk M U p b ∧ InternalDart M U b ∧ M.alpha b = q ∧ ¬ B q

/-- **Two hops through a dart that is not kept make one hop.** -/
theorem hop_skip {U : Finset M.Face} {B : M.Dart → Prop} {p q r : M.Dart} (h₁ : Hop U B p q)
    (hq : ¬ B q) (h₂ : Hop U B q r) : Hop U B p r := by
  rcases h₁ with ⟨-, hBq⟩ | ⟨b, hpb, hb, rfl, -⟩
  · exact absurd hBq hq
  · rcases h₂ with ⟨hqr, hBr⟩ | ⟨b', hqb', hb', hr, hBr⟩
    · exact Or.inl ⟨boundaryWalk_trans_internal hpb hb hqr, hBr⟩
    · exact Or.inr ⟨b', boundaryWalk_trans_internal hpb hb hqb', hb', hr, hBr⟩

/-- **The kept darts of a tour are a chain of boundary walks of `U`.** -/
theorem isChain_filter_hop {U : Finset M.Face} (B : M.Dart → Prop) [DecidablePred B]
    {l : List M.Dart} (hl : l.IsChain (Hop U B)) :
    (l.filter fun a => decide (B a)).IsChain (BoundaryWalk M U) := by
  refine (isChain_filter_of_skip B (fun _ _ _ h₁ hq h₂ => hop_skip h₁ hq h₂) l hl).imp_of_mem_imp
    fun a b _ hb h => ?_
  have hBb : B b := by simpa using (List.mem_filter.mp hb).2
  rcases h with ⟨h, -⟩ | ⟨-, -, -, -, hnb⟩
  · exact h
  · exact absurd hBb hnb

/-- **One stretch of the tour.**  A chain of boundary walks `a, I, b` with every dart of `I` kept
and `b` internal to `U` gives a chain of hops `a, I, alpha b`, when `alpha b` is not kept. -/
theorem isChain_hop_of_stretch {U : Finset M.Face} {B : M.Dart → Prop} {b a' : M.Dart}
    (hb : InternalDart M U b) (hba : M.alpha b = a') (hna : ¬ B a') :
    ∀ {a : M.Dart} {I : List M.Dart}, (a :: I ++ [b]).IsChain (BoundaryWalk M U) →
      (∀ d ∈ I, B d) → (a :: I ++ [a']).IsChain (Hop U B) := by
  intro a I
  induction I generalizing a with
  | nil =>
    intro h _
    have hab : BoundaryWalk M U a b := (List.isChain_cons_cons.mp h).1
    exact List.isChain_cons_cons.mpr ⟨Or.inr ⟨b, hab, hb, hba, hna⟩, List.isChain_singleton a'⟩
  | cons c I ih =>
    intro h hB
    obtain ⟨hac, hc⟩ := List.isChain_cons_cons.mp h
    exact List.isChain_cons_cons.mpr ⟨Or.inl ⟨hac, hB c List.mem_cons_self⟩,
      ih hc fun d hd => hB d (List.mem_cons_of_mem c hd)⟩

/-- **Gluing two chains at a shared element.** -/
theorem isChain_append_overlap {α : Type*} {R : α → α → Prop} {l l' : List α} {m : α}
    (h₁ : (l ++ [m]).IsChain R) (h₂ : (m :: l').IsChain R) : (l ++ m :: l').IsChain R := by
  obtain ⟨hl, -, hlm⟩ := List.isChain_append.mp h₁
  refine List.isChain_append.mpr ⟨hl, h₂, fun x hx y hy => ?_⟩
  obtain rfl : y = m := by simpa using hy
  exact hlm x hx m (by simp)

/-- **A closed tour gives a closed chain of first turns** on its kept darts.  If the tour `P` is a
chain of hops and hops from its last element to its first, and kept darts are boundary darts of
`U`, then the kept darts `c` are a chain of first turns along `c`, closed from last to first. -/
theorem firstTurn_chain_of_tour {U : Finset M.Face} (B : M.Dart → Prop) [DecidablePred B]
    {P c : List M.Dart} (hc : c = P.filter fun a => decide (B a)) (hP : P.IsChain (Hop U B))
    (hclose : ∀ p ∈ P.getLast?, ∀ q ∈ P.head?, Hop U B p q)
    (hbd : ∀ d, B d → IsBoundaryDart M U d) :
    c.IsChain (FirstTurn M c) ∧ ∀ p ∈ c.getLast?, ∀ q ∈ c.head?, FirstTurn M c p q := by
  have hPP : (P ++ P).IsChain (Hop U B) := List.isChain_append.mpr ⟨hP, hP, hclose⟩
  have hcc := isChain_filter_hop B hPP
  rw [List.filter_append, ← hc] at hcc
  obtain ⟨hchain, -, hjoin⟩ := List.isChain_append.mp hcc
  have hcbd : ∀ d ∈ c, IsBoundaryDart M U d := fun d hd => by
    rw [hc] at hd
    exact hbd d (by simpa using (List.mem_filter.mp hd).2)
  exact ⟨hchain.imp fun _ _ h => FirstTurn.of_boundaryWalk hcbd h,
    fun p hp q hq => FirstTurn.of_boundaryWalk hcbd (hjoin p hp q hq)⟩

end ExclusiveTour

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTour.isChain_filter_of_skip
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTour.boundaryWalk_mono
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTour.boundaryWalk_trans_internal
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTour.hop_skip
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTour.isChain_filter_hop
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTour.isChain_hop_of_stretch
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTour.isChain_append_overlap
#audit_axioms GroupApproximation.GGT.VanKampen.ExclusiveTour.firstTurn_chain_of_tour
