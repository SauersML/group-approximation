import GroupApproximation.BooneHigmanLinear.CharZero.BTri.Develop
import Mathlib.Data.List.Chain
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Path lifting and the colimit theorem (Z1-base, piece Z.5, part 3)

The projection of the development (`BTri/Develop.lean`) lifts edge paths uniquely
(`liftStep`, `liftAll`). The endpoint of a lift is invariant under backtracks and triangle
moves (`liftAll_eqvGen`). Hence:

* `amEval_injective`: if the graph is simply connected at `s 0`, evaluation from the amalgam of
  the vertex stabilizers is injective;
* `amEval_surjective`: if the graph is connected, it is surjective;
* `exists_extension`: **the colimit theorem** (Soulé; K. S. Brown). Compatible homomorphisms on
  the three vertex stabilizers extend to a homomorphism on `G`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri

section Lifting

variable {G : Type*} [Group G] {V : Type*} [MulAction G V] {Γ : SimpleGraph V}
  {s : Fin 3 → V} {τ : V → Fin 3}

theorem hatLift_unique' (hA : TriangleAction G Γ s τ) {v w₁ w₂ : Hat G s}
    (h₁ : HatAdj G s v w₁) (h₂ : HatAdj G s v w₂) (hp : hatProj G s w₁ = hatProj G s w₂) :
    w₁ = w₂ := by
  obtain ⟨i, q⟩ := v
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact hatLift_unique hA h₁ h₂ hp

#audit_axioms hatLift_unique'

theorem hatLift_tri' (hA : TriangleAction G Γ s τ) {v w₁ w₂ : Hat G s}
    (h₁ : HatAdj G s v w₁) (h₂ : HatAdj G s v w₂)
    (h : Γ.Adj (hatProj G s w₁) (hatProj G s w₂)) : HatAdj G s w₁ w₂ := by
  obtain ⟨i, q⟩ := v
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact hatLift_tri hA h₁ h₂ h

#audit_axioms hatLift_tri'

open Classical in
/-- One lifting step: the neighbour of `v` over `y`, when there is one. -/
noncomputable def liftStep (v : Hat G s) (y : V) : Hat G s :=
  if h : ∃ w, HatAdj G s v w ∧ hatProj G s w = y then h.choose else v

theorem liftStep_spec (hA : TriangleAction G Γ s τ) (v : Hat G s) {y : V}
    (hy : Γ.Adj (hatProj G s v) y) :
    HatAdj G s v (liftStep v y) ∧ hatProj G s (liftStep v y) = y := by
  have hex := hatLift_exists hA v hy
  rw [liftStep, dif_pos hex]
  exact hex.choose_spec

#audit_axioms liftStep_spec

theorem liftStep_eq (hA : TriangleAction G Γ s τ) {v w : Hat G s} (hvw : HatAdj G s v w) :
    liftStep v (hatProj G s w) = w :=
  hatLift_unique' hA (liftStep_spec hA v (hatProj_adj hA hvw)).1 hvw
    (liftStep_spec hA v (hatProj_adj hA hvw)).2

#audit_axioms liftStep_eq

/-- Lifting a list of successive vertices. -/
noncomputable def liftAll : Hat G s → List V → Hat G s
  | v, [] => v
  | v, y :: l => liftAll (liftStep v y) l

@[simp] theorem liftAll_nil (v : Hat G s) : liftAll v [] = v :=
  rfl

@[simp] theorem liftAll_cons (v : Hat G s) (y : V) (l : List V) :
    liftAll v (y :: l) = liftAll (liftStep v y) l :=
  rfl

theorem liftAll_append (l m : List V) :
    ∀ v : Hat G s, liftAll v (l ++ m) = liftAll (liftAll v l) m := by
  induction l with
  | nil => intro v; rfl
  | cons y l ih => intro v; exact ih (liftStep v y)

#audit_axioms liftAll_append

/-- The lift of a path from `hatProj v` ends over the last vertex. -/
theorem proj_liftAll (hA : TriangleAction G Γ s τ) :
    ∀ (l : List V) (v : Hat G s), List.IsChain Γ.Adj (hatProj G s v :: l) →
      (hatProj G s v :: l).getLast? = some (hatProj G s (liftAll v l)) := by
  intro l
  induction l with
  | nil => intro v _; rfl
  | cons y l ih =>
      intro v hc
      rw [List.isChain_cons_cons] at hc
      have hs := liftStep_spec hA v hc.1
      rw [liftAll_cons, ← ih (liftStep v y) (by rw [hs.2]; exact hc.2), hs.2]
      simp

#audit_axioms proj_liftAll

theorem tail_append_cons (l₁ : List V) (u : V) (m : List V) :
    (l₁ ++ u :: m).tail = (l₁ ++ [u]).tail ++ m := by
  cases l₁ <;> simp

#audit_axioms tail_append_cons

theorem head?_append_cons (l₁ : List V) (u : V) (m : List V) :
    (l₁ ++ u :: m).head? = (l₁ ++ [u]).head? := by
  cases l₁ <;> simp

#audit_axioms head?_append_cons

/-- The lift of a path at an intermediate vertex `u` projects to `u`. -/
theorem proj_liftAll_prefix (hA : TriangleAction G Γ s τ) (b : Hat G s) (l₁ : List V) (u : V)
    (m : List V) (hc : List.IsChain Γ.Adj (l₁ ++ u :: m))
    (hb : (l₁ ++ u :: m).head? = some (hatProj G s b)) :
    hatProj G s (liftAll b (l₁ ++ [u]).tail) = u := by
  have hc' : List.IsChain Γ.Adj (l₁ ++ [u]) := (List.isChain_split.mp hc).1
  have hb' : (l₁ ++ [u]).head? = some (hatProj G s b) := by rw [← head?_append_cons l₁ u m, hb]
  obtain ⟨t, ht⟩ : ∃ t, l₁ ++ [u] = hatProj G s b :: t := by
    cases h : l₁ ++ [u] with
    | nil => simp at h
    | cons x t =>
        rw [h] at hb'
        simp only [List.head?_cons, Option.some.injEq] at hb'
        exact ⟨t, by rw [hb']⟩
  have h := proj_liftAll hA t b (by rw [← ht]; exact hc')
  rw [← ht, List.getLast?_concat, Option.some.injEq] at h
  rw [ht]
  exact h.symm

#audit_axioms proj_liftAll_prefix

/-- Moves preserve being a path. -/
theorem triStep_isChain_iff {L L' : List V} (h : TriStep Γ L L') :
    List.IsChain Γ.Adj L ↔ List.IsChain Γ.Adj L' := by
  cases h with
  | backtrack l₁ l₂ u v huv =>
      rw [List.isChain_split (c := u) (l₁ := l₁) (l₂ := v :: u :: l₂),
        List.isChain_split (c := u) (l₁ := l₁) (l₂ := l₂), List.isChain_cons_cons,
        List.isChain_cons_cons]
      exact ⟨fun ⟨h1, _, _, h4⟩ => ⟨h1, h4⟩, fun ⟨h1, h4⟩ => ⟨h1, huv, huv.symm, h4⟩⟩
  | triangle l₁ l₂ u v w huv hvw huw =>
      rw [List.isChain_split (c := u) (l₁ := l₁) (l₂ := v :: w :: l₂),
        List.isChain_split (c := u) (l₁ := l₁) (l₂ := w :: l₂), List.isChain_cons_cons,
        List.isChain_cons_cons, List.isChain_cons_cons]
      exact ⟨fun ⟨h1, _, _, h4⟩ => ⟨h1, huw, h4⟩, fun ⟨h1, _, h4⟩ => ⟨h1, huv, hvw, h4⟩⟩

#audit_axioms triStep_isChain_iff

/-- Moves preserve the first vertex. -/
theorem triStep_head {L L' : List V} (h : TriStep Γ L L') : L.head? = L'.head? := by
  cases h with
  | backtrack l₁ l₂ u v _ => cases l₁ <;> rfl
  | triangle l₁ l₂ u v w _ _ _ => cases l₁ <;> rfl

#audit_axioms triStep_head

/-- **One move does not change the endpoint of the lift.** -/
theorem liftAll_triStep (hA : TriangleAction G Γ s τ) (b : Hat G s) {L L' : List V}
    (h : TriStep Γ L L') (hL : List.IsChain Γ.Adj L) (hb : L.head? = some (hatProj G s b)) :
    liftAll b L.tail = liftAll b L'.tail := by
  cases h with
  | backtrack l₁ l₂ u v huv =>
      have hc := proj_liftAll_prefix hA b l₁ u _ hL hb
      rw [tail_append_cons l₁ u (v :: u :: l₂), tail_append_cons l₁ u l₂, liftAll_append,
        liftAll_append]
      set c := liftAll b (l₁ ++ [u]).tail
      have hcv := liftStep_spec hA c (by rw [hc]; exact huv)
      rw [liftAll_cons, liftAll_cons]
      congr 1
      calc liftStep (liftStep c v) u = liftStep (liftStep c v) (hatProj G s c) := by rw [hc]
        _ = c := liftStep_eq hA (hatAdj_symm hcv.1)
  | triangle l₁ l₂ u v w huv hvw huw =>
      have hc := proj_liftAll_prefix hA b l₁ u _ hL hb
      rw [tail_append_cons l₁ u (v :: w :: l₂), tail_append_cons l₁ u (w :: l₂), liftAll_append,
        liftAll_append]
      set c := liftAll b (l₁ ++ [u]).tail
      have hcv := liftStep_spec hA c (by rw [hc]; exact huv)
      have hcw := liftStep_spec hA c (by rw [hc]; exact huw)
      have hvw' : HatAdj G s (liftStep c v) (liftStep c w) :=
        hatLift_tri' hA hcv.1 hcw.1 (by rw [hcv.2, hcw.2]; exact hvw)
      rw [liftAll_cons, liftAll_cons, liftAll_cons]
      congr 1
      calc liftStep (liftStep c v) w = liftStep (liftStep c v) (hatProj G s (liftStep c w)) := by
            rw [hcw.2]
        _ = liftStep c w := liftStep_eq hA hvw'

#audit_axioms liftAll_triStep

/-- **The endpoint of the lift is a homotopy invariant.** -/
theorem liftAll_eqvGen (hA : TriangleAction G Γ s τ) (b : Hat G s) {L L' : List V}
    (h : Relation.EqvGen (TriStep Γ) L L') :
    (List.IsChain Γ.Adj L ↔ List.IsChain Γ.Adj L') ∧ L.head? = L'.head? ∧
      (List.IsChain Γ.Adj L → L.head? = some (hatProj G s b) →
        liftAll b L.tail = liftAll b L'.tail) := by
  induction h with
  | rel L L' h =>
      exact ⟨triStep_isChain_iff h, triStep_head h, liftAll_triStep hA b h⟩
  | refl L => exact ⟨Iff.rfl, rfl, fun _ _ => rfl⟩
  | symm L L' _ ih =>
      refine ⟨ih.1.symm, ih.2.1.symm, fun hc hb => ?_⟩
      exact (ih.2.2 (ih.1.mpr hc) (ih.2.1.trans hb)).symm
  | trans L M L' _ _ ih₁ ih₂ =>
      refine ⟨ih₁.1.trans ih₂.1, ih₁.2.1.trans ih₂.2.1, fun hc hb => ?_⟩
      exact (ih₁.2.2 hc hb).trans (ih₂.2.2 (ih₁.1.mp hc) (ih₁.2.1.symm.trans hb))

#audit_axioms liftAll_eqvGen

/-- The base vertex of the development, `(0, 1)`. -/
theorem hatProj_base : hatProj G s (mkHat 0 (1 : Am (stabs G s))) = s 0 := by
  rw [hatProj_mk, map_one, one_smul]

#audit_axioms hatProj_base

/-- Every `ĝ ∈ Am P` is reached by lifting a path from `s 0` to `amEval ĝ • s 0`. -/
theorem exists_path_lift (hA : TriangleAction G Γ s τ) (g : Am (stabs G s)) :
    ∃ L : List V, L.head? = some (s 0) ∧ List.IsChain Γ.Adj L ∧
      L.getLast? = some (amEval (stabs G s) g • s 0) ∧
      liftAll (mkHat 0 (1 : Am (stabs G s))) L.tail = mkHat 0 g := by
  induction g using am_induction with
  | h1 => exact ⟨[s 0], rfl, List.isChain_singleton _, by simp, rfl⟩
  | hmul g i a ih =>
      obtain ⟨L, hh, hc, hl, hlift⟩ := ih
      have hfix : amEval (stabs G s) (g * amOf (stabs G s) i a) • s i =
          amEval (stabs G s) g • s i := by
        rw [map_mul, amEval_amOf, mul_smul, MulAction.mem_stabilizer_iff.mp a.2]
      by_cases hi : i = 0
      · subst hi
        refine ⟨L, hh, hc, by rw [hl, hfix], by rw [hlift, mkHat_mul_amOf]⟩
      · have hne : L ≠ [] := by rintro rfl; simp at hh
        have h1 : Γ.Adj (amEval (stabs G s) g • s 0) (amEval (stabs G s) g • s i) :=
          (hA.adj_smul _ _ _).mpr (hA.std_adj 0 i (Ne.symm hi))
        have h2 : Γ.Adj (amEval (stabs G s) g • s i)
            (amEval (stabs G s) (g * amOf (stabs G s) i a) • s 0) := by
          rw [← hfix]
          exact (hA.adj_smul _ _ _).mpr (hA.std_adj i 0 hi)
        refine ⟨L ++ [amEval (stabs G s) g • s i,
          amEval (stabs G s) (g * amOf (stabs G s) i a) • s 0], ?_, ?_, ?_, ?_⟩
        · simp [List.head?_append, hh]
        · rw [List.isChain_append]
          refine ⟨hc, List.isChain_cons_cons.mpr ⟨h2, List.isChain_singleton _⟩, ?_⟩
          intro x hx y hy
          rw [hl, Option.mem_some_iff] at hx
          simp only [List.head?_cons, Option.mem_some_iff] at hy
          rw [← hx, ← hy]
          exact h1
        · simp
        · rw [List.tail_append_of_ne_nil hne, liftAll_append, hlift, liftAll_cons, liftAll_cons,
            liftAll_nil]
          have e1 : liftStep (mkHat 0 g) (amEval (stabs G s) g • s i) = mkHat i g := by
            have := liftStep_eq hA (hatAdj_mk (s := s) g (Ne.symm hi))
            rwa [hatProj_mk] at this
          have hadj : HatAdj G s (mkHat i g) (mkHat 0 (g * amOf (stabs G s) i a)) :=
            ⟨hi, g * amOf (stabs G s) i a, mkHat_mul_amOf i g a, rfl⟩
          have e2 := liftStep_eq hA hadj
          rw [hatProj_mk] at e2
          rw [e1, e2]

#audit_axioms exists_path_lift

/-- **Evaluation from the amalgam is injective** when the graph is simply connected at `s 0`. -/
theorem amEval_injective (hA : TriangleAction G Γ s τ) (hsc : TriSimplyConnected Γ (s 0)) :
    Function.Injective (amEval (stabs G s)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨L, hh, hc, hl, hlift⟩ := exists_path_lift hA g
  obtain ⟨l, rfl⟩ : ∃ l, L = s 0 :: l := by
    cases L with
    | nil => simp at hh
    | cons x l =>
        simp only [List.head?_cons, Option.some.injEq] at hh
        exact ⟨l, by rw [hh]⟩
  rw [hg, one_smul] at hl
  have hclosed : (s 0 :: l).getLast (List.cons_ne_nil _ _) = s 0 := by
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), Option.some.injEq] at hl
    exact hl
  have hE := (liftAll_eqvGen hA (mkHat 0 (1 : Am (stabs G s))) (hsc l hc hclosed)).2.2 hc
    (by simp)
  rw [hlift] at hE
  have hE' : mkHat 0 g = mkHat 0 (1 : Am (stabs G s)) := hE
  obtain ⟨c, hcg⟩ := mkHat_eq_iff.mp hE'
  rw [mul_one] at hcg
  have hc1 : (c : G) = 1 := by
    have := congrArg (amEval (stabs G s)) hcg
    rwa [amEval_amOf, map_inv, hg, inv_one] at this
  have hc' : c = 1 := Subtype.ext hc1
  rw [hc', map_one] at hcg
  exact inv_eq_one.mp hcg.symm

#audit_axioms amEval_injective

/-- **Evaluation from the amalgam is surjective** when the graph is connected. -/
theorem amEval_surjective (hA : TriangleAction G Γ s τ) (hconn : Γ.Connected) :
    Function.Surjective (amEval (stabs G s)) := by
  intro g
  obtain ⟨p⟩ := hconn.preconnected (s 0) (g • s 0)
  have hc : List.IsChain Γ.Adj (hatProj G s (mkHat 0 (1 : Am (stabs G s))) :: p.support.tail) := by
    rw [hatProj_base, SimpleGraph.Walk.cons_tail_support]
    exact p.isChain_adj_support
  have hl := proj_liftAll hA p.support.tail (mkHat 0 (1 : Am (stabs G s))) hc
  rw [hatProj_base, SimpleGraph.Walk.cons_tail_support,
    List.getLast?_eq_some_getLast p.support_ne_nil, SimpleGraph.Walk.getLast_support,
    Option.some.injEq] at hl
  set E := liftAll (mkHat 0 (1 : Am (stabs G s))) p.support.tail
  obtain ⟨h, hE⟩ := hat_exists_mk E
  have htype : E.1 = 0 := by
    rw [← hatProj_type hA E, ← hl, hA.type_smul, hA.type_std]
  rw [hE, hatProj_mk, htype] at hl
  have hstab : (amEval (stabs G s) h)⁻¹ * g ∈ stabs G s 0 := by
    show (amEval (stabs G s) h)⁻¹ * g ∈ MulAction.stabilizer G (s 0)
    rw [MulAction.mem_stabilizer_iff, mul_smul, hl, inv_smul_smul]
  refine ⟨h * amOf (stabs G s) 0 ⟨_, hstab⟩, ?_⟩
  rw [map_mul, amEval_amOf]
  exact mul_inv_cancel_left _ _

#audit_axioms amEval_surjective

/-- **The colimit theorem.** For a connected, simply connected triangle action, compatible
homomorphisms on the three vertex stabilizers extend to a homomorphism on `G`. -/
theorem exists_extension (hA : TriangleAction G Γ s τ) (hconn : Γ.Connected)
    (hsc : TriSimplyConnected Γ (s 0)) {H : Type*} [Group H] (φ : ∀ i, stabs G s i →* H)
    (hφ : ∀ (i j : Fin 3) (a : stabs G s i) (b : stabs G s j), (a : G) = b → φ i a = φ j b) :
    ∃ ψ : G →* H, ∀ (i : Fin 3) (a : stabs G s i), ψ a = φ i a := by
  let e := MulEquiv.ofBijective (amEval (stabs G s))
    ⟨amEval_injective hA hsc, amEval_surjective hA hconn⟩
  refine ⟨(amLift φ hφ).comp e.symm.toMonoidHom, fun i a => ?_⟩
  have he : e.symm (a : G) = amOf (stabs G s) i a :=
    e.symm_apply_eq.mpr (amEval_amOf (stabs G s) i a).symm
  change amLift φ hφ (e.symm (a : G)) = φ i a
  rw [he, amLift_amOf]

#audit_axioms exists_extension

end Lifting

end BTri
end BooneHigmanLinear
end GroupApproximation
