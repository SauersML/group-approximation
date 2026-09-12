import GroupApproximation.Kazhdan.CCKWTitsMoves
import GroupApproximation.Meta.AxiomGuard

/-!
# Typed words and closed paths in the coset complex

A *typed letter* `⟨i, p⟩` is an element `p ∈ Hᵢ` together with its type.  A typed word `L`
traces a vertex path from a representative `g` (`D g L`): the letter `⟨i, p⟩` visits the coset
of type `i` of the current representative and multiplies it by `p`.

*Typed moves* merge two letters of the same type, drop a letter `⟨i, 1⟩`, or retype a letter
whose element lies in two vertex groups (`BaseMove`, `TypedMove`).  Each typed move becomes
one or two relaxed moves of the traced path (`transfer`), and every closed edge path is the
trace of a typed word whose value is `1` up to relaxed moves (`encode`, `loop_moves`).  So if
every typed word with value `1` reduces to the empty word, the coset complex is simply
connected (`simplyConnected_of_typedWordProblem`).  If every group element is the value of a
typed word, the coset complex is connected (`connected_of_generated`).
-/

namespace GroupApproximation.CCKWTits

open Systolic

universe u

variable {G : Type u} [Group G] {H : Fin 3 → Subgroup G}

/-- A typed letter: an element of one of the vertex groups, with its type. -/
abbrev Letter (H : Fin 3 → Subgroup G) : Type u := Σ i : Fin 3, H i

/-- The value of a typed word. -/
def val : List (Letter H) → G
  | [] => 1
  | a :: L => (a.2 : G) * val L

/-- The vertex path traced by a typed word from the representative `g`. -/
def D (g : G) : List (Letter H) → List (Σ i : Fin 3, G ⧸ H i)
  | [] => []
  | a :: L => vtx H a.1 (g * a.2) :: D (g * a.2) L

theorem val_append (L M : List (Letter H)) : val (L ++ M) = val L * val M := by
  induction L with
  | nil => rw [List.nil_append, val, one_mul]
  | cons a L ih => rw [List.cons_append, val, val, ih, mul_assoc]

theorem D_append (g : G) (L M : List (Letter H)) : D g (L ++ M) = D g L ++ D (g * val L) M := by
  induction L generalizing g with
  | nil => rw [List.nil_append, D, val, mul_one, List.nil_append]
  | cons a L ih => rw [List.cons_append, D, D, ih, val, mul_assoc, List.cons_append]

theorem rep_vtx_mul (i : Fin 3) (h : G) (p : H i) : Rep H (vtx H i (h * p)) h := by
  show (QuotientGroup.mk (h * p) : G ⧸ H i) = QuotientGroup.mk h
  exact QuotientGroup.eq.mpr (by rw [mul_inv_rev, inv_mul_cancel_right]; exact inv_mem p.2)

/-! ### Typed moves -/

/-- The three local typed moves. -/
inductive BaseMove : List (Letter H) → List (Letter H) → Prop
  | merge (i : Fin 3) (p q : H i) : BaseMove [⟨i, p⟩, ⟨i, q⟩] [⟨i, p * q⟩]
  | drop (i : Fin 3) : BaseMove [⟨i, 1⟩] []
  | retype (i j : Fin 3) (p : H i) (hp : (p : G) ∈ H j) : BaseMove [⟨i, p⟩] [⟨j, ⟨p, hp⟩⟩]

/-- A typed move applies a local move inside a word. -/
def TypedMove (L L' : List (Letter H)) : Prop :=
  ∃ pre mid mid' post, BaseMove mid mid' ∧ L = pre ++ (mid ++ post) ∧ L' = pre ++ (mid' ++ post)

theorem val_base {mid mid' : List (Letter H)} (hb : BaseMove mid mid') : val mid = val mid' := by
  cases hb with
  | merge i p q => simp only [val, Subgroup.coe_mul, mul_one, mul_assoc]
  | drop i => simp only [val, Subgroup.coe_one, mul_one]
  | retype i j p hp => rfl

theorem val_typedMove {L L' : List (Letter H)} (hm : TypedMove L L') : val L = val L' := by
  obtain ⟨pre, mid, mid', post, hb, rfl, rfl⟩ := hm
  rw [val_append, val_append, val_append, val_append, val_base hb]

/-! ### Transfer of typed moves to relaxed moves -/

theorem path_split (v : Σ i : Fin 3, G ⧸ H i) (g : G) (j : Fin 3) (pre mid post : List (Letter H)) :
    v :: D g (pre ++ (mid ++ post)) ++ [vtx H j (g * val (pre ++ (mid ++ post)))] =
      (v :: D g pre) ++ D (g * val pre) mid ++
        (D (g * val pre * val mid) post ++ [vtx H j (g * val pre * val mid * val post)]) := by
  simp only [D_append, val_append, List.cons_append, List.append_assoc, mul_assoc]

theorem exists_last_rep (v : Σ i : Fin 3, G ⧸ H i) (g : G) (pre : List (Letter H))
    (hv : Rep H v g) :
    ∃ (P : List (Σ i : Fin 3, G ⧸ H i)) (w : Σ i : Fin 3, G ⧸ H i),
      v :: D g pre = P ++ [w] ∧ Rep H w (g * val pre) := by
  induction pre generalizing v g with
  | nil => exact ⟨[], v, rfl, by rwa [val, mul_one]⟩
  | cons a pre ih =>
      obtain ⟨P, w, hP, hw⟩ := ih (vtx H a.1 (g * a.2)) (g * a.2) (rep_vtx _ _)
      refine ⟨v :: P, w, ?_, ?_⟩
      · rw [D, hP, List.cons_append]
      · rwa [val, ← mul_assoc]

theorem exists_head_rep (h : G) (post : List (Letter H)) (j : Fin 3) :
    ∃ (w : Σ i : Fin 3, G ⧸ H i) (rest : List (Σ i : Fin 3, G ⧸ H i)),
      D h post ++ [vtx H j (h * val post)] = w :: rest ∧ Rep H w h := by
  cases post with
  | nil =>
      refine ⟨vtx H j (h * val []), [], rfl, ?_⟩
      show (QuotientGroup.mk (h * 1) : G ⧸ H j) = QuotientGroup.mk h
      rw [mul_one]
  | cons a post => exact ⟨_, _, rfl, rep_vtx_mul a.1 h a.2⟩

theorem mid_moves {mid mid' : List (Letter H)} (hb : BaseMove mid mid')
    (P rest : List (Σ i : Fin 3, G ⧸ H i)) (w w' : Σ i : Fin 3, G ⧸ H i) (h : G)
    (hw : Rep H w h) (hw' : Rep H w' (h * val mid)) :
    Relation.EqvGen (Moves H) (P ++ [w] ++ D h mid ++ w' :: rest)
      (P ++ [w] ++ D h mid' ++ w' :: rest) := by
  cases hb with
  | merge i p q =>
      have e : vtx H i (h * ↑p) = vtx H i (h * ↑p * ↑q) :=
        vtx_eq_of_rep (rep_vtx_mul i (h * ↑p) q)
      show Relation.EqvGen (Moves H) (P ++ [w] ++ [vtx H i (h * ↑p), vtx H i (h * ↑p * ↑q)] ++ w' :: rest)
        (P ++ [w] ++ [vtx H i (h * ↑(p * q))] ++ w' :: rest)
      rw [e, Subgroup.coe_mul, ← mul_assoc]
      exact Relation.EqvGen.rel _ _ (by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          Moves.stutter (H := H) (P ++ [w]) (w' :: rest) (vtx H i (h * ↑p * ↑q)))
  | drop i =>
      have hw'' : Rep H w' h := by
        have e : h * val [(⟨i, 1⟩ : Letter H)] = h := by
          simp only [val, Subgroup.coe_one, mul_one]
        rwa [e] at hw'
      show Relation.EqvGen (Moves H) (P ++ [w] ++ [vtx H i (h * ↑(1 : H i))] ++ w' :: rest)
        (P ++ [w] ++ [] ++ w' :: rest)
      exact Relation.EqvGen.rel _ _ (by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          Moves.cp (H := H) P rest w (vtx H i (h * ↑(1 : H i))) w' h hw (rep_vtx_mul i h 1) hw'')
  | retype i j p hp =>
      have hw'' : Rep H w' (h * ↑p) := by
        have e : h * val [(⟨i, p⟩ : Letter H)] = h * ↑p := by simp only [val, mul_one]
        rwa [e] at hw'
      show Relation.EqvGen (Moves H) (P ++ [w] ++ [vtx H i (h * ↑p)] ++ w' :: rest)
        (P ++ [w] ++ [vtx H j (h * ↑p)] ++ w' :: rest)
      have m1 : Moves H (P ++ [w] ++ [vtx H i (h * ↑p), vtx H j (h * ↑p)] ++ w' :: rest)
          (P ++ [w] ++ [vtx H i (h * ↑p)] ++ w' :: rest) := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          Moves.cp (H := H) (P ++ [w]) rest (vtx H i (h * ↑p)) (vtx H j (h * ↑p)) w' (h * ↑p)
            (rep_vtx i (h * ↑p)) (rep_vtx j (h * ↑p)) hw''
      have m2 : Moves H (P ++ [w] ++ [vtx H i (h * ↑p), vtx H j (h * ↑p)] ++ w' :: rest)
          (P ++ [w] ++ [vtx H j (h * ↑p)] ++ w' :: rest) := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          Moves.cp (H := H) P (w' :: rest) w (vtx H i (h * ↑p)) (vtx H j (h * ↑p)) h
            hw (rep_vtx_mul i h p) (rep_vtx_mul j h ⟨p, hp⟩)
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ m1))
        (Relation.EqvGen.rel _ _ m2)

/-- **Typed moves become relaxed moves of the traced path.** -/
theorem transfer {L L' : List (Letter H)} (hm : TypedMove L L') (v : Σ i : Fin 3, G ⧸ H i)
    (g : G) (j : Fin 3) (hv : Rep H v g) :
    Relation.EqvGen (Moves H) (v :: D g L ++ [vtx H j (g * val L)])
      (v :: D g L' ++ [vtx H j (g * val L')]) := by
  obtain ⟨pre, mid, mid', post, hb, rfl, rfl⟩ := hm
  rw [path_split, path_split, ← val_base hb]
  obtain ⟨P, w, hPw, hw⟩ := exists_last_rep v g pre hv
  obtain ⟨w', rest, hwr, hw'⟩ := exists_head_rep (g * val pre * val mid) post j
  rw [hPw, hwr]
  exact mid_moves hb P rest w w' (g * val pre) hw hw'

theorem eqvGen_transfer {L L' : List (Letter H)} (hm : Relation.EqvGen TypedMove L L')
    (v : Σ i : Fin 3, G ⧸ H i) (g : G) (j : Fin 3) (hv : Rep H v g) :
    Relation.EqvGen (Moves H) (v :: D g L ++ [vtx H j (g * val L)])
      (v :: D g L' ++ [vtx H j (g * val L')]) :=
  eqvGen_map (fun L ↦ v :: D g L ++ [vtx H j (g * val L)])
    (fun _ _ hab ↦ transfer hab v g j hv) hm

/-! ### Encoding closed paths -/

theorem encode (v : Σ i : Fin 3, G ⧸ H i) (l : List (Σ i : Fin 3, G ⧸ H i)) (g : G)
    (hv : Rep H v g) (hl : List.IsChain (titsComplex G H).G.Adj (v :: l)) :
    ∃ L : List (Letter H), Relation.EqvGen (Moves H) (v :: l) (v :: D g L) ∧
      ∀ w, (v :: l).getLast? = some w → Rep H w (g * val L) := by
  induction l generalizing v g with
  | nil =>
      refine ⟨[], Relation.EqvGen.refl _, fun w hw ↦ ?_⟩
      simp only [List.getLast?_singleton, Option.some.injEq] at hw
      subst hw
      rwa [val, mul_one]
  | cons w l ih =>
      rw [List.isChain_cons_cons] at hl
      obtain ⟨⟨-, k, hvk, hwk⟩, hrest⟩ := hl
      obtain ⟨L', h1, h2⟩ := ih w k hwk hrest
      refine ⟨⟨v.1, ⟨g⁻¹ * k, mem_of_rep_rep hv hvk⟩⟩ :: ⟨w.1, 1⟩ :: L', ?_, ?_⟩
      · have hD : D g (⟨v.1, ⟨g⁻¹ * k, mem_of_rep_rep hv hvk⟩⟩ :: ⟨w.1, 1⟩ :: L' : List (Letter H)) =
            v :: w :: D k L' := by
          show vtx H v.1 (g * (g⁻¹ * k)) :: vtx H w.1 (g * (g⁻¹ * k) * ↑(1 : H w.1)) ::
            D (g * (g⁻¹ * k) * ↑(1 : H w.1)) L' = v :: w :: D k L'
          rw [mul_inv_cancel_left, Subgroup.coe_one, mul_one, vtx_eq_of_rep hvk, vtx_eq_of_rep hwk]
        rw [hD]
        have hpre : Relation.EqvGen (Moves H) (v :: w :: l) (v :: w :: D k L') := by
          simpa only [List.singleton_append] using eqvGen_moves_append_left [v] h1
        have hst : Moves H (v :: v :: w :: D k L') (v :: w :: D k L') := by
          simpa only [List.nil_append] using Moves.stutter (H := H) [] (w :: D k L') v
        exact Relation.EqvGen.trans _ _ _ hpre (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hst))
      · intro w' hw'
        rw [List.getLast?_cons_cons] at hw'
        have e : g * val (⟨v.1, ⟨g⁻¹ * k, mem_of_rep_rep hv hvk⟩⟩ :: ⟨w.1, 1⟩ :: L' : List (Letter H)) =
            k * val L' := by
          show g * ((g⁻¹ * k) * (↑(1 : H w.1) * val L')) = k * val L'
          rw [Subgroup.coe_one, one_mul, ← mul_assoc, mul_inv_cancel_left]
        rw [e]
        exact h2 w' hw'

/-- **Closed edge paths reduce to a point**, given the typed word problem. -/
theorem loop_moves (hwp : ∀ L : List (Letter H), val L = 1 → Relation.EqvGen TypedMove L [])
    (v : Σ i : Fin 3, G ⧸ H i) (l : List (Σ i : Fin 3, G ⧸ H i))
    (hl : List.IsChain (titsComplex G H).G.Adj (v :: l ++ [v])) :
    Relation.EqvGen (Moves H) (v :: l ++ [v]) [v] := by
  obtain ⟨g, hv⟩ := exists_rep v
  obtain ⟨L, hm, hlast⟩ := encode v (l ++ [v]) g hv hl
  have hr : Rep H v (g * val L) := hlast v (by simp)
  set c : Letter H := ⟨v.1, ⟨(g * val L)⁻¹ * g, mem_of_rep_rep hr hv⟩⟩ with hc
  have hval : val (L ++ [c]) = 1 := by
    rw [val_append]
    show val L * (((g * val L)⁻¹ * g) * 1) = 1
    group
  have hc1 : D (g * val L) [c] = [v] := by
    show [vtx H v.1 (g * val L * ((g * val L)⁻¹ * g))] = [v]
    rw [mul_inv_cancel_left, vtx_eq_of_rep hv]
  have hT := eqvGen_transfer (hwp (L ++ [c]) hval) v g v.1 hv
  have hD1 : v :: D g (L ++ [c]) ++ [vtx H v.1 (g * val (L ++ [c]))] = (v :: D g L) ++ [v, v] := by
    rw [D_append, hc1, hval, mul_one, vtx_eq_of_rep hv]
    simp only [List.cons_append, List.append_assoc, List.singleton_append]
  have hDnil : v :: D g ([] : List (Letter H)) ++ [vtx H v.1 (g * val ([] : List (Letter H)))] =
      [v] ++ [v] := by
    show [v] ++ [vtx H v.1 (g * 1)] = [v] ++ [v]
    rw [mul_one, vtx_eq_of_rep hv]
  rw [hD1, hDnil] at hT
  have m1 : Moves H ((v :: l) ++ v :: v :: [v]) ((v :: l) ++ v :: [v]) := Moves.stutter (v :: l) [v] v
  have m2 : Moves H ((v :: l) ++ v :: v :: []) ((v :: l) ++ v :: []) := Moves.stutter (v :: l) [] v
  have e1 : Relation.EqvGen (Moves H) (v :: l ++ [v]) ((v :: (l ++ [v])) ++ [v, v]) := by
    have hshape : (v :: (l ++ [v])) ++ [v, v] = (v :: l) ++ v :: v :: [v] := by
      simp only [List.cons_append, List.append_assoc, List.singleton_append]
    rw [hshape]
    exact Relation.EqvGen.symm _ _
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ m1) (Relation.EqvGen.rel _ _ m2))
  have e2 := eqvGen_moves_append_right [v, v] hm
  have e5 : Relation.EqvGen (Moves H) ([v] ++ [v]) [v] := by
    simpa only [List.nil_append, List.singleton_append] using
      Relation.EqvGen.rel _ _ (Moves.stutter (H := H) [] [] v)
  exact Relation.EqvGen.trans _ _ _ e1 (Relation.EqvGen.trans _ _ _ e2
    (Relation.EqvGen.trans _ _ _ hT e5))

/-- **The typed word problem gives simple connectivity.** -/
theorem simplyConnected_of_typedWordProblem
    (hwp : ∀ L : List (Letter H), val L = 1 → Relation.EqvGen TypedMove L []) :
    SimplyConnected (titsComplex G H) :=
  simplyConnected_of_moves fun v l hl ↦ loop_moves hwp v l hl

/-! ### Connectedness -/

theorem reachable_of_rep {v w : Σ i : Fin 3, G ⧸ H i} {g : G} (hv : Rep H v g) (hw : Rep H w g) :
    (titsComplex G H).G.Reachable v w := by
  by_cases h : v = w
  · rw [h]
  · exact (adj_of_rep_ne hv hw h).reachable

theorem reachable_trace (L : List (Letter H)) :
    ∀ (v : Σ i : Fin 3, G ⧸ H i) (g : G), Rep H v g → ∀ i : Fin 3,
      (titsComplex G H).G.Reachable v (vtx H i (g * val L)) := by
  induction L with
  | nil =>
      intro v g hv i
      refine reachable_of_rep hv ?_
      show (QuotientGroup.mk (g * val ([] : List (Letter H))) : G ⧸ H i) = QuotientGroup.mk g
      rw [val, mul_one]
  | cons a L ih =>
      intro v g hv i
      have h1 := reachable_of_rep hv (rep_vtx_mul a.1 g a.2)
      have h2 := ih (vtx H a.1 (g * a.2)) (g * a.2) (rep_vtx _ _) i
      rw [← mul_assoc] at h2
      exact h1.trans h2

/-- **Generated groups have connected coset complexes.** -/
theorem connected_of_generated (hgen : ∀ g : G, ∃ L : List (Letter H), val L = g) :
    (titsComplex G H).G.Connected := by
  haveI : Nonempty (Σ i : Fin 3, G ⧸ H i) := ⟨vtx H 0 1⟩
  have hbase : ∀ w : Σ i : Fin 3, G ⧸ H i, (titsComplex G H).G.Reachable (vtx H 0 1) w := by
    intro w
    obtain ⟨k, hk⟩ := exists_rep w
    obtain ⟨L, hL⟩ := hgen k
    have h := reachable_trace L (vtx H 0 1) 1 (rep_vtx _ _) w.1
    rwa [one_mul, hL, vtx_eq_of_rep hk] at h
  exact ⟨fun u w ↦ (hbase u).symm.trans (hbase w)⟩

end GroupApproximation.CCKWTits

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CCKWTits.D_append
#audit_axioms GroupApproximation.CCKWTits.val_typedMove
#audit_axioms GroupApproximation.CCKWTits.mid_moves
#audit_axioms GroupApproximation.CCKWTits.transfer
#audit_axioms GroupApproximation.CCKWTits.encode
#audit_axioms GroupApproximation.CCKWTits.loop_moves
#audit_axioms GroupApproximation.CCKWTits.simplyConnected_of_typedWordProblem
#audit_axioms GroupApproximation.CCKWTits.connected_of_generated
