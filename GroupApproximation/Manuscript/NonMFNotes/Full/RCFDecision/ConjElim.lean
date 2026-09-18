import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.BKR
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.CandidatePoints

/-!
# Eliminating one existential quantifier from a conjunction of atoms

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  Fix an assignment `ρ` and a
conjunction `c` of atoms.  Every true leaf of `conjTree i c` evaluates to `true`
exactly when `∃ r ∈ ℝ, c` holds at `ρ[x_i ↦ r]` (`good_conjTree`).  The steps:

* `collect_spec`: after normalizing the coefficients in `x_i` of every atom,
  `collectAtoms` either detects a strict atom that vanishes identically in `x_i`
  (`none`), or turns `c` into a sign condition `sgnVec qs r = σ` on nonzero
  univariate polynomials `qs` (`CollectSpec`);
* `good_conjDecide`: a sign condition is realized iff it is realized at `±∞`, or
  at a root of `∏ qs` or of `(∏ qs)'` (`exists_sgnVec_iff`).  At a root it is
  detected by a positive Ben-Or--Kozen--Reif sum (`bkrSum_pos_iff`).
-/

namespace GroupApproximation.Full.NN11b

open Polynomial

/-! ## Signs of atoms -/

theorem sgn_eq_one_iff (v : ℝ) : sgn v = 1 ↔ 0 < v := by
  constructor
  · intro h
    rcases lt_trichotomy v 0 with h1 | h1 | h1
    · rw [ST.sgn_of_neg h1] at h
      exact absurd h (by norm_num)
    · rw [h1, ST.sgn_zero] at h
      exact absurd h (by norm_num)
    · exact h1
  · exact ST.sgn_of_pos

theorem sgn_eq_zero_iff (v : ℝ) : sgn v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    rcases ST.sgn_cases hv with h1 | h1
    · rw [h1] at h
      exact absurd h (by norm_num)
    · rw [h1] at h
      exact absurd h (by norm_num)
  · intro h
    rw [h, ST.sgn_zero]

theorem atomHolds_iff_sgn (ρ : ℕ → ℝ) (b : Bool) (p : MvP) :
    atomHolds ρ (b, p) ↔ sgn (mvEval ρ p) = if b then 1 else 0 := by
  cases b
  · rw [atomHolds_false, if_neg Bool.false_ne_true]
    exact (sgn_eq_zero_iff _).symm
  · have h1 : (true = true) := rfl
    rw [atomHolds_true, if_pos h1]
    exact (sgn_eq_one_iff _).symm

/-! ## Collecting the atoms -/

/-- The univariate polynomial of a collected atom. -/
noncomputable def nformPoly (ρ : ℕ → ℝ) (x : ℤ × (List MvP × MvP × Bool)) : ℝ[X] :=
  toPoly ρ (x.2.1 ++ [x.2.2.1])

/-- The specification of `collectAtoms` for the conjunction `c` at `ρ`, in the variable `x_i`. -/
def CollectSpec (ρ : ℕ → ℝ) (i : ℕ) (c : List Atom) :
    Option (List (ℤ × (List MvP × MvP × Bool))) → Prop
  | none => ∀ r : ℝ, ¬ guardHolds (Function.update ρ i r) c
  | some d => (∀ x ∈ d, (x.1 = 0 ∨ x.1 = 1) ∧ mvEval ρ x.2.2.1 ≠ 0 ∧
        sgn (mvEval ρ x.2.2.1) = bsgn x.2.2.2) ∧
      ∀ r : ℝ, (guardHolds (Function.update ρ i r) c ↔
        sgnVec (d.map (nformPoly ρ)) r = d.map Prod.fst)

theorem collectSpec_none (ρ : ℕ → ℝ) (i : ℕ) (c : List Atom) :
    CollectSpec ρ i c none ↔ ∀ r : ℝ, ¬ guardHolds (Function.update ρ i r) c :=
  Iff.rfl

theorem collectSpec_some (ρ : ℕ → ℝ) (i : ℕ) (c : List Atom)
    (d : List (ℤ × (List MvP × MvP × Bool))) :
    CollectSpec ρ i c (some d) ↔ (∀ x ∈ d, (x.1 = 0 ∨ x.1 = 1) ∧ mvEval ρ x.2.2.1 ≠ 0 ∧
        sgn (mvEval ρ x.2.2.1) = bsgn x.2.2.2) ∧
      ∀ r : ℝ, (guardHolds (Function.update ρ i r) c ↔
        sgnVec (d.map (nformPoly ρ)) r = d.map Prod.fst) :=
  Iff.rfl

theorem collectSpec_congr {ρ : ℕ → ℝ} {i : ℕ} {c c' : List Atom}
    (hc : ∀ r : ℝ, guardHolds (Function.update ρ i r) c' ↔ guardHolds (Function.update ρ i r) c) :
    ∀ od : Option (List (ℤ × (List MvP × MvP × Bool))),
      CollectSpec ρ i c od → CollectSpec ρ i c' od
  | none, h => (collectSpec_none ρ i c').2 fun r hr =>
      (collectSpec_none ρ i c).1 h r ((hc r).1 hr)
  | some d, h => by
      have h' := (collectSpec_some ρ i c d).1 h
      exact (collectSpec_some ρ i c' d).2 ⟨h'.1, fun r => (hc r).trans (h'.2 r)⟩

theorem collectSpec_cons_some {ρ : ℕ → ℝ} {i : ℕ} {b : Bool} {p : MvP} {c : List Atom}
    {n : List MvP × MvP × Bool} (hn : NormSpec ρ (coeffX i p) (some n)) :
    ∀ od : Option (List (ℤ × (List MvP × MvP × Bool))), CollectSpec ρ i c od →
      CollectSpec ρ i ((b, p) :: c) (od.map (List.cons ((if b then 1 else 0 : ℤ), n)))
  | none, h => by
      have h' := (collectSpec_none ρ i c).1 h
      exact (collectSpec_none ρ i ((b, p) :: c)).2 fun r hr =>
        h' r ((guardHolds_cons _ _ _).1 hr).2
  | some d, h => by
      obtain ⟨b', bl, s⟩ := n
      have hn' : toPoly ρ (coeffX i p) = toPoly ρ (b' ++ [bl]) ∧ mvEval ρ bl ≠ 0 ∧
          sgn (mvEval ρ bl) = bsgn s ∧ b'.length < (coeffX i p).length := hn
      have h' := (collectSpec_some ρ i c d).1 h
      refine (collectSpec_some ρ i ((b, p) :: c)
        (((if b then 1 else 0 : ℤ), (b', bl, s)) :: d)).2 ⟨?_, fun r => ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · refine ⟨?_, hn'.2.1, hn'.2.2.1⟩
          cases b
          · exact Or.inl rfl
          · exact Or.inr rfl
        · exact h'.1 x hx'
      · have e1 : sgnVec ((((if b then 1 else 0 : ℤ), (b', bl, s)) :: d).map (nformPoly ρ)) r =
            sgn ((toPoly ρ (b' ++ [bl])).eval r) :: sgnVec (d.map (nformPoly ρ)) r := rfl
        have e2 : (((if b then 1 else 0 : ℤ), (b', bl, s)) :: d).map Prod.fst =
            (if b then 1 else 0 : ℤ) :: d.map Prod.fst := rfl
        rw [e1, e2, guardHolds_cons, h'.2 r, atomHolds_iff_sgn, ← eval_toPoly_coeffX ρ i r p,
          hn'.1]
        exact List.cons_eq_cons.symm

/-- **Collecting atoms**: `collectAtoms` meets `CollectSpec` whenever every
normalization it reads meets `NormSpec`. -/
theorem collect_spec (ρ : ℕ → ℝ) (i : ℕ) :
    ∀ (c : List Atom) (os : List (Option (List MvP × MvP × Bool))),
      AllRel (fun (a : Atom) (o : Option (List MvP × MvP × Bool)) =>
        NormSpec ρ (coeffX i a.2) o) c os → CollectSpec ρ i c (collectAtoms c os)
  | [], [], _ => by
      show CollectSpec ρ i [] (some [])
      refine (collectSpec_some ρ i [] []).2 ⟨fun _ hx => absurd hx List.not_mem_nil, fun _ => ?_⟩
      exact ⟨fun _ => rfl, fun _ => guardHolds_nil _⟩
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | (true, p) :: c, none :: _, h => by
      obtain ⟨hn, _⟩ := h
      have h0 : toPoly ρ (coeffX i p) = 0 := hn
      show CollectSpec ρ i ((true, p) :: c) none
      refine (collectSpec_none ρ i ((true, p) :: c)).2 fun r hr => ?_
      have hv : mvEval (Function.update ρ i r) p = 0 := by
        rw [← eval_toPoly_coeffX ρ i r p, h0, eval_zero]
      have hpos : 0 < mvEval (Function.update ρ i r) p := ((guardHolds_cons _ _ _).1 hr).1
      rw [hv] at hpos
      exact lt_irrefl 0 hpos
  | (false, p) :: c, none :: os, h => by
      obtain ⟨hn, h2⟩ := h
      have h0 : toPoly ρ (coeffX i p) = 0 := hn
      show CollectSpec ρ i ((false, p) :: c) (collectAtoms c os)
      refine collectSpec_congr (c := c) (fun r => ?_) _ (collect_spec ρ i c os h2)
      have hv : mvEval (Function.update ρ i r) p = 0 := by
        rw [← eval_toPoly_coeffX ρ i r p, h0, eval_zero]
      rw [guardHolds_cons, atomHolds_false]
      exact ⟨fun h' => h'.2, fun h' => ⟨hv, h'⟩⟩
  | (b, p) :: c, some n :: os, h => by
      obtain ⟨hn, h2⟩ := h
      have hn' : NormSpec ρ (coeffX i p) (some n) := hn
      have e : collectAtoms ((b, p) :: c) (some n :: os) =
          (collectAtoms c os).map (List.cons ((if b then 1 else 0 : ℤ), n)) := by
        cases b <;> rfl
      rw [e]
      exact collectSpec_cons_some hn' _ (collect_spec ρ i c os h2)

/-! ## Deciding a sign condition -/

theorem toPoly_prodUP (ρ : ℕ → ℝ) :
    ∀ us : List (List MvP), toPoly ρ (prodUP us) = (us.map (toPoly ρ)).prod
  | [] => toPoly_upOne ρ
  | u :: us => by
      show toPoly ρ (upMul u (prodUP us)) = toPoly ρ u * (us.map (toPoly ρ)).prod
      rw [toPoly_upMul, toPoly_prodUP ρ us]

/-- **Deciding a sign condition**: every true leaf of `conjDecide d` evaluates to
`true` exactly when the sign condition collected in `d` is realized on `ℝ`. -/
theorem good_conjDecide (ρ : ℕ → ℝ) (d : List (ℤ × (List MvP × MvP × Bool)))
    (hd : ∀ x ∈ d, (x.1 = 0 ∨ x.1 = 1) ∧ mvEval ρ x.2.2.1 ≠ 0 ∧
      sgn (mvEval ρ x.2.2.1) = bsgn x.2.2.2) :
    Good ρ (conjDecide d)
      (fun b => b = true ↔ ∃ r : ℝ, sgnVec (d.map (nformPoly ρ)) r = d.map Prod.fst) := by
  have hps : ∀ q ∈ d.map (nformPoly ρ), q ≠ 0 := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
    exact toPoly_append_single_ne_zero ρ x.2.1 x.2.2.1 (hd x hx).2.1
  have hE := exists_sgnVec_iff (d.map (nformPoly ρ)) hps (d.map Prod.fst)
  have hTop : (d.map (nformPoly ρ)).map sgnTop = d.map fun x => bsgn x.2.2.2 := by
    rw [List.map_map]
    refine List.map_congr_left fun x hx => ?_
    exact congrArg Prod.fst (sgnPair_toPoly ρ x.2.1 x.2.2.1 x.2.2.2 (hd x hx).2.1 (hd x hx).2.2)
  have hBot : (d.map (nformPoly ρ)).map sgnBot =
      d.map fun x => bsgn x.2.2.2 * (-1) ^ x.2.1.length := by
    rw [List.map_map]
    refine List.map_congr_left fun x hx => ?_
    exact congrArg Prod.snd (sgnPair_toPoly ρ x.2.1 x.2.2.1 x.2.2.2 (hd x hx).2.1 (hd x hx).2.2)
  have hus : (d.map fun x => x.2.1 ++ [x.2.2.1]).map (toPoly ρ) = d.map (nformPoly ρ) :=
    List.map_map.trans (List.map_congr_left fun _ _ => rfl)
  have hlen : (d.map Prod.fst).length = (d.map (nformPoly ρ)).length := by
    rw [List.length_map, List.length_map]
  have hσ : ∀ s ∈ d.map Prod.fst, s = 0 ∨ s = 1 ∨ s = -1 := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    rcases (hd x hx).1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  show Good ρ (if d.map (fun x => bsgn x.2.2.2) = d.map Prod.fst ∨
      d.map (fun x => bsgn x.2.2.2 * (-1) ^ x.2.1.length) = d.map Prod.fst
    then tpure true
    else tmap (fun z : ℤ × ℤ => decide (0 < z.1) || decide (0 < z.2))
      (tbind (bkrTree (prodUP (d.map fun x => x.2.1 ++ [x.2.2.1]))
          (d.map fun x => x.2.1 ++ [x.2.2.1]) (d.map Prod.fst)) fun z1 =>
        tmap (Prod.mk z1) (bkrTree (upDeriv (prodUP (d.map fun x => x.2.1 ++ [x.2.2.1])))
          (d.map fun x => x.2.1 ++ [x.2.2.1]) (d.map Prod.fst)))) _
  by_cases hc : d.map (fun x => bsgn x.2.2.2) = d.map Prod.fst ∨
      d.map (fun x => bsgn x.2.2.2 * (-1) ^ x.2.1.length) = d.map Prod.fst
  · rw [if_pos hc]
    refine good_pure ρ ?_
    show true = true ↔ ∃ r : ℝ, sgnVec (d.map (nformPoly ρ)) r = d.map Prod.fst
    refine ⟨fun _ => hE.2 (Or.inr (Or.inr ?_)), fun _ => rfl⟩
    rw [hTop, hBot]
    exact hc
  · rw [if_neg hc]
    apply good_tmap
    apply good_bind
    refine good_mono (good_bkrTree ρ (prodUP (d.map fun x => x.2.1 ++ [x.2.2.1]))
      (d.map fun x => x.2.1 ++ [x.2.2.1]) (d.map Prod.fst)) fun z1 hz1 => ?_
    have hz1' : z1 = bkrSum (toPoly ρ (prodUP (d.map fun x => x.2.1 ++ [x.2.2.1])))
        ((d.map fun x => x.2.1 ++ [x.2.2.1]).map (toPoly ρ)) (d.map Prod.fst) := hz1
    apply good_tmap
    refine good_mono (good_bkrTree ρ (upDeriv (prodUP (d.map fun x => x.2.1 ++ [x.2.2.1])))
      (d.map fun x => x.2.1 ++ [x.2.2.1]) (d.map Prod.fst)) fun z2 hz2 => ?_
    have hz2' : z2 = bkrSum (toPoly ρ (upDeriv (prodUP (d.map fun x => x.2.1 ++ [x.2.2.1]))))
        ((d.map fun x => x.2.1 ++ [x.2.2.1]).map (toPoly ρ)) (d.map Prod.fst) := hz2
    show (decide (0 < z1) || decide (0 < z2)) = true ↔
      ∃ r : ℝ, sgnVec (d.map (nformPoly ρ)) r = d.map Prod.fst
    rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff, hz1', hz2', toPoly_upDeriv,
      toPoly_prodUP, hus, bkrSum_pos_iff _ _ _ hlen hσ, bkrSum_pos_iff _ _ _ hlen hσ, hE]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (Or.inl (hTop.symm.trans h)) hc
      · exact absurd (Or.inr (hBot.symm.trans h)) hc

/-! ## One quantifier -/

theorem good_elimCollect (ρ : ℕ → ℝ) (i : ℕ) (c : List Atom) :
    ∀ od : Option (List (ℤ × (List MvP × MvP × Bool))), CollectSpec ρ i c od →
      Good ρ (od.elim (tpure false) conjDecide)
        (fun b => b = true ↔ ∃ r : ℝ, guardHolds (Function.update ρ i r) c)
  | none, h => by
      have h' := (collectSpec_none ρ i c).1 h
      show Good ρ (tpure false) _
      refine good_pure ρ ?_
      show false = true ↔ ∃ r : ℝ, guardHolds (Function.update ρ i r) c
      exact ⟨fun h1 => absurd h1 Bool.false_ne_true, fun ⟨r, hr⟩ => absurd hr (h' r)⟩
  | some d, h => by
      have h' := (collectSpec_some ρ i c d).1 h
      show Good ρ (conjDecide d) _
      refine good_mono (good_conjDecide ρ d h'.1) fun b hb => ?_
      have hb' : b = true ↔ ∃ r : ℝ, sgnVec (d.map (nformPoly ρ)) r = d.map Prod.fst := hb
      exact hb'.trans ⟨fun ⟨r, hr⟩ => ⟨r, (h'.2 r).2 hr⟩, fun ⟨r, hr⟩ => ⟨r, (h'.2 r).1 hr⟩⟩

/-- **Eliminating one existential quantifier**: every true leaf of `conjTree i c`
evaluates to `true` exactly when `∃ x_i, c` holds at `ρ`. -/
theorem good_conjTree (ρ : ℕ → ℝ) (i : ℕ) (c : List Atom) :
    Good ρ (conjTree i c) (fun b => b = true ↔ ∃ r : ℝ, guardHolds (Function.update ρ i r) c) := by
  unfold conjTree
  apply good_bind
  refine good_mono (good_tseq ρ (fun (a : Atom) (o : Option (List MvP × MvP × Bool)) =>
    NormSpec ρ (coeffX i a.2) o) (atomTree i) c fun a _ => good_normUP ρ (coeffX i a.2)) ?_
  intro os hos
  exact good_elimCollect ρ i c _ (collect_spec ρ i c os hos)

end GroupApproximation.Full.NN11b
