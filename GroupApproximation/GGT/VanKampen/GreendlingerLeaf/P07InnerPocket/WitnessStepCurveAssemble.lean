import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCurveSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-66: assembling the doubled bounce chain

Lane gl-p07-66.  Certifies no printed sentence on its own.  NOT COMPILED: authored without
running Lean.

Let `Γ = B ++ G₂ ++ A ++ G₁` and write `Hop' p q` for `Hop (α p) q`.  Suppose four
`Hop'`-chains are given,
`α z₁ · B · α z₂`, `z₂ · G₂ · z₃`, `α z₃ · A · α z₄` and `z₄ · G₁ · z₁`,
and the four darts `z_k` are bounces: `z_k ∉ Γ` and `α z_k ∉ Γ`.

Math.
* Each chain is a `Rel` chain once its head is replaced by the reverse of the head
  (`witnessStepCurve_rel_segment`): the heads become `z₁`, `α z₂`, `z₃`, `α z₄`, all off `Γ`.
* Glued at the common ends they give the closed `Rel` chain
  `z₁ · B · α z₂ · G₂ · z₃ · A · α z₄ · G₁ · z₁`, which doubles.
* Deleting the darts off `Γ` (the four bounces) keeps a chain, because `Rel` composes through
  bounces (`witnessStepCurve_rel_trans`), and leaves `Γ ++ Γ`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u

namespace FourPieceWitness

/-- A dart of one of four blocks is a dart of their concatenation. -/
theorem witnessStepCurve_mem_four {β : Type*} {l₁ l₂ l₃ l₄ : List β} {d : β}
    (h : d ∈ l₁ ∨ d ∈ l₂ ∨ d ∈ l₃ ∨ d ∈ l₄) : d ∈ l₁ ++ l₂ ++ l₃ ++ l₄ := by
  rcases h with h | h | h | h
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
  · exact List.mem_append_left _ (List.mem_append_right _ h)
  · exact List.mem_append_right _ h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_mem_four

/-- A dart off four blocks is off their concatenation. -/
theorem witnessStepCurve_not_mem_four {β : Type*} {l₁ l₂ l₃ l₄ : List β} {d : β}
    (h₁ : d ∉ l₁) (h₂ : d ∉ l₂) (h₃ : d ∉ l₃) (h₄ : d ∉ l₄) : d ∉ l₁ ++ l₂ ++ l₃ ++ l₄ := by
  intro h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact h₁ h
      · exact h₂ h
    · exact h₃ h
  · exact h₄ h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_not_mem_four

/-- A property of every dart of a doubled closed list. -/
theorem witnessStepCurve_forall_double {β : Type*} {P : β → Prop} {v : β} {L : List β}
    (hv : P v) (hL : ∀ y ∈ L, P y) : ∀ y ∈ v :: (L ++ v :: L), P y := by
  intro y hy
  rcases List.mem_cons.mp hy with h | h
  · rw [h]
    exact hv
  · rcases List.mem_append.mp h with h | h
    · exact hL y h
    · rcases List.mem_cons.mp h with h | h
      · rw [h]
        exact hv
      · exact hL y h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_forall_double

/-- A property of every dart of four blocks separated by three darts. -/
theorem witnessStepCurve_forall_seven {β : Type*} {P : β → Prop} {B G₂ A G₁ : List β}
    {z₂ z₃ z₄ : β} (hB : ∀ d ∈ B, P d) (h₂ : P z₂) (hG₂ : ∀ d ∈ G₂, P d) (h₃ : P z₃)
    (hA : ∀ d ∈ A, P d) (h₄ : P z₄) (hG₁ : ∀ d ∈ G₁, P d) :
    ∀ y ∈ B ++ z₂ :: (G₂ ++ z₃ :: (A ++ z₄ :: G₁)), P y := by
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · exact hB y h
  rcases List.mem_cons.mp h with h | h
  · rw [h]
    exact h₂
  rcases List.mem_append.mp h with h | h
  · exact hG₂ y h
  rcases List.mem_cons.mp h with h | h
  · rw [h]
    exact h₃
  rcases List.mem_append.mp h with h | h
  · exact hA y h
  rcases List.mem_cons.mp h with h | h
  · rw [h]
    exact h₄
  · exact hG₁ y h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_forall_seven

/-- **The glued closed bounce chain.** -/
theorem witnessStepCurve_closed_chain {M : CombMap.{u}} {Γ B G₂ A G₁ : List M.Dart}
    {z₁ z₂ z₃ z₄ : M.Dart} (hB : ∀ d ∈ B, d ∈ Γ) (hG₂ : ∀ d ∈ G₂, d ∈ Γ)
    (hA : ∀ d ∈ A, d ∈ Γ) (hG₁ : ∀ d ∈ G₁, d ∈ Γ)
    (hSb : (M.alpha z₁ :: (B ++ [M.alpha z₂])).IsChain
      (fun p q => witnessStepCurve_Hop M Γ (M.alpha p) q))
    (hS2 : (z₂ :: (G₂ ++ [z₃])).IsChain (fun p q => witnessStepCurve_Hop M Γ (M.alpha p) q))
    (hSa : (M.alpha z₃ :: (A ++ [M.alpha z₄])).IsChain
      (fun p q => witnessStepCurve_Hop M Γ (M.alpha p) q))
    (hS1 : (z₄ :: (G₁ ++ [z₁])).IsChain (fun p q => witnessStepCurve_Hop M Γ (M.alpha p) q))
    (h₁ : z₁ ∉ Γ) (h₂ : M.alpha z₂ ∉ Γ) (h₃ : z₃ ∉ Γ) (h₄ : M.alpha z₄ ∉ Γ) :
    (z₁ :: ((B ++ M.alpha z₂ :: (G₂ ++ z₃ :: (A ++ M.alpha z₄ :: G₁))) ++ [z₁])).IsChain
      (witnessStepCurve_Rel M Γ) := by
  have h₁' : M.alpha (M.alpha z₁) ∉ Γ := by
    rw [M.alpha_involutive z₁]
    exact h₁
  have h₃' : M.alpha (M.alpha z₃) ∉ Γ := by
    rw [M.alpha_involutive z₃]
    exact h₃
  have cb := witnessStepCurve_rel_segment B (M.alpha z₁) (M.alpha (M.alpha z₁)) hSb
    (witnessStepCurve_rel_of_bounce h₁') hB
  have c2 := witnessStepCurve_rel_segment G₂ z₂ (M.alpha z₂) hS2
    (witnessStepCurve_rel_of_bounce h₂) hG₂
  have ca := witnessStepCurve_rel_segment A (M.alpha z₃) (M.alpha (M.alpha z₃)) hSa
    (witnessStepCurve_rel_of_bounce h₃') hA
  have c1 := witnessStepCurve_rel_segment G₁ z₄ (M.alpha z₄) hS1
    (witnessStepCurve_rel_of_bounce h₄) hG₁
  rw [M.alpha_involutive z₁] at cb
  rw [M.alpha_involutive z₃] at ca
  have g1 := witnessStepCurve_chain_glue A z₃ ca c1
  have g2 := witnessStepCurve_chain_glue G₂ (M.alpha z₂) c2 g1
  have g3 := witnessStepCurve_chain_glue B z₁ cb g2
  simpa only [List.append_assoc, List.cons_append] using g3

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_closed_chain

open scoped Classical in
/-- **The doubled bounce chain.**  Four `Hop'`-chains through the blocks of
`Γ = B ++ G₂ ++ A ++ G₁`, joined at four bounce darts, make `Γ ++ Γ` a `Rel` chain. -/
theorem witnessStepCurve_double_chain {M : CombMap.{u}} {Γ B G₂ A G₁ : List M.Dart}
    {z₁ z₂ z₃ z₄ : M.Dart} (hΓ : Γ = B ++ G₂ ++ A ++ G₁)
    (hSb : (M.alpha z₁ :: (B ++ [M.alpha z₂])).IsChain
      (fun p q => witnessStepCurve_Hop M Γ (M.alpha p) q))
    (hS2 : (z₂ :: (G₂ ++ [z₃])).IsChain (fun p q => witnessStepCurve_Hop M Γ (M.alpha p) q))
    (hSa : (M.alpha z₃ :: (A ++ [M.alpha z₄])).IsChain
      (fun p q => witnessStepCurve_Hop M Γ (M.alpha p) q))
    (hS1 : (z₄ :: (G₁ ++ [z₁])).IsChain (fun p q => witnessStepCurve_Hop M Γ (M.alpha p) q))
    (h₁ : z₁ ∉ Γ ∧ M.alpha z₁ ∉ Γ) (h₂ : z₂ ∉ Γ ∧ M.alpha z₂ ∉ Γ)
    (h₃ : z₃ ∉ Γ ∧ M.alpha z₃ ∉ Γ) (h₄ : z₄ ∉ Γ ∧ M.alpha z₄ ∉ Γ) :
    (Γ ++ Γ).IsChain (witnessStepCurve_Rel M Γ) := by
  have hB : ∀ d ∈ B, d ∈ Γ := fun d hd => by
    rw [hΓ]
    exact witnessStepCurve_mem_four (Or.inl hd)
  have hG₂ : ∀ d ∈ G₂, d ∈ Γ := fun d hd => by
    rw [hΓ]
    exact witnessStepCurve_mem_four (Or.inr (Or.inl hd))
  have hA : ∀ d ∈ A, d ∈ Γ := fun d hd => by
    rw [hΓ]
    exact witnessStepCurve_mem_four (Or.inr (Or.inr (Or.inl hd)))
  have hG₁ : ∀ d ∈ G₁, d ∈ Γ := fun d hd => by
    rw [hΓ]
    exact witnessStepCurve_mem_four (Or.inr (Or.inr (Or.inr hd)))
  have h₂' : M.alpha z₂ ∉ Γ ∧ M.alpha (M.alpha z₂) ∉ Γ := by
    rw [M.alpha_involutive z₂]
    exact ⟨h₂.2, h₂.1⟩
  have h₄' : M.alpha z₄ ∉ Γ ∧ M.alpha (M.alpha z₄) ∉ Γ := by
    rw [M.alpha_involutive z₄]
    exact ⟨h₄.2, h₄.1⟩
  have hd := witnessStepCurve_chain_double
    (witnessStepCurve_closed_chain hB hG₂ hA hG₁ hSb hS2 hSa hS1 h₁.1 h₂.2 h₃.1 h₄.2)
  have hP := witnessStepCurve_forall_double (P := fun y => y ∈ Γ ∨ (y ∉ Γ ∧ M.alpha y ∉ Γ))
    (Or.inr h₁) (witnessStepCurve_forall_seven (B := B) (G₂ := G₂) (A := A) (G₁ := G₁)
      (fun d hd => Or.inl (hB d hd)) (Or.inr h₂') (fun d hd => Or.inl (hG₂ d hd))
      (Or.inr h₃) (fun d hd => Or.inl (hA d hd)) (Or.inr h₄') (fun d hd => Or.inl (hG₁ d hd)))
  have hf := witnessStepCurve_chain_filter (fun e => decide (e ∈ Γ))
    (fun y => y ∉ Γ ∧ M.alpha y ∉ Γ)
    (fun _ y _ r₁ r₂ (hq : y ∉ Γ ∧ M.alpha y ∉ Γ) => witnessStepCurve_rel_trans r₁ r₂ hq.1 hq.2)
    _ hd (fun y hy (hp : decide (y ∈ Γ) = false) => Or.resolve_left (hP y hy)
      (of_decide_eq_false hp))
  have hL := witnessStepCurve_filter_four (fun e => decide (e ∈ Γ))
    (B := B) (G₂ := G₂) (A := A) (G₁ := G₁) (z₂ := M.alpha z₂) (z₃ := z₃) (z₄ := M.alpha z₄)
    (fun d hd => @decide_eq_true _ (_) (hB d hd)) (fun h => h₂.2 (of_decide_eq_true h))
    (fun d hd => @decide_eq_true _ (_) (hG₂ d hd)) (fun h => h₃.1 (of_decide_eq_true h))
    (fun d hd => @decide_eq_true _ (_) (hA d hd)) (fun h => h₄.2 (of_decide_eq_true h))
    (fun d hd => @decide_eq_true _ (_) (hG₁ d hd))
  have he := witnessStepCurve_filter_double (fun e => decide (e ∈ Γ)) (z := z₁)
    (fun h => h₁.1 (of_decide_eq_true h)) (hL.trans hΓ.symm)
  rw [he] at hf
  exact hf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_double_chain

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
