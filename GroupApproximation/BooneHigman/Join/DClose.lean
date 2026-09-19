import GroupApproximation.BooneHigman.Join.DFEL

/-!
# Expansion along paths, and right multiplication by letters (lane bh-pal-met-join)

* `dpath_expand`: if `c` is a word of the code `L` and `σ ∈ jH L`, then `σ = f · σ'` with
  `f ∈ PhiD` and `σ'` on a code `L'` containing `c s`.  Words of `L` not above `c s` survive.
  Words incomparable with `c s` that are at or below `L` stay at or below `L'`.
* `procL`: right multiplication by a product of letters whose words are at or below `L` and
  pairwise separated keeps the form `f · σ'`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {n : ℕ}

/-- `z` lies at or below a word of `L`. -/
def AtB (L : List (List (Fin (n + 2)))) (z : List (Fin (n + 2))) : Prop := ∃ w ∈ L, w <+: z

#audit_axioms GroupApproximation.BooneHigman.Join.AtB

theorem atB_exp {L L' : List (List (Fin (n + 2)))} {c : List (Fin (n + 2))}
    (hm : ∀ x, x ∈ L' ↔ x ∈ exF L c) {z : List (Fin (n + 2))} (hz : AtB L z) (hzc : z ≠ c) :
    AtB L' z := by
  obtain ⟨w, hw, hwz⟩ := hz
  by_cases hwc : w = c
  · rw [hwc] at hwz
    obtain ⟨t, rfl⟩ := hwz
    cases t with
    | nil => exact absurd (List.append_nil c) hzc
    | cons b t =>
      exact ⟨c ++ [b], (hm _).mpr (mem_exF.mpr (Or.inr ⟨b, rfl⟩)), ⟨t, by simp⟩⟩
  · exact ⟨w, (hm _).mpr (mem_exF.mpr (Or.inl ⟨hw, hwc⟩)), hwz⟩

#audit_axioms GroupApproximation.BooneHigman.Join.atB_exp

theorem jH_of_exF {L L' : List (List (Fin (n + 2)))} {c : List (Fin (n + 2))}
    (hm : ∀ x, x ∈ L' ↔ x ∈ exF L c) {ρ : higmanVCCommon_Q (n + 2)}
    (hρ : ρ ∈ jH (n + 2) (exF L c)) : ρ ∈ jH (n + 2) L'.toFinset :=
  jH_mono (fun x hx => List.mem_toFinset.mpr ((hm x).mpr hx)) hρ

#audit_axioms GroupApproximation.BooneHigman.Join.jH_of_exF

/-- **Expansion along a path.** -/
theorem dpath_expand : ∀ (s : List (Fin (n + 2))) (L : List (List (Fin (n + 2)))), IsCode n L →
    ∀ c ∈ L, ∀ σ ∈ jH (n + 2) L.toFinset, ∃ L', IsCode n L' ∧ ∃ f ∈ PhiD n,
      ∃ σ' ∈ jH (n + 2) L'.toFinset, σ = f * σ' ∧ c ++ s ∈ L' ∧
      (∀ w ∈ L, ¬ w <+: c ++ s → w ∈ L') ∧ ∀ z, ¬ z <+: c ++ s → AtB L z → AtB L' z
  | [], L, hL, c, hc, σ, hσ =>
    ⟨L, hL, 1, (PhiD n).one_mem, σ, hσ, (one_mul σ).symm, by rwa [List.append_nil],
      fun w hw _ => hw, fun z _ hz => hz⟩
  | a :: s, L, hL, c, hc, σ, hσ => by
    obtain ⟨d', hd', f₁, hf₁, ρ, hρ, e, -⟩ := dfel hL hσ c hc
    obtain ⟨L₁, hL₁, hm⟩ := hL.expand hc
    have hca : c ++ [a] ∈ L₁ := (hm _).mpr (mem_exF.mpr (Or.inr ⟨a, rfl⟩))
    obtain ⟨L', hL', f₂, hf₂, σ', hσ', e', hmem, hsurv, hpres⟩ :=
      dpath_expand s L₁ hL₁ (c ++ [a]) hca ρ (jH_of_exF hm hρ)
    have hcs : c ++ [a] ++ s = c ++ a :: s := by simp
    rw [hcs] at hmem hsurv hpres
    refine ⟨L', hL', f₁ * f₂, (PhiD n).mul_mem hf₁ hf₂, σ', hσ', by rw [e, e', mul_assoc], hmem,
      ?_, ?_⟩
    · intro w hw hwp
      refine hsurv w ((hm w).mpr (mem_exF.mpr (Or.inl ⟨hw, ?_⟩))) hwp
      intro hwc
      rw [hwc] at hwp
      exact hwp (List.prefix_append c (a :: s))
    · intro z hz hzL
      refine hpres z hz (atB_exp hm hzL ?_)
      intro hzc
      rw [hzc] at hz
      exact hz (List.prefix_append c (a :: s))

#audit_axioms GroupApproximation.BooneHigman.Join.dpath_expand

/-- Two letters with pairwise incomparable words. -/
def Sep (P P' : List (Fin (n + 2)) × List (Fin (n + 2))) : Prop :=
  Inc P.1 P'.1 ∧ Inc P.1 P'.2 ∧ Inc P.2 P'.1 ∧ Inc P.2 P'.2

#audit_axioms GroupApproximation.BooneHigman.Join.Sep

theorem mul_prod_eq {G : Type*} [Group G] {σ f₁ σ₁ f₂ σ₂ a r f₃ σ' : G} (e₁ : σ = f₁ * σ₁)
    (e₂ : σ₁ = f₂ * σ₂) (e₃ : σ₂ * a * r = f₃ * σ') : σ * (a * r) = f₁ * f₂ * f₃ * σ' := by
  rw [e₁, e₂]
  calc f₁ * (f₂ * σ₂) * (a * r) = f₁ * f₂ * (σ₂ * a * r) := by group
    _ = f₁ * f₂ * f₃ * σ' := by rw [e₃]; group

#audit_axioms GroupApproximation.BooneHigman.Join.mul_prod_eq

/-- **Right multiplication by separated letters keeps the form.** -/
theorem procL : ∀ (ps : List (List (Fin (n + 2)) × List (Fin (n + 2))))
    (L : List (List (Fin (n + 2)))), IsCode n L → ∀ σ ∈ jH (n + 2) L.toFinset,
    (∀ P ∈ ps, Inc P.1 P.2 ∧ AtB L P.1 ∧ AtB L P.2) → ps.Pairwise Sep →
    ∃ L', IsCode n L' ∧ ∃ f ∈ PhiD n, ∃ σ' ∈ jH (n + 2) L'.toFinset,
      σ * (ps.map fun P => jL P.1 P.2).prod = f * σ'
  | [], L, hL, σ, hσ, _, _ => ⟨L, hL, 1, (PhiD n).one_mem, σ, hσ, by simp⟩
  | P :: ps, L, hL, σ, hσ, hps, hsep => by
    rw [List.pairwise_cons] at hsep
    obtain ⟨hinc, hp, hq⟩ := hps P List.mem_cons_self
    obtain ⟨c, hc, s, hcs⟩ := hp
    obtain ⟨L₁, hL₁, f₁, hf₁, σ₁, hσ₁, e₁, hmem₁, hsurv₁, hpres₁⟩ := dpath_expand s L hL c hc σ hσ
    rw [hcs] at hmem₁ hsurv₁ hpres₁
    obtain ⟨c', hc', s', hcs'⟩ := hpres₁ P.2 hinc.2 hq
    obtain ⟨L₂, hL₂, f₂, hf₂, σ₂, hσ₂, e₂, hmem₂, hsurv₂, hpres₂⟩ :=
      dpath_expand s' L₁ hL₁ c' hc' σ₁ hσ₁
    rw [hcs'] at hmem₂ hsurv₂ hpres₂
    have hp₂ : P.1 ∈ L₂ := hsurv₂ _ hmem₁ hinc.1
    have hσ₃ : σ₂ * jL P.1 P.2 ∈ jH (n + 2) L₂.toFinset :=
      (jH (n + 2) _).mul_mem hσ₂ (jL_mem_jH (List.mem_toFinset.mpr hp₂) (List.mem_toFinset.mpr hmem₂))
    have hrest : ∀ P' ∈ ps, Inc P'.1 P'.2 ∧ AtB L₂ P'.1 ∧ AtB L₂ P'.2 := by
      intro P' hP'
      obtain ⟨i1, i2, i3, i4⟩ := hsep.1 P' hP'
      obtain ⟨j0, j1, j2⟩ := hps P' (List.mem_cons_of_mem P hP')
      exact ⟨j0, hpres₂ _ i3.2 (hpres₁ _ i1.2 j1), hpres₂ _ i4.2 (hpres₁ _ i2.2 j2)⟩
    obtain ⟨L', hL', f₃, hf₃, σ', hσ', e₃⟩ := procL ps L₂ hL₂ _ hσ₃ hrest hsep.2
    refine ⟨L', hL', f₁ * f₂ * f₃, (PhiD n).mul_mem ((PhiD n).mul_mem hf₁ hf₂) hf₃, σ', hσ', ?_⟩
    rw [List.map_cons, List.prod_cons]
    exact mul_prod_eq e₁ e₂ e₃

#audit_axioms GroupApproximation.BooneHigman.Join.procL

end GroupApproximation.BooneHigman.Join
