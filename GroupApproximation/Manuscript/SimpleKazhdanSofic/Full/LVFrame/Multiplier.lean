import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.Separation
import GroupApproximation.Meta.AxiomGuard

/-!
# The simultaneous word multiplier (Khanh Lemma 4.1, first half)

Lane `sk-leavitt-08`, Khanh (arXiv:2609.08428v1), Lemma 4.1 (`lem:word-multiplier`).

Khanh, tex l.338: "Given finitely many nonzero $a_1,\ldots,a_s\in R$, there are $x\in R$ and
nonempty positive words $\eta_1,\ldots,\eta_s$ such that $\eta_i^*a_ix=1$ for every $i$."

Khanh, tex l.344: "For every $i$, at least one is nonzero, since
$a_i=\sum_j(a_i\gamma_j)\gamma_j^*$."  Khanh, tex l.346: "Put $t_j=e^{j(L+1)}f$ and
$x_0=\sum_j\gamma_jt_j$. ... Thus $P_i=a_ix_0$ is a nonempty positive polynomial for each $i$."

## Route (a simplification of Khanh's `x_0`)

With `R = L_{F_2}(1,2)`, `η^* = wordT η`, positive word `μ = wordS μ`.
* Take `D ≥` every depth from `exists_posPoly_mul_wordS`, write `a_i s_γ = posPoly (T_i γ)` for
  all `γ` of length `D`, and put `x_0 = ∑_{|γ| = D} s_γ s_γ` (i.e. `t_γ = γ` instead of Khanh's
  `e^{j(L+1)}f`). Then `a_i x_0 = ∑_γ ∑_{μ ∈ T_i γ} s_{μγ}`, and `(γ, μ) ↦ μγ` is injective
  because all `γ` have the same length (`List.append_inj'`), so no cancellation over `F_2`.
* Some `T_i γ` is nonempty since `a_i = ∑_γ (a_i s_γ) t_γ ≠ 0`.
* `x = x_0 e^M f`, `η_i = μ_i e^M f` for `μ_i ∈ supp P_i`; conclude by eq:word-separation.
-/

namespace GroupApproximation.Full.LVFrame

open scoped BigOperators

/-- `b x_0` is the positive polynomial on the concatenated words `μγ`. -/
theorem mul_sum_wordS_mul_wordS_eq_posPoly (D : ℕ)
    (b : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))
    (T : (Fin D → Fin 2) → Finset (List (Fin 2)))
    (hT : ∀ f, b * (BinaryLeavitt.family (ZMod 2)).wordS (List.ofFn f) = posPoly (T f)) :
    b * ∑ f : Fin D → Fin 2, (BinaryLeavitt.family (ZMod 2)).wordS (List.ofFn f) *
        (BinaryLeavitt.family (ZMod 2)).wordS (List.ofFn f) =
      posPoly (Finset.image
        (fun p : (Σ _ : Fin D → Fin 2, List (Fin 2)) => p.2 ++ List.ofFn p.1)
        (Finset.univ.sigma T)) := by
  have hinj : Set.InjOn
      (fun p : (Σ _ : Fin D → Fin 2, List (Fin 2)) => p.2 ++ List.ofFn p.1)
      (Finset.univ.sigma T : Set (Σ _ : Fin D → Fin 2, List (Fin 2))) := by
    intro p _ q _ hpq
    obtain ⟨f, μ⟩ := p
    obtain ⟨f', μ'⟩ := q
    have hpq' : μ ++ List.ofFn f = μ' ++ List.ofFn f' := hpq
    obtain ⟨h1, h2⟩ := List.append_inj' hpq' (by simp only [List.length_ofFn])
    obtain rfl := List.ofFn_injective h2
    obtain rfl := h1
    rfl
  calc
    b * ∑ f : Fin D → Fin 2, (BinaryLeavitt.family (ZMod 2)).wordS (List.ofFn f) *
        (BinaryLeavitt.family (ZMod 2)).wordS (List.ofFn f) =
        ∑ f : Fin D → Fin 2, b * (BinaryLeavitt.family (ZMod 2)).wordS (List.ofFn f) *
          (BinaryLeavitt.family (ZMod 2)).wordS (List.ofFn f) := by
      rw [Finset.mul_sum]
      simp only [mul_assoc]
    _ = ∑ f : Fin D → Fin 2, ∑ μ ∈ T f,
          (BinaryLeavitt.family (ZMod 2)).wordS (μ ++ List.ofFn f) := by
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [hT f]
      unfold posPoly
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [LeavittFamily.wordS_append]
    _ = ∑ p ∈ Finset.univ.sigma T, (BinaryLeavitt.family (ZMod 2)).wordS (p.2 ++ List.ofFn p.1) :=
      (Finset.sum_sigma Finset.univ T
        (fun p => (BinaryLeavitt.family (ZMod 2)).wordS (p.2 ++ List.ofFn p.1))).symm
    _ = posPoly (Finset.image
        (fun p : (Σ _ : Fin D → Fin 2, List (Fin 2)) => p.2 ++ List.ofFn p.1)
        (Finset.univ.sigma T)) := by
      unfold posPoly
      rw [Finset.sum_image hinj]

#audit_axioms GroupApproximation.Full.LVFrame.mul_sum_wordS_mul_wordS_eq_posPoly

/-- Some `b s_γ` (`|γ| = D`) has nonempty support when `b ≠ 0` (tex l.344). -/
theorem exists_mem_of_mul_wordS_eq_posPoly (D : ℕ)
    (b : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) (hb : b ≠ 0)
    (T : (Fin D → Fin 2) → Finset (List (Fin 2)))
    (hT : ∀ f, b * (BinaryLeavitt.family (ZMod 2)).wordS (List.ofFn f) = posPoly (T f)) :
    ∃ f, ∃ μ, μ ∈ T f := by
  by_contra hne
  apply hb
  rw [LeavittFamily.eq_sum_mul_wordS_mul_wordT (BinaryLeavitt.family (ZMod 2)) b D]
  refine Finset.sum_eq_zero fun f _ => ?_
  have hTf : T f = ∅ := Finset.eq_empty_of_forall_notMem fun μ hμ => hne ⟨f, μ, hμ⟩
  rw [hT f, hTf, posPoly_empty, zero_mul]

#audit_axioms GroupApproximation.Full.LVFrame.exists_mem_of_mul_wordS_eq_posPoly

/-- **Step `x_0`** (tex l.346): one right multiplier making every `a_i x_0` a nonempty positive
polynomial. -/
theorem exists_posPoly_right_multiplier {ι : Type*} [Fintype ι]
    (a : ι → BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) (ha : ∀ i, a i ≠ 0) :
    ∃ x0 : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2), ∃ P : ι → Finset (List (Fin 2)),
      ∀ i, a i * x0 = posPoly (P i) ∧ ∃ μ, μ ∈ P i := by
  choose N hN using fun i => exists_posPoly_mul_wordS (a i)
  have hlen : ∀ i (f : Fin (Finset.univ.sup N) → Fin 2), N i ≤ (List.ofFn f).length := by
    intro i f
    rw [List.length_ofFn]
    exact Finset.le_sup (Finset.mem_univ i)
  choose S hS using fun i (f : Fin (Finset.univ.sup N) → Fin 2) =>
    hN i (List.ofFn f) (hlen i f)
  refine ⟨∑ f : Fin (Finset.univ.sup N) → Fin 2,
      (BinaryLeavitt.family (ZMod 2)).wordS (List.ofFn f) *
        (BinaryLeavitt.family (ZMod 2)).wordS (List.ofFn f),
    fun i => Finset.image
      (fun p : (Σ _ : Fin (Finset.univ.sup N) → Fin 2, List (Fin 2)) => p.2 ++ List.ofFn p.1)
      (Finset.univ.sigma (S i)), fun i => ⟨?_, ?_⟩⟩
  · exact mul_sum_wordS_mul_wordS_eq_posPoly _ (a i) (S i) (hS i)
  · obtain ⟨f, μ, hμ⟩ := exists_mem_of_mul_wordS_eq_posPoly _ (a i) (ha i) (S i) (hS i)
    have hmem : (⟨f, μ⟩ : Σ _ : Fin (Finset.univ.sup N) → Fin 2, List (Fin 2)) ∈
        Finset.univ.sigma (S i) :=
      Finset.mem_sigma.mpr ⟨Finset.mem_univ f, hμ⟩
    exact ⟨μ ++ List.ofFn f, Finset.mem_image_of_mem
      (fun p : (Σ _ : Fin (Finset.univ.sup N) → Fin 2, List (Fin 2)) => p.2 ++ List.ofFn p.1)
      hmem⟩

#audit_axioms GroupApproximation.Full.LVFrame.exists_posPoly_right_multiplier

/-- **Lemma 4.1 (`lem:word-multiplier`), multiplier part**, for any finite index type. -/
theorem exists_word_multiplier_fintype {ι : Type*} [Fintype ι]
    (a : ι → BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) (ha : ∀ i, a i ≠ 0) :
    ∃ x : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2), ∃ η : ι → List (Fin 2),
      (∀ i, η i ≠ []) ∧
        ∀ i, (BinaryLeavitt.family (ZMod 2)).wordT (η i) * a i * x = 1 := by
  obtain ⟨x0, P, hP⟩ := exists_posPoly_right_multiplier a ha
  choose μ hμ using fun i => (hP i).2
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ i, ∀ ν ∈ P i, ν.length ≤ M :=
    ⟨Finset.univ.sup fun i => (P i).sup List.length, fun i ν hν =>
      le_trans (Finset.le_sup (f := List.length) hν)
        (Finset.le_sup (f := fun i => (P i).sup List.length) (Finset.mem_univ i))⟩
  refine ⟨x0 * (BinaryLeavitt.family (ZMod 2)).wordS (BinaryLeavitt.killWord M),
    fun i => μ i ++ BinaryLeavitt.killWord M, fun i => append_killWord_ne_nil (μ i) M,
    fun i => ?_⟩
  show (BinaryLeavitt.family (ZMod 2)).wordT (μ i ++ BinaryLeavitt.killWord M) * a i *
      (x0 * (BinaryLeavitt.family (ZMod 2)).wordS (BinaryLeavitt.killWord M)) = 1
  rw [mul_assoc, ← mul_assoc (a i) x0, (hP i).1]
  exact wordT_append_killWord_mul_posPoly M (P i) (hM i) (hμ i)

#audit_axioms GroupApproximation.Full.LVFrame.exists_word_multiplier_fintype

/-- **Lemma 4.1 (`lem:word-multiplier`)** in the lane's `Fin s` form; `η^* = wordT η`. -/
theorem exists_word_multiplier {s : ℕ} (a : Fin s → BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))
    (ha : ∀ i, a i ≠ 0) :
    ∃ x : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2), ∃ η : Fin s → List (Fin 2),
      (∀ i, η i ≠ []) ∧
        ∀ i, (BinaryLeavitt.family (ZMod 2)).wordT (η i) * a i * x = 1 :=
  exists_word_multiplier_fintype a ha

#audit_axioms GroupApproximation.Full.LVFrame.exists_word_multiplier

end GroupApproximation.Full.LVFrame
