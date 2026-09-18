import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.FinRange

/-!
# Folding lists of operations that commute on an invariant set

Combinatorial input for the forward direction of Kharlampovich--Myasnikov--Sapir
(arXiv:1204.6506) Theorem `tmm`(b), used for `thm:fixed-radical-membership` of
`non_mf_group_notes.tex`.  A configuration word
`x_{q_i A_0} * a_1^{(m_1)} * ⋯ * a_K^{(m_K)} * A_1 * ⋯ * A_K` is a left fold of operations
over `List.finRange K`.  One machine step changes one operation of the fold, and on the
abelian subgroup `T` of the source it can be pulled out of the fold (`opFold_extract`).
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Forward

variable {α ι : Type*}

/-- Apply the operations `G k`, `k ∈ L`, in the order of `L`. -/
def opFold (G : ι → α → α) (L : List ι) (f : α) : α :=
  List.foldl (fun h k ↦ G k h) f L

theorem opFold_nil (G : ι → α → α) (f : α) : opFold G [] f = f := rfl

theorem opFold_cons (G : ι → α → α) (a : ι) (L : List ι) (f : α) :
    opFold G (a :: L) f = opFold G L (G a f) := rfl

variable {T : Set α}

theorem iterate_mem {F : α → α} (hF : ∀ f ∈ T, F f ∈ T) :
    ∀ (m : ℕ), ∀ f ∈ T, F^[m] f ∈ T := by
  intro m
  induction m with
  | zero => exact fun f hf ↦ hf
  | succ m ih =>
    intro f hf
    rw [Function.iterate_succ_apply']
    exact hF _ (ih f hf)

theorem iterate_comm {F H : α → α} (hF : ∀ f ∈ T, F f ∈ T)
    (hFH : ∀ f ∈ T, F (H f) = H (F f)) : ∀ (m : ℕ), ∀ f ∈ T, F^[m] (H f) = H (F^[m] f) := by
  intro m
  induction m with
  | zero => exact fun _ _ ↦ rfl
  | succ m ih =>
    intro f hf
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih f hf,
      hFH _ (iterate_mem hF m f hf)]

theorem opFold_mem {G : ι → α → α} :
    ∀ (L : List ι), (∀ k ∈ L, ∀ f ∈ T, G k f ∈ T) → ∀ f ∈ T, opFold G L f ∈ T := by
  intro L
  induction L with
  | nil => exact fun _ f hf ↦ hf
  | cons a L ih =>
    intro hG f hf
    rw [opFold_cons]
    exact ih (fun k hk ↦ hG k (List.mem_cons.mpr (Or.inr hk)))
      (G a f) (hG a (List.mem_cons.mpr (Or.inl rfl)) f hf)

theorem opFold_comm {G : ι → α → α} {H : α → α} :
    ∀ (L : List ι), (∀ k ∈ L, ∀ f ∈ T, G k f ∈ T) →
      (∀ k ∈ L, ∀ f ∈ T, G k (H f) = H (G k f)) →
      ∀ f ∈ T, opFold G L (H f) = H (opFold G L f) := by
  intro L
  induction L with
  | nil => exact fun _ _ _ _ ↦ rfl
  | cons a L ih =>
    intro hG hH f hf
    have ha : a ∈ a :: L := List.mem_cons.mpr (Or.inl rfl)
    rw [opFold_cons, opFold_cons, hH a ha f hf]
    exact ih (fun k hk ↦ hG k (List.mem_cons.mpr (Or.inr hk)))
      (fun k hk ↦ hH k (List.mem_cons.mpr (Or.inr hk))) (G a f) (hG a ha f hf)

theorem opFold_congr {G G' : ι → α → α} :
    ∀ (L : List ι), (∀ k ∈ L, ∀ f, G k f = G' k f) → ∀ f, opFold G L f = opFold G' L f := by
  intro L
  induction L with
  | nil => exact fun _ _ ↦ rfl
  | cons a L ih =>
    intro hGG' f
    rw [opFold_cons, opFold_cons, hGG' a (List.mem_cons.mpr (Or.inl rfl)) f]
    exact ih (fun k hk ↦ hGG' k (List.mem_cons.mpr (Or.inr hk))) (G' a f)

/-- Pulling one changed operation out of a fold.  If the folds `G` and `G'` agree away from
the index `n`, and `G n = H ∘ G' n` on `T`, with `H` commuting with every `G' k` on `T`, then
`opFold G L = H ∘ opFold G' L` on `T`. -/
theorem opFold_extract {G G' : ι → α → α} {H : α → α} {n : ι} :
    ∀ (L : List ι), n ∈ L → L.Nodup →
      (∀ k ∈ L, k ≠ n → ∀ f, G k f = G' k f) →
      (∀ f ∈ T, G n f = H (G' n f)) →
      (∀ k ∈ L, ∀ f ∈ T, G' k f ∈ T) →
      (∀ k ∈ L, ∀ f ∈ T, G' k (H f) = H (G' k f)) →
      ∀ f ∈ T, opFold G L f = H (opFold G' L f) := by
  intro L
  induction L with
  | nil =>
    intro hnL
    simp at hnL
  | cons a L ih =>
    intro hnL hnd hsame hn hG' hH f hf
    have ha : a ∈ a :: L := List.mem_cons.mpr (Or.inl rfl)
    have hsub : ∀ k, k ∈ L → k ∈ a :: L := fun k hk ↦ List.mem_cons.mpr (Or.inr hk)
    rw [opFold_cons, opFold_cons]
    by_cases han : a = n
    · have hnotin : n ∉ L := by
        rw [← han]
        exact (List.nodup_cons.mp hnd).1
      have hne : ∀ k, k ∈ L → k ≠ n := by
        intro k hk hkn
        apply hnotin
        rw [← hkn]
        exact hk
      rw [han, hn f hf, opFold_congr L (fun k hk ↦ hsame k (hsub k hk) (hne k hk))]
      exact opFold_comm L (fun k hk ↦ hG' k (hsub k hk)) (fun k hk ↦ hH k (hsub k hk))
        (G' n f) (hG' n hnL f hf)
    · have hnL' : n ∈ L := by
        rcases List.mem_cons.mp hnL with h | h
        · exact absurd h.symm han
        · exact h
      rw [hsame a ha han f]
      exact ih hnL' (List.nodup_cons.mp hnd).2 (fun k hk ↦ hsame k (hsub k hk)) hn
        (fun k hk ↦ hG' k (hsub k hk)) (fun k hk ↦ hH k (hsub k hk)) (G' a f)
        (hG' a ha f hf)

end Forward

end KMS

end GroupApproximation.Full.Kharlampovich
