import GroupApproximation.Higman.RelatorEnumeration

/-!
# Relabelling generators, and images of relator sets

Assembling a presentation of a construction out of presentations of its parts
always relabels: the free product puts two generating sets side by side, the
HNN extension adds a stable letter, and both then have to be re-indexed by `ℕ`
so that `Higman.RelatorRE` applies.  Each relabelling moves the relator set by
`FreeGroup.map`, and the question each time is whether enumerability survives.

It does, and the reason is worth stating once: membership in `FreeGroup.map σ ''
S` is *not* decided by inverting `σ`; it is witnessed.  A witness is a raw word
`u` with `freeEval u ∈ S` together with a deletion certificate for
`relabel σ u ++ invRaw v`, and both components are `Primcodable`.  So the image
of an enumerable set under a computable relabelling is enumerable, with no
injectivity hypothesis on `σ` at all.
-/

namespace GroupApproximation
namespace Higman

/-! ## 1.  Relabelling raw words -/

/-- Relabel the letters of a raw word. -/
def relabel (σ : ℕ → ℕ) (w : RawWord) : RawWord := w.map fun p ↦ (σ p.1, p.2)

@[simp] theorem relabel_nil (σ : ℕ → ℕ) : relabel σ [] = [] := rfl

theorem evalRaw_relabel {A : Type} [Group A] (x : ℕ → A) (σ : ℕ → ℕ)
    (w : RawWord) : evalRaw x (relabel σ w) = evalRaw (fun k ↦ x (σ k)) w := by
  induction w with
  | nil => simp [relabel]
  | cons p w ih =>
      obtain ⟨i, b⟩ := p
      show evalRaw x ((σ i, b) :: relabel σ w) = _
      rw [evalRaw_cons, evalRaw_cons, ih]

theorem freeEval_relabel (σ : ℕ → ℕ) (w : RawWord) :
    freeEval (relabel σ w) = FreeGroup.map σ (freeEval w) := by
  unfold freeEval
  rw [evalRaw_relabel, map_evalRaw]
  rfl

theorem primrec_relabel {σ : ℕ → ℕ} (hσ : Primrec σ) : Primrec (relabel σ) := by
  refine (Primrec.list_map Primrec.id ?_).of_eq fun _ ↦ rfl
  exact (Primrec.pair (hσ.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)).to₂

/-! ## 2.  Images of enumerable relator sets -/

/-- **The image of an enumerable relator set under a computable relabelling is
enumerable.**  No injectivity is needed: membership is witnessed by a preimage
word together with a deletion certificate. -/
theorem search_image {σ : ℕ → ℕ} (hσ : Primrec σ) {S : Set (FreeGroup ℕ)}
    {fS : RawWord → ℕ → Bool} (hS : Primrec₂ fS)
    (hspec : ∀ v : RawWord, freeEval v ∈ S ↔ ∃ n, fS v n = true) :
    ∃ f : RawWord → (RawWord × ℕ × List ℕ) → Bool, Primrec₂ f ∧
      ∀ v : RawWord,
        freeEval v ∈ (FreeGroup.map σ) '' S ↔ ∃ c, f v c = true := by
  refine ⟨fun v c ↦
      fS c.1 c.2.1 &&
        decide (Computability.applySteps (relabel σ c.1 ++ invRaw v) c.2.2
          = some []), ?_, ?_⟩
  · refine Primrec.and.comp ?_ ?_
    · exact hS.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    · refine (Primrec.eq.comp ?_ (Primrec.const (some []))).decide
      refine Computability.primrec_applySteps.comp ?_
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      exact Primrec.list_append.comp
        ((primrec_relabel hσ).comp (Primrec.fst.comp Primrec.snd))
        (primrec_invRaw.comp Primrec.fst)
  · intro v
    constructor
    · rintro ⟨x, hxS, hx⟩
      obtain ⟨u, rfl⟩ :=
        (mem_closure_iff_exists_evalRaw FreeGroup.of x).1
          (by rw [FreeGroup.closure_range_of]; exact Subgroup.mem_top x)
      obtain ⟨n, hn⟩ := (hspec u).1 hxS
      have hzero : freeEval (relabel σ u ++ invRaw v) = 1 := by
        unfold freeEval
        rw [evalRaw_append, evalRaw_invRaw]
        show freeEval (relabel σ u) * (freeEval v)⁻¹ = 1
        rw [mul_inv_eq_one, freeEval_relabel]
        exact hx
      obtain ⟨is, his⟩ := (freeEval_eq_one_iff _).1 hzero
      exact ⟨(u, n, is), by simp [hn, his]⟩
    · rintro ⟨⟨u, n, is⟩, hc⟩
      rw [Bool.and_eq_true_iff] at hc
      refine ⟨freeEval u, (hspec u).2 ⟨n, hc.1⟩, ?_⟩
      have hzero : freeEval (relabel σ u ++ invRaw v) = 1 :=
        (freeEval_eq_one_iff _).2 ⟨is, by simpa using hc.2⟩
      unfold freeEval at hzero
      rw [evalRaw_append, evalRaw_invRaw, mul_inv_eq_one] at hzero
      rw [← freeEval_relabel]
      exact hzero

end Higman
end GroupApproximation
