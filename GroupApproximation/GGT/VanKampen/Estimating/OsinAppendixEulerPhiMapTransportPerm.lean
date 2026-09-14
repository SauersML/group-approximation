import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerRegionFaces
import GroupApproximation.Meta.AxiomGuard

/-!
# First returns through a detour past one point

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

A face-edge doubling changes the face rotation of the collapsed map at one dart `w`: where the old
rotation went to `w`, the new one goes to the new dart `s`, and from `s` it goes on to where the
old rotation went from `w`.  A first return to a retained set avoiding `w` does not see the change.
This module states that for permutations.

* `PhiMapTransport.pow_apply_bypass`, `isFirstReturn_bypass`: first returns through a detour past
  one point.
* `PhiMapTransport.pow_apply_of_semiconj`, `isFirstReturn_of_semiconj`: through a semiconjugacy.
* `PhiMapTransport.apply_equiv_of_isFirstReturn`: two first returns along embeddings with one image
  correspond through the identification of their retained types.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(a);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.PhiMapTransport

open Equiv PermFirstReturn

universe u v w

open scoped Classical in
/-- **Iterates through a detour past one point.** -/
theorem pow_apply_bypass {A : Type u} {B : Type v} {p : Perm A} {p' : Perm B} {ι : A ↪ B}
    {w : A} {s : B} (h0 : p w ≠ w)
    (h1 : ∀ x, x ≠ w → p x ≠ w → p' (ι x) = ι (p x))
    (h2 : ∀ x, x ≠ w → p x = w → p' (ι x) = s)
    (h3 : p' s = ι (p w)) (k : ℕ) (y : A) (hy : y ≠ w) :
    (p' ^ k) (ι y) = if (p ^ k) y = w then s else ι ((p ^ k) y) := by
  induction k with
  | zero => simp only [pow_zero, Perm.one_apply, if_neg hy]
  | succ k ih =>
    have hp' : (p' ^ (k + 1)) (ι y) = p' ((p' ^ k) (ι y)) := by rw [pow_succ', Perm.mul_apply]
    have hp : (p ^ (k + 1)) y = p ((p ^ k) y) := by rw [pow_succ', Perm.mul_apply]
    rw [hp', ih, hp]
    by_cases hz : (p ^ k) y = w
    · rw [if_pos hz, h3, hz, if_neg h0]
    · rw [if_neg hz]
      by_cases hpz : p ((p ^ k) y) = w
      · rw [if_pos hpz]
        exact h2 _ hz hpz
      · rw [if_neg hpz]
        exact h1 _ hz hpz

/-- **A first return through a detour past one point.**  If `p'` follows `p` along `ι`, except
that it detours through `s` in place of `w`, a first return of `p` to a retained set avoiding `w` is
also a first return of `p'`. -/
theorem isFirstReturn_bypass {A : Type u} {B : Type v} {C : Type w} {p : Perm A} {p' : Perm B}
    {ι : A ↪ B} {w : A} {s : B} (hs : s ∉ Set.range ι) (h0 : p w ≠ w)
    (h1 : ∀ x, x ≠ w → p x ≠ w → p' (ι x) = ι (p x))
    (h2 : ∀ x, x ≠ w → p x = w → p' (ι x) = s)
    (h3 : p' s = ι (p w)) {q : Perm C} {e : C ↪ A} (hw : w ∉ Set.range e)
    (hq : IsFirstReturn p q e) : IsFirstReturn p' q (e.trans ι) := by
  classical
  intro c
  have hc : e c ≠ w := fun h => hw ⟨c, h⟩
  obtain ⟨m, hm, hpm, hskip⟩ := hq c
  refine ⟨m, hm, ?_, fun k hk hkm hmem => ?_⟩
  · simp only [Function.Embedding.trans_apply]
    rw [pow_apply_bypass h0 h1 h2 h3 m (e c) hc, hpm, if_neg (fun h => hw ⟨q c, h⟩)]
  · obtain ⟨c', hc'⟩ := hmem
    simp only [Function.Embedding.trans_apply] at hc'
    rw [pow_apply_bypass h0 h1 h2 h3 k (e c) hc] at hc'
    by_cases hz : (p ^ k) (e c) = w
    · rw [if_pos hz] at hc'
      exact hs ⟨e c', hc'⟩
    · rw [if_neg hz] at hc'
      exact hskip k hk hkm ⟨c', ι.injective hc'⟩

/-- **Iterates through a semiconjugacy.** -/
theorem pow_apply_of_semiconj {A : Type u} {B : Type v} {p : Perm A} {p' : Perm B} {ι : A ↪ B}
    (h : ∀ x, p' (ι x) = ι (p x)) (k : ℕ) (y : A) : (p' ^ k) (ι y) = ι ((p ^ k) y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ih, h, pow_succ', Perm.mul_apply]

/-- **A first return through a semiconjugacy.** -/
theorem isFirstReturn_of_semiconj {A : Type u} {B : Type v} {C : Type w} {p : Perm A}
    {p' : Perm B} {ι : A ↪ B} (h : ∀ x, p' (ι x) = ι (p x)) {q : Perm C} {e : C ↪ A}
    (hq : IsFirstReturn p q e) : IsFirstReturn p' q (e.trans ι) := by
  intro c
  obtain ⟨m, hm, hpm, hskip⟩ := hq c
  refine ⟨m, hm, ?_, fun k hk hkm hmem => ?_⟩
  · simp only [Function.Embedding.trans_apply]
    rw [pow_apply_of_semiconj h, hpm]
  · obtain ⟨c', hc'⟩ := hmem
    simp only [Function.Embedding.trans_apply] at hc'
    rw [pow_apply_of_semiconj h] at hc'
    exact hskip k hk hkm ⟨c', ι.injective hc'⟩

/-- **First returns along two embeddings with one image correspond.** -/
theorem apply_equiv_of_isFirstReturn {A : Type u} {C : Type v} {C' : Type w} {p : Perm A}
    {q : Perm C} {q' : Perm C'} {e : C ↪ A} {e' : C' ↪ A} (φ : C ≃ C')
    (hφ : ∀ c, e' (φ c) = e c) (hq : IsFirstReturn p q e) (hq' : IsFirstReturn p q' e')
    (c : C) : q' (φ c) = φ (q c) := by
  obtain ⟨m, hm, hpm, hskip⟩ := hq c
  have hrun : (p ^ m) (e' (φ c)) = e' (φ (q c)) := by rw [hφ, hφ]; exact hpm
  refine PermFirstReturn.apply_eq_of_isFirstReturn hq' hm hrun fun k hk hkm hmem => ?_
  obtain ⟨c'', hc''⟩ := hmem
  rw [hφ] at hc''
  have h1 : e (φ.symm c'') = e' c'' := by rw [← hφ, Equiv.apply_symm_apply]
  exact hskip k hk hkm ⟨φ.symm c'', h1.trans hc''⟩

end GroupApproximation.GGT.VanKampen.PhiMapTransport

#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.isFirstReturn_bypass
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.isFirstReturn_of_semiconj
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.apply_equiv_of_isFirstReturn
