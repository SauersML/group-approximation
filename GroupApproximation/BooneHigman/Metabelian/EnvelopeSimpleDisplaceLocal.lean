import GroupApproximation.BooneHigman.Metabelian.EnvelopeRN
import GroupApproximation.Meta.AxiomGuard

/-!
# Locally determined maps of the Cantor set

A map `f : Cantor X → Cantor X` is *locally determined* when each finite initial segment of
`f x` depends only on a finite initial segment of `x` (continuity for the product topology,
spelled without topology).

* `StreamAgree M x y`: `x` and `y` have the same first `M` letters; equivalently
  `firstWord M x = firstWord M y`.
* `LocallyDetermined.comp`, `locallyDetermined_id`: closure under composition.
* Generators of `V_X(H)` are locally determined: permutations with a depth
  (`locallyDetermined_of_hasDepth`, a prefix substitution on every depth-`D` cone), tree
  automorphisms (`locallyDetermined_cantorHom`, via `firstWord_streamFun`), and localizations
  of locally determined permutations (`locallyDetermined_localize`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

variable {X : Type*}

/-- Two streams with the same first `M` letters. -/
def StreamAgree (M : ℕ) (x y : Cantor X) : Prop :=
  ∀ k < M, x k = y k

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.StreamAgree

theorem StreamAgree.symm {M : ℕ} {x y : Cantor X} (h : StreamAgree M x y) :
    StreamAgree M y x := by
  intro k hk
  exact (h k hk).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.StreamAgree.symm

theorem StreamAgree.mono {M N : ℕ} {x y : Cantor X} (h : StreamAgree M x y) (hNM : N ≤ M) :
    StreamAgree N x y := by
  intro k hk
  exact h k (lt_of_lt_of_le hk hNM)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.StreamAgree.mono

theorem firstWord_eq_of_streamAgree {M : ℕ} {x y : Cantor X} (h : StreamAgree M x y) :
    firstWord M x = firstWord M y := by
  unfold firstWord
  exact congrArg List.ofFn (funext fun i : Fin M => h i i.2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.firstWord_eq_of_streamAgree

theorem streamAgree_of_firstWord_eq {M : ℕ} {x y : Cantor X} (h : firstWord M x = firstWord M y) :
    StreamAgree M x y := by
  intro k hk
  have hk' : k < (firstWord M x).length := by
    rw [length_firstWord]
    exact hk
  have hy := isStreamPrefix_firstWord M y
  rw [← h] at hy
  exact (isStreamPrefix_firstWord M x k hk').trans (hy k hk').symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.streamAgree_of_firstWord_eq

theorem streamAgree_of_mem_cone_firstWord {L : ℕ} {x y : Cantor X}
    (hy : y ∈ cone (firstWord L x)) : StreamAgree L x y := by
  intro k hk
  have hk' : k < (firstWord L x).length := by
    rw [length_firstWord]
    exact hk
  exact (isStreamPrefix_firstWord L x k hk').trans ((mem_cone.mp hy) k hk').symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.streamAgree_of_mem_cone_firstWord

theorem isStreamPrefix_of_streamAgree {M : ℕ} {w : List X} {x y : Cantor X}
    (h : StreamAgree M x y) (hM : w.length ≤ M) (hx : IsStreamPrefix w x) :
    IsStreamPrefix w y := by
  intro k hk
  exact (h k (lt_of_lt_of_le hk hM)).symm.trans (hx k hk)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.isStreamPrefix_of_streamAgree

theorem streamAgree_prepend {N : ℕ} {x y : Cantor X} (h : StreamAgree N x y) (w : List X) :
    StreamAgree N (prepend w x) (prepend w y) := by
  intro k hk
  by_cases hkw : k < w.length
  · rw [prepend_getElem _ _ hkw, prepend_getElem _ _ hkw]
  · rw [prepend_of_length_le _ _ hkw, prepend_of_length_le _ _ hkw]
    exact h _ (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.streamAgree_prepend

/-- Every initial segment of `f x` is determined by an initial segment of `x`. -/
def LocallyDetermined (f : Cantor X → Cantor X) : Prop :=
  ∀ (x : Cantor X) (N : ℕ), ∃ M : ℕ, ∀ y : Cantor X,
    StreamAgree M x y → StreamAgree N (f x) (f y)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.LocallyDetermined

theorem locallyDetermined_id : LocallyDetermined (id : Cantor X → Cantor X) := by
  intro _ N
  exact ⟨N, fun _ hy => hy⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.locallyDetermined_id

theorem LocallyDetermined.comp {f g : Cantor X → Cantor X} (hf : LocallyDetermined f)
    (hg : LocallyDetermined g) : LocallyDetermined (f ∘ g) := by
  intro x N
  obtain ⟨M₁, h₁⟩ := hf (g x) N
  obtain ⟨M₂, h₂⟩ := hg x M₁
  exact ⟨M₂, fun y hy => h₁ (g y) (h₂ y hy)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.LocallyDetermined.comp

/-- A prefix substitution on every depth-`D` cone is locally determined. -/
theorem locallyDetermined_of_hasDepth {f : Equiv.Perm (Cantor X)} {D : ℕ} (hf : HasDepth f D) :
    LocallyDetermined ⇑f := by
  intro x N
  refine ⟨D + N, fun y hy => ?_⟩
  obtain ⟨v, hv⟩ := hf (firstWord D x) (length_firstWord D x)
  have hL : (firstWord D x).length = D := length_firstWord D x
  have hx : IsStreamPrefix (firstWord D x) x := isStreamPrefix_firstWord D x
  have hy' : IsStreamPrefix (firstWord D x) y := isStreamPrefix_of_streamAgree hy (by omega) hx
  have ex : f x = prepend v (dropN (firstWord D x).length x) := by
    rw [← hv (dropN (firstWord D x).length x), prepend_dropN_of_isStreamPrefix _ x hx]
  have ey : f y = prepend v (dropN (firstWord D x).length y) := by
    rw [← hv (dropN (firstWord D x).length y), prepend_dropN_of_isStreamPrefix _ y hy']
  intro k hkN
  by_cases hk : k < v.length
  · rw [ex, ey, prepend_getElem _ _ hk, prepend_getElem _ _ hk]
  · rw [ex, ey, prepend_of_length_le _ _ hk, prepend_of_length_le _ _ hk]
    exact hy _ (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.locallyDetermined_of_hasDepth

/-- Tree automorphisms act letter by letter, hence are locally determined. -/
theorem locallyDetermined_cantorHom (g : TreeAut X) : LocallyDetermined ⇑(cantorHom g) := by
  intro x N
  refine ⟨N, fun y hy => streamAgree_of_firstWord_eq ?_⟩
  rw [cantorHom_apply, cantorHom_apply, firstWord_streamFun, firstWord_streamFun,
    firstWord_eq_of_streamAgree hy]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.locallyDetermined_cantorHom

/-- Localizing a locally determined permutation inside a cone keeps it locally determined. -/
theorem locallyDetermined_localize {σ : Equiv.Perm (Cantor X)} (hσ : LocallyDetermined ⇑σ)
    (w : List X) : LocallyDetermined ⇑(localize w σ) := by
  intro x N
  by_cases hx : IsStreamPrefix w x
  · obtain ⟨z, rfl⟩ := mem_cone_iff.mp hx
    obtain ⟨M, hM⟩ := hσ z N
    refine ⟨w.length + M, fun y hy => ?_⟩
    have hwy : IsStreamPrefix w y := isStreamPrefix_of_streamAgree hy (by omega) hx
    obtain ⟨z', rfl⟩ := mem_cone_iff.mp hwy
    have hzz : StreamAgree M z z' := by
      intro k hk
      have h1 := hy (k + w.length) (by omega)
      have hkL : ¬ k + w.length < w.length := by omega
      rwa [prepend_of_length_le _ _ hkL, prepend_of_length_le _ _ hkL, Nat.add_sub_cancel] at h1
    rw [localize_apply_prepend, localize_apply_prepend]
    exact streamAgree_prepend (hM z' hzz) w
  · refine ⟨w.length + N, fun y hy => ?_⟩
    have hy' : ¬ IsStreamPrefix w y := fun h =>
      hx (isStreamPrefix_of_streamAgree hy.symm (by omega) h)
    rw [localize_apply_of_not hx, localize_apply_of_not hy']
    exact hy.mono (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.locallyDetermined_localize

end GroupApproximation.BooneHigman.Metabelian.Envelope
