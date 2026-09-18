import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVStatement
import Mathlib.Algebra.Group.End
import Mathlib.SetTheory.Cardinal.NatCard
import GroupApproximation.Meta.AxiomGuard

/-!
# Higman's theorem depends only on the number of letters

A bijection of alphabets `e : X ≃ Y` acts letterwise on streams (`cantorCongr e`).  Conjugating
by this map carries `higmanThompsonV X` isomorphically onto `higmanThompsonV Y`
(`higmanVCongr`).  So `HigmanVFPStatement` reduces to the alphabets `Fin d` with `d ≥ 2`
(`higmanVFP_of_fin`).

Route.
* `prepend_map`: the letterwise map sends `w x` to `(e w)(e x)`.
* `permCongr_mem_higmanThompsonV`: if `f` carries the depth-`N` cone of `e⁻¹ u` onto the cone of
  `v`, then its conjugate carries the cone of `u` onto the cone of `e v`.  So the conjugate has
  depth `N` as well.
* `higmanVCongr`: the conjugation restricted to the two subgroups, as a `MulEquiv`.
* `higmanVFP_of_fin`: transport along `Finite.equivFin X : X ≃ Fin (Nat.card X)`.

*Why the isolated statement is strictly smaller.*  `HigmanVFinFPStatement` is the special case
`X = Fin d` of `HigmanVFPStatement`.  The reduction discharges the alphabet transport.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X Y : Type*}

/-- The letterwise action of a bijection of alphabets on streams. -/
def cantorCongr (e : X ≃ Y) : Cantor X ≃ Cantor Y where
  toFun x n := e (x n)
  invFun y n := e.symm (y n)
  left_inv x := funext fun n ↦ e.symm_apply_apply (x n)
  right_inv y := funext fun n ↦ e.apply_symm_apply (y n)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.cantorCongr

@[simp] theorem cantorCongr_apply (e : X ≃ Y) (x : Cantor X) (n : ℕ) :
    cantorCongr e x n = e (x n) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.cantorCongr_apply

theorem cantorCongr_symm (e : X ≃ Y) : (cantorCongr e).symm = cantorCongr e.symm :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.cantorCongr_symm

theorem cantorCongr_apply_symm_apply (e : X ≃ Y) (y : Cantor Y) :
    cantorCongr e (cantorCongr e.symm y) = y :=
  (cantorCongr e).apply_symm_apply y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.cantorCongr_apply_symm_apply

/-- The letterwise map sends the stream `w x` to the stream `(e w)(e x)`. -/
theorem prepend_map (e : X ≃ Y) (w : List X) (x : Cantor X) :
    prepend (w.map e) (cantorCongr e x) = cantorCongr e (prepend w x) := by
  funext n
  rw [cantorCongr_apply]
  by_cases hn : n < w.length
  · have hn' : n < (w.map e).length := by
      rw [List.length_map]
      exact hn
    rw [prepend_getElem _ _ hn', prepend_getElem _ _ hn, List.getElem_map]
  · have hn' : ¬ n < (w.map e).length := by
      rw [List.length_map]
      exact hn
    rw [prepend_of_length_le _ _ hn', prepend_of_length_le _ _ hn, cantorCongr_apply,
      List.length_map]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.prepend_map

/-- Conjugating by a bijection of alphabets preserves the Higman–Thompson group. -/
theorem permCongr_mem_higmanThompsonV [Finite X] [Finite Y] (e : X ≃ Y)
    {f : Equiv.Perm (Cantor X)} (hf : f ∈ higmanThompsonV X) :
    (cantorCongr e).permCongr f ∈ higmanThompsonV Y := by
  obtain ⟨N, hN⟩ := mem_higmanThompsonV.mp hf
  refine mem_higmanThompsonV.mpr ⟨N, ?_⟩
  intro u hu
  obtain ⟨v, hv⟩ := hN (u.map e.symm) (by rw [List.length_map, hu])
  refine ⟨v.map e, ?_⟩
  intro y
  rw [Equiv.permCongr_apply, cantorCongr_symm, ← prepend_map e.symm u y,
    hv (cantorCongr e.symm y), ← prepend_map e v (cantorCongr e.symm y),
    cantorCongr_apply_symm_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.permCongr_mem_higmanThompsonV

/-- **Alphabet transport.**  A bijection of alphabets induces an isomorphism of Higman–Thompson
groups. -/
def higmanVCongr [Finite X] [Finite Y] (e : X ≃ Y) :
    ↥(higmanThompsonV X) ≃* ↥(higmanThompsonV Y) where
  toFun f := ⟨(cantorCongr e).permCongr f, permCongr_mem_higmanThompsonV e f.2⟩
  invFun g := ⟨(cantorCongr e).permCongr.symm g, by
    rw [Equiv.permCongr_symm, cantorCongr_symm]
    exact permCongr_mem_higmanThompsonV e.symm g.2⟩
  left_inv f :=
    Subtype.ext ((cantorCongr e).permCongr.symm_apply_apply (f : Equiv.Perm (Cantor X)))
  right_inv g :=
    Subtype.ext ((cantorCongr e).permCongr.apply_symm_apply (g : Equiv.Perm (Cantor Y)))
  map_mul' f g := Subtype.ext ((cantorCongr e).permCongr_mul f g)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCongr

/-- **Higman's theorem over the alphabets `Fin d`.**  For every `d ≥ 2`, the Higman–Thompson
group `higmanThompsonV (Fin d)` is finitely presented. -/
def HigmanVFinFPStatement : Prop :=
  ∀ d : ℕ, 1 < d → Group.IsFinitelyPresented ↥(higmanThompsonV (Fin d))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVFinFPStatement

/-- Higman's theorem over `Fin d` gives it over every finite nontrivial alphabet. -/
theorem higmanVFP_of_fin (h : HigmanVFinFPStatement) : HigmanVFPStatement := by
  intro X _ _
  haveI := h (Nat.card X) Finite.one_lt_card
  exact Group.IsFinitelyPresented.equiv (higmanVCongr (Finite.equivFin X).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_of_fin

end GroupApproximation.BooneHigman.Metabelian.Envelope
