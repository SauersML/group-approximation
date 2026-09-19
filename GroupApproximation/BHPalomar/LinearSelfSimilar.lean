import Mathlib.Logic.Equiv.List
import GroupApproximation.BooneHigman.Products.Hosts
import GroupApproximation.BooneHigmanLinear.FrontierFour
import GroupApproximation.Meta.AxiomGuard

/-!
# LISW Question 1.11 from route A

Llosa Isenrich–Schesler–Wu (arXiv:2510.01952v1, Question 1.11) ask whether every finitely generated
linear group embeds in a finitely generated self-similar group.  Route A's linear host
(`GroupApproximation.BooneHigmanLinear.linearHost_routeA`) gives an embedding of every finitely
generated subgroup of `GL_n(K)`, for any field `K`, in a finitely presented self-similar subgroup
of `Aut(T_X)` for a finite alphabet `X`.  This file transports that embedding to the vocabulary of
the Palomar challenge, where a self-similar group is a subgroup of `Equiv.Perm (List (Fin d))`:

* `wordConj e`: conjugation by the bijection of words `List X ≃ List Y` that `e : X ≃ Y` induces,
  as an injective homomorphism `Aut(T_X) →* Equiv.Perm (List Y)`;
* `palomar_of_embedsInFPSelfSimilarGroup`: a group that embeds in a finitely presented self-similar
  subgroup of `Aut(T_X)` embeds in a finitely presented subgroup of `Equiv.Perm (List (Fin d))`
  that is self-similar in the challenge's sense;
* `linearSelfSimilar_routeA`: Question 1.11, in the challenge's statement, from `S1`, `P1` and `Z1`
  (route A without the Higman–`V` input `H1`).

`PalomarIsSelfSimilar` repeats the challenge's `IsSelfSimilar` body verbatim, so the Palomar
Solution can close its statement by `exact`.

This module is deliberately not imported by the root.  The Palomar Solution imports it directly.
-/

namespace GroupApproximation
namespace BHPalomar
namespace LinearSelfSimilar

open GroupApproximation.BooneHigman
open GroupApproximation.BooneHigman.Trees

/-- The challenge's self-similarity predicate (`Palomar/BooneHigmanChallenge.lean`, verbatim body):
each element preserves lengths, and for every element `g` and vertex `v` there is `h` in `S` with
`g (v ++ w) = g v ++ h w` for all `w`. -/
def PalomarIsSelfSimilar {d : ℕ} (S : Subgroup (Equiv.Perm (List (Fin d)))) : Prop :=
  ∀ g ∈ S, (∀ v : List (Fin d), (g v).length = v.length) ∧
    ∀ v : List (Fin d), ∃ h ∈ S, ∀ w : List (Fin d), g (v ++ w) = g v ++ h w

variable {X Y : Type}

/-- Conjugation of tree automorphisms by the bijection of words induced by `e : X ≃ Y`. -/
def wordConj (e : X ≃ Y) : TreeAut X →* Equiv.Perm (List Y) where
  toFun g := (Equiv.listEquivOfEquiv e).permCongr (g : Equiv.Perm (List X))
  map_one' := by
    ext w
    simp [Equiv.permCongr_apply]
  map_mul' g h := by
    ext w
    simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply]

theorem wordConj_apply (e : X ≃ Y) (g : TreeAut X) (w : List Y) :
    wordConj e g w = List.map e (g • List.map e.symm w) := rfl

theorem wordConj_injective (e : X ≃ Y) : Function.Injective (wordConj e) := by
  intro a b hab
  apply Subtype.ext
  apply (Equiv.listEquivOfEquiv e).permCongr.injective
  exact hab

/-- **Transport to the challenge's vocabulary.**  A group that embeds in a finitely presented
self-similar subgroup of `Aut(T_X)` embeds in a finitely presented subgroup of
`Equiv.Perm (List (Fin d))` that is self-similar in the challenge's sense, with `d = |X|`. -/
theorem palomar_of_embedsInFPSelfSimilarGroup {G : Type*} [Group G]
    (hG : Products.EmbedsInFPSelfSimilarGroup G) :
    ∃ (d : ℕ) (S : Subgroup (Equiv.Perm (List (Fin d)))), PalomarIsSelfSimilar S ∧
      Group.IsFinitelyPresented S ∧ ∃ f : G →* S, Function.Injective f := by
  obtain ⟨X, hX, _, H, hH, hHfp, f, hf⟩ := hG
  haveI := hX
  haveI := hHfp
  let e : X ≃ Fin (Nat.card X) := Finite.equivFin X
  let ψ : TreeAut X →* Equiv.Perm (List (Fin (Nat.card X))) := wordConj e
  have hψ : Function.Injective ψ := wordConj_injective e
  let iso : H ≃* H.map ψ := H.equivMapOfInjective ψ hψ
  haveI : Group.IsFinitelyPresented (H.map ψ) := Group.IsFinitelyPresented.equiv iso
  refine ⟨Nat.card X, H.map ψ, ?_, inferInstance, iso.toMonoidHom.comp f,
    iso.injective.comp hf⟩
  intro g' hg'
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
  refine ⟨fun v => ?_, fun v => ⟨ψ (TreeAut.state g (List.map e.symm v)),
    Subgroup.mem_map_of_mem ψ (hH.state_mem hg _), fun w => ?_⟩⟩
  · simp only [ψ, wordConj_apply, List.length_map, TreeAut.length_smul]
  · simp only [ψ, wordConj_apply, List.map_append, TreeAut.smul_append]

/-- **LISW Question 1.11 from route A without `H1`.**  Every finitely generated linear group, over
any field, embeds in a finitely presented self-similar group, in the challenge's statement, from
Suslin absorption at bad primes (`S1`) and the two `K₂` gaps (`P1`, `Z1`). -/
theorem linearSelfSimilar_routeA (hS1 : Metabelian.Absorption.suslinZLocal_BadStatement)
    (hP1 : ∀ p : ℕ, p.Prime → Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4)
    (hZ1 : Metabelian.ElemFPCharZero.CharZeroK2SplitGapStatement) :
    ∀ (K : Type) [Field K] (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)),
      H.FG →
      ∃ (d : ℕ) (S : Subgroup (Equiv.Perm (List (Fin d)))), PalomarIsSelfSimilar S ∧
        Group.IsFinitelyPresented S ∧ ∃ f : H →* S, Function.Injective f :=
  fun K _ n H hH =>
    palomar_of_embedsInFPSelfSimilarGroup (BooneHigmanLinear.linearHost_routeA hS1 hP1 hZ1 K n H hH)

#audit_axioms GroupApproximation.BHPalomar.LinearSelfSimilar.palomar_of_embedsInFPSelfSimilarGroup

end LinearSelfSimilar
end BHPalomar
end GroupApproximation
