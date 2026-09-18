import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Meta.AxiomGuard

/-!
# Injective stability for `K₂` from an action with last-index root data

Lane `bh-met-35`.  This module holds the formal half of the permutation-action method for injective
stability (the method of van der Kallen's proof).  It works over an arbitrary ring `R`.

* `LastRootAction n R Ω` bundles two pieces of data.  The first is an action `act : St_n(R) →*
  Perm Ω`.  The second is a family of permutations `T i j hij a` of `Ω`, indexed by the roots of
  `St_{n+1}(R)`.  The data must satisfy:
  * `compat`: on roots avoiding the last index, `T` agrees with `act`;
  * `add`, `commute`, `adjacent`: the Steinberg relators hold for `T` whenever some index in the
    relator is the last one.
* `LastRootAction.T_add`, `T_commute`, `T_adjacent`: the relators then hold for *all* indices.
  If no index is last, every root comes from `St_n(R)` along `castSucc`.  Rewrite with `compat`,
  pull `act` out (`map_mul`, `map_commutatorElement`) and use the relation in `St_n(R)`.
* `LastRootAction.lift`: `T` descends to a homomorphism `St_{n+1}(R) →* Perm Ω`
  (`PresentedGroup.toGroup`), and `lift_comp_stab` gives `lift ∘ stab = act`.
* `eq_one_of_K2Stab_of_lastRootAction`: if `act` separates a point `ω₀` on a class `P` of elements
  of `K₂(n, R)`, then every `u` in `P` with `K2Stab u = 1` is trivial.  Indeed
  `act u = lift (stab u) = lift 1 = 1` fixes `ω₀`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

/-- An action of `St_n(R)` on `Ω`, together with permutations for the roots of `St_{n+1}(R)` that
extend it and satisfy every Steinberg relator involving the last index. -/
structure LastRootAction (n : ℕ) (R : Type*) [Ring R] (Ω : Type*) where
  /-- The action of `St_n(R)`. -/
  act : St n R →* Equiv.Perm Ω
  /-- Candidate permutations for the roots `x_ij(a)` of `St_{n+1}(R)`. -/
  T : ∀ i j : Fin (n + 1), i ≠ j → R → Equiv.Perm Ω
  /-- On roots avoiding the last index, `T` is the given action. -/
  compat : ∀ (i j : Fin n) (hij : i ≠ j) (h' : i.castSucc ≠ j.castSucc) (a : R),
    T i.castSucc j.castSucc h' a = act (x i j hij a)
  /-- Additivity for roots involving the last index. -/
  add : ∀ (i j : Fin (n + 1)) (hij : i ≠ j) (a b : R), (i = Fin.last n ∨ j = Fin.last n) →
    T i j hij a * T i j hij b = T i j hij (a + b)
  /-- Commutation of non-addable roots, when some index is the last one. -/
  commute : ∀ (i j k l : Fin (n + 1)) (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → l ≠ i → ∀ a b : R,
    (i = Fin.last n ∨ j = Fin.last n ∨ k = Fin.last n ∨ l = Fin.last n) →
    ⁅T i j hij a, T k l hkl b⁆ = 1
  /-- The adjacent commutator relation, when some index is the last one. -/
  adjacent : ∀ (i j k : Fin (n + 1)) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
    (i = Fin.last n ∨ j = Fin.last n ∨ k = Fin.last n) →
    ⁅T i j hij a, T j k hjk b⁆ = T i k hik (a * b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.LastRootAction

variable {R : Type*} [Ring R] {n : ℕ} {Ω : Type*}

/-- Additivity of `T` for all roots. -/
theorem LastRootAction.T_add (A : LastRootAction n R Ω) (i j : Fin (n + 1)) (hij : i ≠ j)
    (a b : R) : A.T i j hij a * A.T i j hij b = A.T i j hij (a + b) := by
  by_cases h : i = Fin.last n ∨ j = Fin.last n
  · exact A.add i j hij a b h
  · simp only [not_or] at h
    obtain ⟨hi, hj⟩ := h
    obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj
    have hij' : i' ≠ j' := ne_of_apply_ne Fin.castSucc hij
    rw [A.compat i' j' hij' hij a, A.compat i' j' hij' hij b, A.compat i' j' hij' hij (a + b),
      ← map_mul, x_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.LastRootAction.T_add

/-- Commutation of non-addable roots under `T`, for all indices. -/
theorem LastRootAction.T_commute (A : LastRootAction n R Ω) (i j k l : Fin (n + 1))
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    ⁅A.T i j hij a, A.T k l hkl b⁆ = 1 := by
  by_cases h : i = Fin.last n ∨ j = Fin.last n ∨ k = Fin.last n ∨ l = Fin.last n
  · exact A.commute i j k l hij hkl hjk hli a b h
  · simp only [not_or] at h
    obtain ⟨hi, hj, hk, hl⟩ := h
    obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj
    obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hk
    obtain ⟨l', rfl⟩ := Fin.exists_castSucc_eq.mpr hl
    have hij' : i' ≠ j' := ne_of_apply_ne Fin.castSucc hij
    have hkl' : k' ≠ l' := ne_of_apply_ne Fin.castSucc hkl
    have hjk' : j' ≠ k' := ne_of_apply_ne Fin.castSucc hjk
    have hli' : l' ≠ i' := ne_of_apply_ne Fin.castSucc hli
    rw [A.compat i' j' hij' hij a, A.compat k' l' hkl' hkl b, ← map_commutatorElement,
      (x_commute_of_ne i' j' k' l' hij' hkl' hjk' hli' a b).commutator_eq, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.LastRootAction.T_commute

/-- The adjacent commutator relation under `T`, for all indices. -/
theorem LastRootAction.T_adjacent (A : LastRootAction n R Ω) (i j k : Fin (n + 1))
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅A.T i j hij a, A.T j k hjk b⁆ = A.T i k hik (a * b) := by
  by_cases h : i = Fin.last n ∨ j = Fin.last n ∨ k = Fin.last n
  · exact A.adjacent i j k hij hjk hik a b h
  · simp only [not_or] at h
    obtain ⟨hi, hj, hk⟩ := h
    obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj
    obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hk
    have hij' : i' ≠ j' := ne_of_apply_ne Fin.castSucc hij
    have hjk' : j' ≠ k' := ne_of_apply_ne Fin.castSucc hjk
    have hik' : i' ≠ k' := ne_of_apply_ne Fin.castSucc hik
    rw [A.compat i' j' hij' hij a, A.compat j' k' hjk' hjk b, A.compat i' k' hik' hik (a * b),
      ← map_commutatorElement, x_commutator i' j' k' hij' hjk' hik' a b]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.LastRootAction.T_adjacent

/-- The permutation attached to a Steinberg generator of `St_{n+1}(R)`. -/
def LastRootAction.generatorPerm (A : LastRootAction n R Ω)
    (g : SteinbergGenerator (Fin (n + 1)) R) : Equiv.Perm Ω :=
  A.T g.row g.column g.row_ne_column g.coefficient

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.LastRootAction.generatorPerm

/-- `T` kills every Steinberg relator of `St_{n+1}(R)`. -/
theorem LastRootAction.generatorPerm_kills_relations (A : LastRootAction n R Ω)
    (w : FreeGroup (SteinbergGenerator (Fin (n + 1)) R))
    (hw : w ∈ SteinbergGroup.relations (I := Fin (n + 1)) (R := R)) :
    FreeGroup.lift A.generatorPerm w = 1 := by
  change SteinbergGroup.IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, LastRootAction.generatorPerm]
      change A.T i j hij a * A.T i j hij b * (A.T i j hij (a + b))⁻¹ = 1
      rw [A.T_add i j hij a b, mul_inv_cancel]
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of, LastRootAction.generatorPerm]
      change ⁅A.T i j hij a, A.T k l hkl b⁆ = 1
      exact A.T_commute i j k l hij hkl hjk hli a b
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        LastRootAction.generatorPerm]
      change ⁅A.T i j hij a, A.T j k hjk b⁆ * (A.T i k hik (a * b))⁻¹ = 1
      rw [A.T_adjacent i j k hij hjk hik a b, mul_inv_cancel]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.LastRootAction.generatorPerm_kills_relations

/-- The action of `St_{n+1}(R)` induced by `T`. -/
def LastRootAction.lift (A : LastRootAction n R Ω) : St (n + 1) R →* Equiv.Perm Ω :=
  PresentedGroup.toGroup (f := A.generatorPerm) A.generatorPerm_kills_relations

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.LastRootAction.lift

@[simp] theorem LastRootAction.lift_x (A : LastRootAction n R Ω) (i j : Fin (n + 1))
    (hij : i ≠ j) (a : R) : A.lift (x i j hij a) = A.T i j hij a := by
  exact PresentedGroup.toGroup.of _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.LastRootAction.lift_x

/-- The induced action restricts to `act` along the stabilization. -/
theorem LastRootAction.lift_comp_stab (A : LastRootAction n R Ω) :
    A.lift.comp (stab n R) = A.act := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, a⟩
  change A.lift (stab n R (x i j hij a)) = A.act (x i j hij a)
  rw [stab_x, A.lift_x, A.compat i j hij _ a]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.LastRootAction.lift_comp_stab

/-- An element of `St_n(R)` that stabilizes to `1` acts trivially. -/
theorem LastRootAction.act_eq_one_of_stab_eq_one (A : LastRootAction n R Ω) {g : St n R}
    (hg : stab n R g = 1) : A.act g = 1 := by
  rw [← A.lift_comp_stab, MonoidHom.comp_apply, hg, map_one]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.LastRootAction.act_eq_one_of_stab_eq_one

/-- **The formal injective-stability step**, for an arbitrary ring.  A `LastRootAction` whose `act`
separates `ω₀` on a class `P ⊆ K₂(n, R)` makes `K2Stab` injective on `P`. -/
theorem eq_one_of_K2Stab_of_lastRootAction (A : LastRootAction n R Ω) (P : K2n n R → Prop)
    (ω₀ : Ω) (hsep : ∀ u : K2n n R, P u → A.act (u : St n R) ω₀ = ω₀ → u = 1)
    (u : K2n n R) (hP : P u) (hu : K2Stab n R u = 1) : u = 1 := by
  refine hsep u hP ?_
  have h2 := congrArg (fun v : K2n (n + 1) R ↦ (v : St (n + 1) R)) hu
  have h1 : stab n R (u : St n R) = 1 := h2
  have h3 : A.act (u : St n R) = 1 := A.act_eq_one_of_stab_eq_one h1
  exact (DFunLike.congr_fun h3 ω₀).trans (Equiv.Perm.one_apply ω₀)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.eq_one_of_K2Stab_of_lastRootAction

end GroupApproximation.BooneHigman.Metabelian.ElemFP
