import GroupApproximation.BooneHigman.Metabelian.CharPHost.Carry

/-!
# State recursion of the carry substitution (lane bh-met-01)

Research node `positive-char-polynomial-affine-groups-are-self-similar-proof`, step 4
("Substitution"): for every `a' ∈ O^(k-1)`,

  `σ_α(P)<a'> = P(u, α + u a') = P<α + u a'>`,

where `P<a> = P(u, a)` sends the uniformizer variable to `u`.  The state of a state is obtained
by composing substitutions: the state at the word `(e_1, α_1) (e_2, α_2) ⋯ (e_j, α_j)` uses
`σ_{α_j} ∘ ⋯ ∘ σ_{α_1}`, and this composite sends `s_i ↦ α_{1,i} + s_0 α_{2,i} + ⋯ + s_0^j s_i`.

Here `O` is replaced by an arbitrary commutative `R`-algebra `S` with a chosen element `u`.

Main declarations:
* `withUniformizer i₀ u a`, the point with `u` at `i₀` and `a` elsewhere; `shiftPoint α u a`, the
  point `α + u a`;
* `aeval_carrySubst`: `σ_α(P)<a> = P<α + u a>`;
* `carrySubstList i₀ w`, the composite `σ_{α_j} ∘ ⋯ ∘ σ_{α_1}` for `w = [α_1, …, α_j]`, with
  `carrySubstList_append`, `carrySubstList_X_self`, `carrySubstList_X_of_ne` (the digit formula),
  and `aeval_carrySubstList`: `σ_w(P)<a> = P<α_1 + u(α_2 + ⋯ + u(α_j + u a))>`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharPHost

open MvPolynomial

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
variable {S : Type*} [CommRing S] [Algebra R S]

/-- The point with coordinate `u` at the uniformizer index `i₀` and `a i` elsewhere. -/
def withUniformizer (i₀ : ι) (u : S) (a : ι → S) (i : ι) : S :=
  if i = i₀ then u else a i

/-- The point `α + u a`. -/
def shiftPoint (α : ι → R) (u : S) (a : ι → S) (i : ι) : S :=
  algebraMap R S (α i) + u * a i

/-- **Substitution identity**: `σ_α(P)(u, a) = P(u, α + u a)`. -/
theorem aeval_carrySubst (i₀ : ι) (α : ι → R) (u : S) (a : ι → S) (P : MvPolynomial ι R) :
    aeval (withUniformizer i₀ u a) (carrySubst i₀ α P) =
      aeval (withUniformizer i₀ u (shiftPoint α u a)) P := by
  have h : (aeval (withUniformizer i₀ u a)).comp (carrySubst i₀ α) =
      aeval (withUniformizer i₀ u (shiftPoint α u a)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X]
    by_cases hi : i = i₀
    · subst hi
      rw [carrySubst_X_self]
      simp [withUniformizer]
    · rw [carrySubst_X_of_ne i₀ α hi]
      simp [withUniformizer, shiftPoint, hi]
  have hP := AlgHom.congr_fun h P
  rwa [AlgHom.comp_apply] at hP

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.aeval_carrySubst

/-- The composite substitution along a word of parameters: for `w = [α_1, …, α_j]` this is
`σ_{α_j} ∘ ⋯ ∘ σ_{α_1}`, the substitution of the state at a vertex of level `j`. -/
noncomputable def carrySubstList (i₀ : ι) :
    List (ι → R) → (MvPolynomial ι R →ₐ[R] MvPolynomial ι R)
  | [] => AlgHom.id R (MvPolynomial ι R)
  | α :: w => (carrySubstList i₀ w).comp (carrySubst i₀ α)

theorem carrySubstList_nil (i₀ : ι) :
    carrySubstList i₀ ([] : List (ι → R)) = AlgHom.id R (MvPolynomial ι R) := rfl

theorem carrySubstList_cons (i₀ : ι) (α : ι → R) (w : List (ι → R)) :
    carrySubstList i₀ (α :: w) = (carrySubstList i₀ w).comp (carrySubst i₀ α) := rfl

/-- **State recursion**: the substitution of a concatenated word is the composite. -/
theorem carrySubstList_append (i₀ : ι) (w w' : List (ι → R)) :
    carrySubstList i₀ (w ++ w') = (carrySubstList i₀ w').comp (carrySubstList i₀ w) := by
  induction w with
  | nil => rw [List.nil_append, carrySubstList_nil, AlgHom.comp_id]
  | cons α w ih =>
    rw [List.cons_append, carrySubstList_cons, carrySubstList_cons, ih, AlgHom.comp_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.carrySubstList_append

theorem carrySubstList_X_self (i₀ : ι) (w : List (ι → R)) :
    carrySubstList i₀ w (X i₀) = X i₀ := by
  induction w with
  | nil => rw [carrySubstList_nil, AlgHom.id_apply]
  | cons α w ih => rw [carrySubstList_cons, AlgHom.comp_apply, carrySubst_X_self, ih]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.carrySubstList_X_self

/-- The digits `α_{1,i} + s_0 α_{2,i} + ⋯ + s_0^(j-1) α_{j,i}` of a word `[α_1, …, α_j]`. -/
noncomputable def carryDigits (i₀ : ι) : List (ι → R) → ι → MvPolynomial ι R
  | [], _ => 0
  | α :: w, i => C (α i) + X i₀ * carryDigits i₀ w i

theorem carryDigits_nil (i₀ i : ι) : carryDigits i₀ ([] : List (ι → R)) i = 0 := rfl

theorem carryDigits_cons (i₀ : ι) (α : ι → R) (w : List (ι → R)) (i : ι) :
    carryDigits i₀ (α :: w) i = C (α i) + X i₀ * carryDigits i₀ w i := rfl

/-- **Digit formula** for the composite substitution: for `i ≠ i₀`,
`σ_w(s_i) = α_{1,i} + s_0 α_{2,i} + ⋯ + s_0^(j-1) α_{j,i} + s_0^j s_i`. -/
theorem carrySubstList_X_of_ne (i₀ : ι) (w : List (ι → R)) {i : ι} (hi : i ≠ i₀) :
    carrySubstList i₀ w (X i) = carryDigits i₀ w i + X i₀ ^ w.length * X i := by
  induction w with
  | nil =>
    rw [carrySubstList_nil, AlgHom.id_apply, carryDigits_nil, List.length_nil, pow_zero, one_mul,
      zero_add]
  | cons α w ih =>
    rw [carrySubstList_cons, AlgHom.comp_apply, carrySubst_X_of_ne i₀ α hi, map_add, map_mul,
      carrySubstList_X_self, ih, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, carryDigits_cons,
      List.length_cons]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.carrySubstList_X_of_ne

/-- The point `α_1 + u(α_2 + ⋯ + u(α_j + u a))` reached along a word `[α_1, …, α_j]`. -/
def listPoint (u : S) : List (ι → R) → (ι → S) → ι → S
  | [], a => a
  | α :: w, a => shiftPoint α u (listPoint u w a)

theorem listPoint_nil (u : S) (a : ι → S) : listPoint u ([] : List (ι → R)) a = a := rfl

theorem listPoint_cons (u : S) (α : ι → R) (w : List (ι → R)) (a : ι → S) :
    listPoint u (α :: w) a = shiftPoint α u (listPoint u w a) := rfl

/-- **Iterated substitution identity**: `σ_w(P)(u, a) = P(u, α_1 + u(α_2 + ⋯ + u(α_j + u a)))`.
-/
theorem aeval_carrySubstList (i₀ : ι) (u : S) (w : List (ι → R)) (a : ι → S)
    (P : MvPolynomial ι R) :
    aeval (withUniformizer i₀ u a) (carrySubstList i₀ w P) =
      aeval (withUniformizer i₀ u (listPoint u w a)) P := by
  induction w generalizing P with
  | nil => rw [carrySubstList_nil, AlgHom.id_apply, listPoint_nil]
  | cons α w ih =>
    rw [carrySubstList_cons, AlgHom.comp_apply, ih, aeval_carrySubst, listPoint_cons]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.aeval_carrySubstList

end CharPHost
end Metabelian
end BooneHigman
end GroupApproximation
