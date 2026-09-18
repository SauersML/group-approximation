import GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeShift
import GroupApproximation.BooneHigman.Trees.TreeAut
import GroupApproximation.Meta.AxiomGuard

/-!
# The action of affine pairs on words (lane bh-met-02)

Research node `positive-char-polynomial-affine-groups-are-self-similar-proof`, step 4.  An affine
pair `(g, b)` with `g ∈ M_m(F[s_σ])`, `b ∈ F[s_σ]^m` acts on words over the letters
`F^m × F^{σ ∖ i₀}` by

  `(g, b) · ((e, a) v) = (g(0, a) e + b(0, a), a) · (σ_a(g), (σ_a(g) e + σ_a(b) - c)/s) · v`,

i.e. the first letter gets the digit `digit` and the tail is acted on by the state
`(σ_a(g), carry)`.

Main declarations:
* `act i₀ g b`, with `length_act`, `act_prefix`, `isTreeMap_act`;
* `act_one`: the pair `(1, 0)` acts trivially;
* `act_act`: `(g, b) · ((g', b') · v) = (g g', b + g b') · v`, the semidirect-product law.
-/

noncomputable section

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharPHost
namespace TreeHost

open MvPolynomial
open scoped Matrix

variable {F : Type*} [Field F] {σ : Type*} [DecidableEq σ] (i₀ : σ) {m : Type*} [Fintype m]

/-- The action of the affine pair `(g, b)` on words. -/
def act : Matrix m m (MvPolynomial σ F) → (m → MvPolynomial σ F) → List (Letter m F i₀) →
    List (Letter m F i₀)
  | _, _, [] => []
  | g, b, x :: v => (digit i₀ g b x, x.2) :: act (g.map (shift i₀ x.2)) (carry i₀ g b x) v

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.act

theorem act_cons (g : Matrix m m (MvPolynomial σ F)) (b : m → MvPolynomial σ F) (e : m → F)
    (a : {i : σ // i ≠ i₀} → F) (v : List (Letter m F i₀)) :
    act i₀ g b ((e, a) :: v) =
      (digit i₀ g b (e, a), a) :: act i₀ (g.map (shift i₀ a)) (carry i₀ g b (e, a)) v :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.act_cons

theorem length_act (g : Matrix m m (MvPolynomial σ F)) (b : m → MvPolynomial σ F)
    (w : List (Letter m F i₀)) : (act i₀ g b w).length = w.length := by
  induction w generalizing g b with
  | nil => rfl
  | cons x u ih =>
    obtain ⟨e, a⟩ := x
    rw [act_cons, List.length_cons, List.length_cons, ih]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.length_act

theorem act_prefix (g : Matrix m m (MvPolynomial σ F)) (b : m → MvPolynomial σ F)
    (w v : List (Letter m F i₀)) : act i₀ g b w <+: act i₀ g b (w ++ v) := by
  induction w generalizing g b with
  | nil => exact List.nil_prefix
  | cons x u ih =>
    obtain ⟨e, a⟩ := x
    rw [List.cons_append, act_cons, act_cons]
    exact (List.prefix_cons_inj _).2 (ih _ _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.act_prefix

theorem isTreeMap_act (g : Matrix m m (MvPolynomial σ F)) (b : m → MvPolynomial σ F) :
    Trees.IsTreeMap (act i₀ g b) :=
  ⟨length_act i₀ g b, act_prefix i₀ g b⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.isTreeMap_act

/-! ### The identity pair -/

theorem image_one_apply [DecidableEq m] (e : m → F) (j : m) :
    image (1 : Matrix m m (MvPolynomial σ F)) 0 e j = C (e j) := by
  rw [image, Matrix.one_mulVec, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.image_one_apply

theorem digit_carry_one [DecidableEq m] (e : m → F) (a : {i : σ // i ≠ i₀} → F) :
    digit i₀ (1 : Matrix m m (MvPolynomial σ F)) 0 (e, a) = e ∧
      carry i₀ (1 : Matrix m m (MvPolynomial σ F)) 0 (e, a) = 0 := by
  have h : ∀ j, shift i₀ a (image (1 : Matrix m m (MvPolynomial σ F)) 0 e j) =
      C (e j) + X i₀ * 0 := fun j => by
    rw [image_one_apply, shift_C, mul_zero, add_zero]
  exact ⟨funext fun j => (shift_unique i₀ a (h j)).1, funext fun j => (shift_unique i₀ a (h j)).2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.digit_carry_one

theorem map_one_shift [DecidableEq m] (a : {i : σ // i ≠ i₀} → F) :
    (1 : Matrix m m (MvPolynomial σ F)).map (shift i₀ a) = 1 :=
  Matrix.map_one (shift i₀ a) (map_zero (shift i₀ a)) (map_one (shift i₀ a))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.map_one_shift

/-- The pair `(1, 0)` acts trivially. -/
theorem act_one [DecidableEq m] (v : List (Letter m F i₀)) :
    act i₀ (1 : Matrix m m (MvPolynomial σ F)) 0 v = v := by
  induction v with
  | nil => rfl
  | cons x u ih =>
    obtain ⟨e, a⟩ := x
    obtain ⟨hd, hc⟩ := digit_carry_one i₀ e a
    rw [act_cons, map_one_shift, hd, hc, ih]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.act_one

/-! ### Products -/

omit [DecidableEq σ] in
/-- The first-level image of a product pair `(g g', b + g b')`. -/
theorem image_mul (g g' : Matrix m m (MvPolynomial σ F)) (b b' : m → MvPolynomial σ F)
    (e : m → F) : image (g * g') (b + g *ᵥ b') e = g *ᵥ image g' b' e + b := by
  rw [image, image, Matrix.mulVec_add, Matrix.mulVec_mulVec]
  abel

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.image_mul

/-- Digit and carry of a product pair: the digit is computed letter by letter, and the carry is
`carry g b (c', a) + σ_a(g) w'` where `(c', w')` are digit and carry of `(g', b')`. -/
theorem digit_carry_mul (g g' : Matrix m m (MvPolynomial σ F)) (b b' : m → MvPolynomial σ F)
    (e : m → F) (a : {i : σ // i ≠ i₀} → F) :
    digit i₀ (g * g') (b + g *ᵥ b') (e, a) = digit i₀ g b (digit i₀ g' b' (e, a), a) ∧
      carry i₀ (g * g') (b + g *ᵥ b') (e, a) =
        carry i₀ g b (digit i₀ g' b' (e, a), a) + g.map (shift i₀ a) *ᵥ carry i₀ g' b' (e, a) := by
  have hvec : (⇑(shift i₀ a) ∘ image g' b' e) =
      fun k => C (digit i₀ g' b' (e, a) k) + X i₀ * carry i₀ g' b' (e, a) k :=
    funext fun k => shift_image i₀ g' b' e a k
  have h2 : ∀ j, (g.map (shift i₀ a) *ᵥ fun k => C (digit i₀ g' b' (e, a) k)) j +
      shift i₀ a (b j) = C (digit i₀ g b (digit i₀ g' b' (e, a), a) j) +
        X i₀ * carry i₀ g b (digit i₀ g' b' (e, a), a) j := by
    intro j
    have h := shift_image i₀ g b (digit i₀ g' b' (e, a)) a j
    rwa [image, Pi.add_apply, map_add, RingHom.map_mulVec, shift_comp_C] at h
  have h : ∀ j, shift i₀ a (image (g * g') (b + g *ᵥ b') e j) =
      C (digit i₀ g b (digit i₀ g' b' (e, a), a) j) +
        X i₀ * (carry i₀ g b (digit i₀ g' b' (e, a), a) j +
          (g.map (shift i₀ a) *ᵥ carry i₀ g' b' (e, a)) j) := by
    intro j
    rw [image_mul, Pi.add_apply, map_add, RingHom.map_mulVec, hvec, mulVec_add_X_mul]
    linear_combination h2 j
  exact ⟨funext fun j => (shift_unique i₀ a (h j)).1, funext fun j => (shift_unique i₀ a (h j)).2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.digit_carry_mul

/-- **The semidirect-product law**: `(g, b) · ((g', b') · v) = (g g', b + g b') · v`. -/
theorem act_act (g g' : Matrix m m (MvPolynomial σ F)) (b b' : m → MvPolynomial σ F)
    (v : List (Letter m F i₀)) :
    act i₀ g b (act i₀ g' b' v) = act i₀ (g * g') (b + g *ᵥ b') v := by
  induction v generalizing g g' b b' with
  | nil => rfl
  | cons x u ih =>
    obtain ⟨e, a⟩ := x
    obtain ⟨hd, hc⟩ := digit_carry_mul i₀ g g' b b' e a
    rw [act_cons, act_cons, act_cons, ih, hd, hc, Matrix.map_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.act_act

end TreeHost
end CharPHost
end Metabelian
end BooneHigman
end GroupApproximation

end
