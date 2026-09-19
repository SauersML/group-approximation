import GroupApproximation.Steinberg.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# van der Kallen's presentation `St*(n, A)` and the elements `X(v, w)` (k2-poly, piece F.1)

W. van der Kallen, *Another presentation for Steinberg groups*, Indag. Math. **39** (1977),
304–312 (read at source). Let `A` be a commutative ring.

* **2.1.** `U` is the set of pairs `(i, j)` with `i` a unimodular column and `j` a row such that
  `j i = 0`.
* **2.2.** `St*(n, A)` is presented by generators `X(i, j)`, `(i, j) ∈ U`, and the relations
  - `X(i, j) X(i, k) = X(i, j + k)` if `(i, j), (i, k) ∈ U`,
  - `X(i, j) X(k, l) X(i, j)⁻¹ = X(k + i (j k), l - (l i) j)` if `(i, j), (k, l) ∈ U`.
* **3.5.** `x_pq(a) ↦ X(ε_p, a ε_qᵀ)` is a homomorphism `φ : St(n, A) → St*(n, A)`.
* **Theorem 1 (2.5).** If `n ≥ 4`, `φ` is an isomorphism.

This file proves everything except Theorem 1 itself:

* `U`, `conjPair` and `conjPair_mem` (the second relation stays inside `U`);
* `StStar`, the generators `X` and the two relations `X_mul`, `X_conj`, with `X_zero`, `X_neg`;
* the ordinary pairs `stdPair p q a = (ε_p, a ε_qᵀ)`, and `phi`, which is vdK 3.5. Its adjacent
  Steinberg relation is derived from the two `St*` relations;
* `Theorem1At`, vdK's Theorem 1 as a named statement (**owed**: vdK §3, 3.6–3.22);
* `Elements` and `elementsOfTheorem1`, the consumer-facing form of F.1 (a) on the k2-poly board:
  well-defined elements `X(v, w) ∈ St(n, A)` for every `(v, w) ∈ U`, satisfying both relations
  and restricting to `x_pq(a)` on the ordinary pairs. This follows from Theorem 1.

Columns and rows are both functions `I → A`, and `j i` is `j ⬝ᵥ i`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace VdK

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

section Pairs

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A]

/-- A column `v` is *unimodular* if some row `k` has `k v = 1` (vdK 2.3). -/
abbrev IsUnimodular (v : I → A) : Prop :=
  ∃ k : I → A, k ⬝ᵥ v = 1

variable (I A) in
/-- van der Kallen's set `U` (2.1): a unimodular column `i` and a row `j` with `j i = 0`. -/
def U : Set ((I → A) × (I → A)) :=
  {p | IsUnimodular p.1 ∧ p.2 ⬝ᵥ p.1 = 0}

theorem mem_U {p : (I → A) × (I → A)} : p ∈ U I A ↔ IsUnimodular p.1 ∧ p.2 ⬝ᵥ p.1 = 0 :=
  Iff.rfl

theorem mk_mem_U {i j : I → A} : (i, j) ∈ U I A ↔ IsUnimodular i ∧ j ⬝ᵥ i = 0 :=
  Iff.rfl

/-- The pair `(k + i (j k), l - (l i) j)` of vdK's second relation (2.2), for `p = (i, j)` and
`q = (k, l)`. -/
def conjPair (p q : (I → A) × (I → A)) : (I → A) × (I → A) :=
  (q.1 + (p.2 ⬝ᵥ q.1) • p.1, q.2 - (q.2 ⬝ᵥ p.1) • p.2)

/-- The second relation stays inside `U`. The row `m - (m i) j` witnesses unimodularity of
`k + i (j k)`, where `m k = 1`. -/
theorem conjPair_mem {p q : (I → A) × (I → A)} (hp : p ∈ U I A) (hq : q ∈ U I A) :
    conjPair p q ∈ U I A := by
  obtain ⟨-, hji⟩ := mem_U.1 hp
  obtain ⟨⟨m, hm⟩, hlk⟩ := mem_U.1 hq
  refine mem_U.2 ⟨⟨m - (m ⬝ᵥ p.1) • p.2, ?_⟩, ?_⟩
  · simp only [conjPair, sub_dotProduct, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hm, hji]
    ring
  · simp only [conjPair, sub_dotProduct, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hlk, hji]
    ring

#audit_axioms conjPair_mem

theorem add_mem {i j k : I → A} (hj : (i, j) ∈ U I A) (hk : (i, k) ∈ U I A) :
    (i, j + k) ∈ U I A :=
  mk_mem_U.2 ⟨(mk_mem_U.1 hj).1, by rw [add_dotProduct, (mk_mem_U.1 hj).2, (mk_mem_U.1 hk).2,
    add_zero]⟩

theorem zero_mem {i j : I → A} (hj : (i, j) ∈ U I A) : (i, 0) ∈ U I A :=
  mk_mem_U.2 ⟨(mk_mem_U.1 hj).1, by simp⟩

theorem neg_mem {i j : I → A} (hj : (i, j) ∈ U I A) : (i, -j) ∈ U I A :=
  mk_mem_U.2 ⟨(mk_mem_U.1 hj).1, by rw [neg_dotProduct, (mk_mem_U.1 hj).2, neg_zero]⟩

/-- `(ε_p, a ε_qᵀ)`, the pair of the ordinary generator `x_pq(a)` (vdK 2.4). -/
abbrev stdPair (p q : I) (a : A) : (I → A) × (I → A) :=
  (Pi.single p 1, Pi.single q a)

theorem stdPair_mem {p q : I} (hpq : p ≠ q) (a : A) : stdPair p q a ∈ U I A :=
  mk_mem_U.2 ⟨⟨Pi.single p 1, by rw [single_dotProduct, Pi.single_eq_same, mul_one]⟩,
    by rw [single_dotProduct, Pi.single_eq_of_ne hpq.symm, mul_zero]⟩

end Pairs

section Presentation

variable (I A : Type*) [Fintype I] [DecidableEq I] [CommRing A]

/-- The generators `X(i, j)` of `St*(n, A)`, one for each `(i, j) ∈ U` (vdK 2.2). -/
abbrev Gen : Type _ :=
  {p : (I → A) × (I → A) // p ∈ U I A}

variable {I A}

/-- vdK's two families of defining relators of `St*(n, A)` (2.2). -/
inductive IsRel : FreeGroup (Gen I A) → Prop
  | add (i j k : I → A) (h₁ : (i, j) ∈ U I A) (h₂ : (i, k) ∈ U I A) (h₃ : (i, j + k) ∈ U I A) :
      IsRel (FreeGroup.of (⟨(i, j), h₁⟩ : Gen I A) * FreeGroup.of ⟨(i, k), h₂⟩ *
        (FreeGroup.of ⟨(i, j + k), h₃⟩)⁻¹)
  | conj (p q : (I → A) × (I → A)) (hp : p ∈ U I A) (hq : q ∈ U I A) :
      IsRel (FreeGroup.of (⟨p, hp⟩ : Gen I A) * FreeGroup.of ⟨q, hq⟩ *
        (FreeGroup.of ⟨p, hp⟩)⁻¹ * (FreeGroup.of ⟨conjPair p q, conjPair_mem hp hq⟩)⁻¹)

variable (I A)

/-- The relator set of `St*(n, A)`. -/
def rels : Set (FreeGroup (Gen I A)) :=
  {w | IsRel w}

/-- **van der Kallen's group `St*(n, A)`** (2.2). -/
abbrev StStar : Type _ :=
  PresentedGroup (rels I A)

variable {I A}

/-- The generator `X(i, j)` of `St*(n, A)`. -/
def X (p : (I → A) × (I → A)) (hp : p ∈ U I A) : StStar I A :=
  PresentedGroup.of (⟨p, hp⟩ : Gen I A)

theorem X_congr {p q : (I → A) × (I → A)} (h : p = q) (hp : p ∈ U I A) (hq : q ∈ U I A) :
    X p hp = X q hq := by
  subst h
  rfl

/-- vdK's first relation. -/
theorem X_mul (i j k : I → A) (h₁ : (i, j) ∈ U I A) (h₂ : (i, k) ∈ U I A)
    (h₃ : (i, j + k) ∈ U I A) :
    X (i, j) h₁ * X (i, k) h₂ = X (i, j + k) h₃ := by
  apply eq_of_mul_inv_eq_one
  have hrel : FreeGroup.of (⟨(i, j), h₁⟩ : Gen I A) * FreeGroup.of ⟨(i, k), h₂⟩ *
      (FreeGroup.of ⟨(i, j + k), h₃⟩)⁻¹ ∈ rels I A :=
    IsRel.add i j k h₁ h₂ h₃
  simpa only [X, PresentedGroup.of, map_mul, map_inv] using PresentedGroup.one_of_mem hrel

#audit_axioms X_mul

/-- vdK's second relation. -/
theorem X_conj (p q : (I → A) × (I → A)) (hp : p ∈ U I A) (hq : q ∈ U I A) :
    X p hp * X q hq * (X p hp)⁻¹ = X (conjPair p q) (conjPair_mem hp hq) := by
  apply eq_of_mul_inv_eq_one
  have hrel : FreeGroup.of (⟨p, hp⟩ : Gen I A) * FreeGroup.of ⟨q, hq⟩ *
      (FreeGroup.of ⟨p, hp⟩)⁻¹ * (FreeGroup.of ⟨conjPair p q, conjPair_mem hp hq⟩)⁻¹ ∈
      rels I A :=
    IsRel.conj p q hp hq
  simpa only [X, PresentedGroup.of, map_mul, map_inv] using PresentedGroup.one_of_mem hrel

#audit_axioms X_conj

theorem X_zero (i : I → A) (h : (i, (0 : I → A)) ∈ U I A) : X (i, 0) h = 1 := by
  have h0 : X (i, 0) h * X (i, 0) h = X (i, 0) h := by
    rw [X_mul i 0 0 h h (add_mem h h)]
    exact X_congr (by simp) _ _
  exact mul_left_cancel (h0.trans (mul_one _).symm)

theorem X_neg (i j : I → A) (h : (i, j) ∈ U I A) (h' : (i, -j) ∈ U I A) :
    X (i, -j) h' = (X (i, j) h)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [X_mul i j (-j) h h' (add_mem h h'),
    X_congr (show (i, j + -j) = (i, (0 : I → A)) by simp) _ (zero_mem h)]
  exact X_zero i _

/-! ### vdK 3.5: the homomorphism `φ : St(n, A) → St*(n, A)` -/

theorem X_std_add {p q : I} (hpq : p ≠ q) (a b : A) :
    X (stdPair p q a) (stdPair_mem hpq a) * X (stdPair p q b) (stdPair_mem hpq b) =
      X (stdPair p q (a + b)) (stdPair_mem hpq (a + b)) := by
  rw [X_mul (Pi.single p 1) (Pi.single q a) (Pi.single q b) (stdPair_mem hpq a)
    (stdPair_mem hpq b) (add_mem (stdPair_mem hpq a) (stdPair_mem hpq b))]
  exact X_congr (by simp [stdPair, Pi.single_add]) _ _

theorem X_std_commute {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (a b : A) :
    ⁅X (stdPair i j a) (stdPair_mem hij a), X (stdPair k l b) (stdPair_mem hkl b)⁆ = 1 := by
  have hpair : conjPair (stdPair i j a) (stdPair k l b) = stdPair k l b := by
    refine Prod.ext ?_ ?_
    · show Pi.single k 1 + (Pi.single j a ⬝ᵥ Pi.single k 1) • Pi.single i 1 = Pi.single k 1
      rw [single_dotProduct, Pi.single_eq_of_ne hjk, mul_zero, zero_smul, add_zero]
    · show Pi.single l b - (Pi.single l b ⬝ᵥ Pi.single i 1) • Pi.single j a = Pi.single l b
      rw [single_dotProduct, Pi.single_eq_of_ne hli, mul_zero, zero_smul, sub_zero]
  rw [commutatorElement_def, X_conj, X_congr hpair _ (stdPair_mem hkl b)]
  simp

#audit_axioms X_std_commute

/-- The adjacent Steinberg relation holds in `St*`. With `u = X(ε_i, a ε_jᵀ)`,
`w = X(ε_j, b ε_kᵀ)` and `t = X(ε_i, ab ε_kᵀ)`, the two `St*` relations give
`w u w⁻¹ = u t⁻¹` and `u t u⁻¹ = t`. Together these give `⁅u, w⁆ = t`. -/
theorem X_std_adjacent {i j k : I} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : A) :
    ⁅X (stdPair i j a) (stdPair_mem hij a), X (stdPair j k b) (stdPair_mem hjk b)⁆ =
      X (stdPair i k (a * b)) (stdPair_mem hik (a * b)) := by
  have htu : (Pi.single i 1, -Pi.single k (a * b)) ∈ U I A := neg_mem (stdPair_mem hik (a * b))
  have hsum : (Pi.single i 1, Pi.single j a + -Pi.single k (a * b)) ∈ U I A :=
    add_mem (stdPair_mem hij a) htu
  -- `w u w⁻¹ = u t⁻¹`
  have hF1 : X (stdPair j k b) (stdPair_mem hjk b) * X (stdPair i j a) (stdPair_mem hij a) *
      (X (stdPair j k b) (stdPair_mem hjk b))⁻¹ =
      X (stdPair i j a) (stdPair_mem hij a) *
        (X (stdPair i k (a * b)) (stdPair_mem hik (a * b)))⁻¹ := by
    have hpair : conjPair (stdPair j k b) (stdPair i j a) =
        (Pi.single i 1, Pi.single j a + -Pi.single k (a * b)) := by
      refine Prod.ext ?_ ?_
      · show Pi.single i 1 + (Pi.single k b ⬝ᵥ Pi.single i 1) • Pi.single j 1 = Pi.single i 1
        rw [single_dotProduct, Pi.single_eq_of_ne hik.symm, mul_zero, zero_smul, add_zero]
      · show Pi.single j a - (Pi.single j a ⬝ᵥ Pi.single j 1) • Pi.single k b =
          Pi.single j a + -Pi.single k (a * b)
        rw [single_dotProduct, Pi.single_eq_same, mul_one, ← smul_eq_mul, Pi.single_smul',
          sub_eq_add_neg]
    rw [X_conj, X_congr hpair _ hsum,
      ← X_neg (Pi.single i 1) (Pi.single k (a * b)) (stdPair_mem hik (a * b)) htu,
      X_mul (Pi.single i 1) (Pi.single j a) (-Pi.single k (a * b)) (stdPair_mem hij a) htu hsum]
  -- `u t u⁻¹ = t`
  have hF2 : X (stdPair i j a) (stdPair_mem hij a) *
      X (stdPair i k (a * b)) (stdPair_mem hik (a * b)) *
      (X (stdPair i j a) (stdPair_mem hij a))⁻¹ =
      X (stdPair i k (a * b)) (stdPair_mem hik (a * b)) := by
    have hpair : conjPair (stdPair i j a) (stdPair i k (a * b)) = stdPair i k (a * b) := by
      refine Prod.ext ?_ ?_
      · show Pi.single i 1 + (Pi.single j a ⬝ᵥ Pi.single i 1) • Pi.single i 1 = Pi.single i 1
        rw [single_dotProduct, Pi.single_eq_of_ne hij.symm, mul_zero, zero_smul, add_zero]
      · show Pi.single k (a * b) - (Pi.single k (a * b) ⬝ᵥ Pi.single i 1) • Pi.single j a =
          Pi.single k (a * b)
        rw [single_dotProduct, Pi.single_eq_of_ne hik.symm, mul_zero, zero_smul, sub_zero]
    rw [X_conj, X_congr hpair _ (stdPair_mem hik (a * b))]
  set u := X (stdPair i j a) (stdPair_mem hij a)
  set w := X (stdPair j k b) (stdPair_mem hjk b)
  set t := X (stdPair i k (a * b)) (stdPair_mem hik (a * b))
  have hinv : w * u⁻¹ * w⁻¹ = t * u⁻¹ := by
    calc w * u⁻¹ * w⁻¹ = (w * u * w⁻¹)⁻¹ := by group
      _ = (u * t⁻¹)⁻¹ := by rw [hF1]
      _ = t * u⁻¹ := by group
  calc ⁅u, w⁆ = u * (w * u⁻¹ * w⁻¹) := by rw [commutatorElement_def]; group
    _ = u * (t * u⁻¹) := by rw [hinv]
    _ = u * t * u⁻¹ := by group
    _ = t := hF2

#audit_axioms X_std_adjacent

variable (I A) in
/-- **vdK 3.5.** The homomorphism `φ : St(n, A) → St*(n, A)`, `x_pq(a) ↦ X(ε_p, a ε_qᵀ)`. -/
def phi : SteinbergGroup I A →* StStar I A :=
  PresentedGroup.toGroup
    (f := fun g : SteinbergGenerator I A =>
      X (stdPair g.row g.column g.coefficient) (stdPair_mem g.row_ne_column g.coefficient))
    (by
      intro w hw
      change SteinbergGroup.IsRelation w at hw
      cases hw with
      | add i j hij a b =>
          simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
          change X (stdPair i j a) _ * X (stdPair i j b) _ * (X (stdPair i j (a + b)) _)⁻¹ = 1
          rw [X_std_add hij a b]
          simp
      | commute i j k l hij hkl hjk hli a b =>
          simp only [map_commutatorElement, FreeGroup.lift_apply_of]
          exact X_std_commute hij hkl hjk hli a b
      | adjacent i j k hij hjk hik a b =>
          simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
          change ⁅X (stdPair i j a) _, X (stdPair j k b) _⁆ *
            (X (stdPair i k (a * b)) _)⁻¹ = 1
          rw [X_std_adjacent hij hjk hik a b]
          simp)

@[simp] theorem phi_x (p q : I) (hpq : p ≠ q) (a : A) :
    phi I A (x p q hpq a) = X (stdPair p q a) (stdPair_mem hpq a) :=
  PresentedGroup.toGroup.of _

#audit_axioms phi_x

/-! ### vdK Theorem 1 and the consumer-facing elements `X(v, w) ∈ St(n, A)` -/

variable (I A) in
/-- **van der Kallen, Theorem 1 (2.5).** `φ : St(n, A) → St*(n, A)` is an isomorphism. vdK prove
this for commutative `A` and `n ≥ 4`, i.e. `4 ≤ Fintype.card I`. **Owed**: the proof, vdK §3,
3.6–3.22. It builds `ψ : St* → St` from the elements `x(i, j)` of 3.8 and 3.10, the sets
`X̄(i, j)` of 3.13, and uniqueness (3.15, 3.21). Milnor's Lemma 5.4 (central extensions of
perfect groups) and the perfectness of `St*` (3.4) then force `ψ ∘ φ = id`. -/
def Theorem1At : Prop :=
  Function.Bijective (phi I A)

variable (I A) in
/-- **F.1 (a)**, in the form the k2-poly consumers use: elements `X(v, w) ∈ St(n, A)` for every
`(v, w) ∈ U`, satisfying vdK's two relations and restricting to the ordinary generators. -/
structure Elements where
  /-- The element `X(v, w) ∈ St(n, A)`. -/
  elt : ∀ p : (I → A) × (I → A), p ∈ U I A → SteinbergGroup I A
  mul : ∀ (i j k : I → A) (h₁ : (i, j) ∈ U I A) (h₂ : (i, k) ∈ U I A)
    (h₃ : (i, j + k) ∈ U I A), elt (i, j) h₁ * elt (i, k) h₂ = elt (i, j + k) h₃
  conj : ∀ (p q : (I → A) × (I → A)) (hp : p ∈ U I A) (hq : q ∈ U I A),
    elt p hp * elt q hq * (elt p hp)⁻¹ = elt (conjPair p q) (conjPair_mem hp hq)
  std : ∀ (p q : I) (hpq : p ≠ q) (a : A), elt (stdPair p q a) (stdPair_mem hpq a) = x p q hpq a

/-- vdK's Theorem 1 gives the elements `X(v, w) ∈ St(n, A)`: transport `X` along `φ⁻¹`. -/
noncomputable def elementsOfTheorem1 (h : Theorem1At I A) : Elements I A :=
  let e : SteinbergGroup I A ≃* StStar I A := MulEquiv.ofBijective (phi I A) h
  { elt := fun p hp => e.symm (X p hp)
    mul := fun i j k h₁ h₂ h₃ => by
      rw [← map_mul, X_mul i j k h₁ h₂ h₃]
    conj := fun p q hp hq => by
      rw [← map_inv, ← map_mul, ← map_mul, X_conj]
    std := fun p q hpq a => by
      rw [MulEquiv.symm_apply_eq]
      exact (phi_x p q hpq a).symm }

end Presentation

end VdK
end K2Found
end BooneHigmanLinear
end GroupApproximation
