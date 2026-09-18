import GroupApproximation.BooneHigman.Metabelian.VdKInjCosetStab
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# van der Kallen's injectivity action, part 1: row cocycles

Lane `bh-met-91o`.  This is the combinatorial data for van der Kallen's elementary proof that
`St_n(R) → St_{n+1}(R)` is injective.  `St_{n+1}(R)` acts on the right on pairs
`(h, u) ∈ St_n(R) × R^{n+1}`:

  `(h, u) · x_{ij}(a) = (h · c(u, x_{ij}(a)), u ᵥ* M_{x_{ij}(a)})`.

The `St_n(R)`-valued function `c` on rows and roots is a *row cocycle*.

* `vdkInjAct_row u g = u ᵥ* M_g` is the right row action, with `vdkInjAct_row_one` and
  `vdkInjAct_row_mul`.
* `vdkInjAct_Cocycle n R` is the type of candidate cocycles
  `c : R^{n+1} → (roots of St_{n+1}(R)) → St_n(R)`.
* `vdkInjAct_IsCocycle c` lists the Steinberg relators of `St_{n+1}(R)`, rewritten as identities
  of Steinberg words in `St_n(R)`, one family per relator type (`add`, `commute`, `adjacent`).
  These are the relation checks for the proposed action.
* `vdkInjAct_IsBased c`: at the base row `e_last`, a stabilized root `x_{i'j'}(a)` (with
  `i' = castSucc i`, `j' = castSucc j`) has cocycle value exactly `x_{ij}(a) ∈ St_n(R)`.
* The group-theoretic helpers `vdkInjAct_add_aux`, `vdkInjAct_comm_aux` and `vdkInjAct_adj_aux`
  turn right-action identities into relator identities for the inverse permutations.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
  (projectionMatrix projectionMatrix_mul projectionMatrix_one)
open scoped Matrix commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The right row action of `St_m(R)` on `R^m`: `u ↦ u ᵥ* M_g`. -/
noncomputable def vdkInjAct_row {m : ℕ} (u : Fin m → R) (g : St m R) : Fin m → R :=
  u ᵥ* projectionMatrix g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_row

theorem vdkInjAct_row_one {m : ℕ} (u : Fin m → R) : vdkInjAct_row u (1 : St m R) = u := by
  show u ᵥ* projectionMatrix (1 : St m R) = u
  rw [projectionMatrix_one, Matrix.vecMul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_row_one

theorem vdkInjAct_row_mul {m : ℕ} (u : Fin m → R) (g g' : St m R) :
    vdkInjAct_row (vdkInjAct_row u g) g' = vdkInjAct_row u (g * g') := by
  show u ᵥ* projectionMatrix g ᵥ* projectionMatrix g' = u ᵥ* projectionMatrix (g * g')
  rw [projectionMatrix_mul, Matrix.vecMul_vecMul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_row_mul

variable (n R) in
/-- A candidate row cocycle: a value in `St_n(R)` for every row `u ∈ R^{n+1}` and every root
`x_{ij}(a)` of `St_{n+1}(R)`. -/
abbrev vdkInjAct_Cocycle : Type _ :=
  (Fin (n + 1) → R) → ∀ i j : Fin (n + 1), i ≠ j → R → St n R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_Cocycle

/-- The relation checks for the proposed action: every Steinberg relator of `St_{n+1}(R)`, read
through `(h, u) · x_{ij}(a) = (h · c(u, x_{ij}(a)), u ᵥ* M_{x_{ij}(a)})`, becomes an identity of
Steinberg words in `St_n(R)`.  The row components of each relator agree automatically. -/
structure vdkInjAct_IsCocycle (c : vdkInjAct_Cocycle n R) : Prop where
  /-- The relator `x_{ij}(a) x_{ij}(b) = x_{ij}(a + b)`. -/
  add : ∀ (u : Fin (n + 1) → R) (i j : Fin (n + 1)) (hij : i ≠ j) (a b : R),
    c u i j hij a * c (vdkInjAct_row u (x i j hij a)) i j hij b = c u i j hij (a + b)
  /-- The relator `x_{ij}(a) x_{kl}(b) = x_{kl}(b) x_{ij}(a)` for `j ≠ k`, `l ≠ i`. -/
  commute : ∀ (u : Fin (n + 1) → R) (i j k l : Fin (n + 1)) (hij : i ≠ j) (hkl : k ≠ l),
    j ≠ k → l ≠ i → ∀ a b : R,
    c u i j hij a * c (vdkInjAct_row u (x i j hij a)) k l hkl b =
      c u k l hkl b * c (vdkInjAct_row u (x k l hkl b)) i j hij a
  /-- The relator `x_{ij}(a) x_{jk}(b) = x_{ik}(ab) x_{jk}(b) x_{ij}(a)` for `i ≠ k`. -/
  adjacent : ∀ (u : Fin (n + 1) → R) (i j k : Fin (n + 1)) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : R),
    c u i j hij a * c (vdkInjAct_row u (x i j hij a)) j k hjk b =
      c u i k hik (a * b) * c (vdkInjAct_row u (x i k hik (a * b))) j k hjk b *
        c (vdkInjAct_row (vdkInjAct_row u (x i k hik (a * b))) (x j k hjk b)) i j hij a

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_IsCocycle

/-- The normalisation at the base row `e_last`: a stabilized root `x_{i'j'}(a)` has cocycle value
`x_{ij}(a)`. -/
def vdkInjAct_IsBased (c : vdkInjAct_Cocycle n R) : Prop :=
  ∀ (i j : Fin n) (hij : i ≠ j) (h' : i.castSucc ≠ j.castSucc) (a : R),
    c (Pi.single (Fin.last n) 1) i.castSucc j.castSucc h' a = x i j hij a

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_IsBased

/-- A row cocycle is trivial on `x_{ij}(0)`. -/
theorem vdkInjAct_IsCocycle.zero {c : vdkInjAct_Cocycle n R} (hc : vdkInjAct_IsCocycle c)
    (u : Fin (n + 1) → R) (i j : Fin (n + 1)) (hij : i ≠ j) : c u i j hij 0 = 1 := by
  have h := hc.add u i j hij 0 0
  rw [x_zero, vdkInjAct_row_one, add_zero] at h
  exact mul_left_cancel (h.trans (mul_one _).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_IsCocycle.zero

/-- The adjacent Steinberg relation in product form: `y₁ y₂ = y₃ y₂ y₁`. -/
theorem vdkInjAct_x_adjacent_eq {m : ℕ} (i j k : Fin m) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : R) :
    x i j hij a * x j k hjk b = x i k hik (a * b) * x j k hjk b * x i j hij a := by
  rw [← x_commutator i j k hij hjk hik a b, commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_x_adjacent_eq

/-- Additivity for the inverse permutations, from `q p = r`. -/
theorem vdkInjAct_add_aux {G : Type*} [Group G] {p q r : G} (h : q * p = r) :
    p⁻¹ * q⁻¹ * (r⁻¹)⁻¹ = 1 := by
  rw [← h]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_add_aux

/-- Commutation for the inverse permutations, from `q p = p q`. -/
theorem vdkInjAct_comm_aux {G : Type*} [Group G] {p q : G} (h : q * p = p * q) :
    ⁅p⁻¹, q⁻¹⁆ = 1 := by
  have e : p * q = q * p := h.symm
  rw [commutatorElement_def]
  calc p⁻¹ * q⁻¹ * p⁻¹⁻¹ * q⁻¹⁻¹ = p⁻¹ * q⁻¹ * (p * q) := by group
    _ = p⁻¹ * q⁻¹ * (q * p) := by rw [e]
    _ = 1 := by group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_comm_aux

/-- The adjacent relator for the inverse permutations, from `q p = p q s`. -/
theorem vdkInjAct_adj_aux {G : Type*} [Group G] {p q s : G} (h : q * p = p * q * s) :
    ⁅p⁻¹, q⁻¹⁆ * (s⁻¹)⁻¹ = 1 := by
  have hs : s = (p * q)⁻¹ * (q * p) := by
    rw [h]
    group
  rw [hs, commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_adj_aux

end GroupApproximation.BooneHigman.Metabelian.ElemFP
