import GroupApproximation.Algebra.HNNBridgeFamily
import GroupApproximation.Algebra.CoprodIAltWord

/-!
# The conjugate family is free

`Algebra.HNNBridgeFamily` fixes `uₖ = a^{k+1} b a^{-(k+1)}` and the junction
identity; `Algebra.CoprodIAltWord` supplies alternating reduced words.  This
file joins them: a product

    u_{k₁}^{n₁} ⋯ u_{k_m}^{n_m}       (kᵢ ≠ k_{i+1}, nᵢ ≠ 0)

expands into the alternating word

    a^{k₁+1} b^{n₁} a^{k₂-k₁} b^{n₂} ⋯ a^{k_m-k_{m-1}} b^{n_m} a^{-(k_m+1)} ,

which is reduced --- every `b`-block because `nᵢ ≠ 0`, every interior
`a`-block because `kᵢ ≠ k_{i+1}`, the outer ones because `kᵢ + 1 ≠ 0` --- and
therefore nontrivial.  That is `uProd_ne_one`, and it is the freeness of the
family in the form the Higman--Neumann--Neumann bridge consumes.

The computation is carried out on the free product side, through Mathlib's
`freeGroupEquivCoprodI`, and proof-free: `expand` produces the bare letter
list, `listProd` multiplies it, and the `Word` with its `ne_one` and
`chain_ne` is assembled only in the last step.
-/

namespace GroupApproximation
namespace HNNBridgeFreeness

open Monoid Monoid.CoprodI
open GroupApproximation.HNNBridgeFamily
open GroupApproximation.CoprodIAltWord

/-- The generator of the one-generator free group. -/
def e : FreeGroup Unit := FreeGroup.of Unit.unit

/-- Exponent sum on the one-generator free group. -/
def eExp : FreeGroup Unit →* Multiplicative ℤ :=
  FreeGroup.lift fun _ ↦ Multiplicative.ofAdd (1 : ℤ)

@[simp] theorem eExp_e : eExp e = Multiplicative.ofAdd (1 : ℤ) := by
  simp [eExp, e]

theorem e_zpow_ne_one {m : ℤ} (hm : m ≠ 0) : e ^ m ≠ 1 := by
  intro h
  have h1 : Multiplicative.ofAdd m = 1 := by
    simpa [map_zpow, eExp_e] using congrArg eExp h
  exact hm (congrArg Multiplicative.toAdd h1)

/-! ## 1.  The expansion -/

/-- The product of a list of blocks `(k, n)`, meaning `uₖⁿ`. -/
def uProd : List (ℕ × ℤ) → FreeGroup (Fin 2)
  | [] => 1
  | (k, n) :: rest => u k ^ n * uProd rest

/-- The letters of the expansion, with a pending `a`-exponent `c`.  Indices are
supplied by `altList`; only the letters are produced here. -/
def expand : ℤ → List (ℕ × ℤ) → List (FreeGroup Unit)
  | c, [] => [e ^ c]
  | c, (k, n) :: rest =>
      e ^ (c + (k : ℤ) + 1) :: e ^ n :: expand (-((k : ℤ) + 1)) rest

theorem expand_ne_nil (c : ℤ) (l : List (ℕ × ℤ)) : expand c l ≠ [] := by
  cases l with
  | nil => simp [expand]
  | cons p rest => simp [expand]

/-! ## 2.  The expansion computes the product -/

theorem toCoprod_a2_zpow (m : ℤ) :
    freeGroupEquivCoprodI (a2 ^ m) = CoprodI.of (i := (0 : Fin 2)) (e ^ m) := by
  rw [map_zpow]
  simp [a2, e]

theorem toCoprod_b2_zpow (m : ℤ) :
    freeGroupEquivCoprodI (b2 ^ m) = CoprodI.of (i := (1 : Fin 2)) (e ^ m) := by
  rw [map_zpow]
  simp [b2, e]

theorem listProd_expand (c : ℤ) (l : List (ℕ × ℤ)) :
    listProd (M := fun _ : Fin 2 ↦ FreeGroup Unit) (altList 0 (expand c l))
      = CoprodI.of (i := (0 : Fin 2)) (e ^ c) * freeGroupEquivCoprodI (uProd l) := by
  induction l generalizing c with
  | nil =>
      rw [expand, listProd_altList_singleton, uProd, map_one, mul_one]
  | cons p rest ih =>
      obtain ⟨k, n⟩ := p
      rw [expand, listProd_altList_cons_cons, ih, uProd, map_mul,
        u_zpow', map_mul, map_mul, toCoprod_a2_zpow, toCoprod_b2_zpow,
        toCoprod_a2_zpow]
      have hfuse : (CoprodI.of (i := (0 : Fin 2)) (e ^ (c + (k : ℤ) + 1)) :
          CoprodI (fun _ : Fin 2 ↦ FreeGroup Unit))
          = CoprodI.of (i := (0 : Fin 2)) (e ^ c)
              * CoprodI.of (i := (0 : Fin 2)) (e ^ ((k : ℤ) + 1)) := by
        rw [← map_mul, ← zpow_add]
        ring_nf
      rw [hfuse]
      simp only [mul_assoc]
      rfl

/-! ## 3.  The blocks are nontrivial -/

theorem expand_letters_ne_one : ∀ (c : ℤ) (l : List (ℕ × ℤ)),
    (∀ p ∈ l, p.2 ≠ 0) →
    l.IsChain (fun p q : ℕ × ℤ ↦ p.1 ≠ q.1) →
    (l = [] → c ≠ 0) →
    (∀ k n, l.head? = some (k, n) → c + (k : ℤ) + 1 ≠ 0) →
    ∀ q ∈ expand c l, q ≠ 1 := by
  intro c l
  induction l generalizing c with
  | nil =>
      intro _ _ hnil _ q hq
      rw [expand, List.mem_singleton] at hq
      subst hq
      exact e_zpow_ne_one (hnil rfl)
  | cons p rest ih =>
      obtain ⟨k, n⟩ := p
      intro hexp hchain _ hhead q hq
      rw [expand, List.mem_cons, List.mem_cons] at hq
      rcases hq with rfl | rfl | hq'
      · exact e_zpow_ne_one (hhead k n rfl)
      · exact e_zpow_ne_one (hexp (k, n) (by simp))
      · refine ih _ (fun r hr ↦ hexp r (List.mem_cons_of_mem _ hr))
          (hchain.tail) ?_ ?_ q hq'
        · intro _
          omega
        · intro k' n' hk'
          have hne : k ≠ k' := by
            rcases rest with _ | ⟨r, rest'⟩
            · simp at hk'
            · rw [List.head?_cons, Option.some_inj] at hk'
              subst hk'
              exact (List.isChain_cons_cons.mp hchain).1
          intro hz
          exact hne (by omega)

/-! ## 4.  Freeness -/

/-- **The conjugate family is free.**  A nonempty alternating product of
nontrivial powers of the `uₖ` is nontrivial. -/
theorem uProd_ne_one (l : List (ℕ × ℤ)) (hne : l ≠ [])
    (hexp : ∀ p ∈ l, p.2 ≠ 0)
    (hchain : l.IsChain fun p q : ℕ × ℤ ↦ p.1 ≠ q.1) :
    uProd l ≠ 1 := by
  intro hcon
  classical
  have hletters : ∀ q ∈ expand 0 l, q ≠ 1 := by
    refine expand_letters_ne_one 0 l hexp hchain (fun h ↦ absurd h hne) ?_
    intro k n _
    omega
  have hprod : listProd (M := fun _ : Fin 2 ↦ FreeGroup Unit)
      (altList 0 (expand 0 l)) = 1 := by
    rw [listProd_expand, hcon, map_one, mul_one, zpow_zero, map_one]
  refine prod_altWord_ne_one (0 : Fin 2) (expand 0 l) hletters
    (expand_ne_nil 0 l) ?_
  rw [word_prod_eq_listProd, altWord_toList]
  exact hprod

end HNNBridgeFreeness
end GroupApproximation
