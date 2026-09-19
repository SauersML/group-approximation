import Mathlib.GroupTheory.HNNExtension
import Mathlib.Tactic.Group

/-!
# The free product as an HNN extension with trivial associated subgroups

`Algebra.FreeProductOrder` proves that a commutator of nontrivial elements of
distinct factors of a free product has infinite order, and records why
transferring it from `Monoid.CoprodI` to `Monoid.Coprod` blows up: the
two-element family has to be given by recursion on `Bool`, does not reduce at a
variable index, and the instance arguments then make the final application time
out even at a heartbeat budget five times the default.

This file takes the other road.  `G * ℤ` is also `HNNExtension G ⊥ ⊥`, and that
description has no family and no instance to unify: the stable letter is the
free `ℤ`, and *every* word in it is Britton-reduced, because the associated
subgroups are trivial and the chain condition of `NormalWord.ReducedWord` asks
only that a letter lying in the associated subgroup forces the exponents to
agree.

`commutator_ne_one` is the consequence the variant Adian--Rabin construction
needs of its witness `⁅w, s⁆`: it is nontrivial exactly when `w` is, and
`zpow_t_ne_one` of `Algebra.HNNRetraction` already gives that the stable letter
itself has infinite order.
-/

namespace GroupApproximation
namespace HNNTrivialAssociated

open HNNExtension

variable {G : Type} [Group G]

/-- The free product `G * ℤ`, as an HNN extension with trivial associated
subgroups. -/
abbrev FreeProd (G : Type) [Group G] : Type :=
  HNNExtension G (⊥ : Subgroup G) (⊥ : Subgroup G) (MulEquiv.refl _)

/-- With trivial associated subgroups, a letter of the base lies in the
associated subgroup only when it is the identity. -/
theorem mem_toSubgroup_iff (u : ℤˣ) (g : G) :
    g ∈ HNNExtension.toSubgroup (⊥ : Subgroup G) (⊥ : Subgroup G) u ↔ g = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp [HNNExtension.toSubgroup]

/-- The letters of `⁅w, t⁆ⁿ⁺¹`, after the head `w`.  The exponents alternate
`+1, -1`, and every group letter is `w⁻¹` or `w` except the last, which is `1`
and has no successor to constrain. -/
def commList (w : G) : ℕ → List (ℤˣ × G)
  | 0 => [((1 : ℤˣ), w⁻¹), ((-1 : ℤˣ), 1)]
  | n + 1 => ((1 : ℤˣ), w⁻¹) :: ((-1 : ℤˣ), w) :: commList w n

theorem commList_ne_nil (w : G) (n : ℕ) : commList w n ≠ [] := by
  cases n <;> simp [commList]

/-- The commutator, abbreviated. -/
def commElt (w : G) : FreeProd G :=
  HNNExtension.of w * HNNExtension.t * (HNNExtension.of w)⁻¹ *
    (HNNExtension.t : FreeProd G)⁻¹

/-- The product of the letters is the commutator power, off by the head. -/
theorem commList_prod (w : G) :
    ∀ n : ℕ,
      ((commList w n).map fun x : ℤˣ × G =>
          (HNNExtension.t : FreeProd G) ^ (x.1 : ℤ) * HNNExtension.of x.2).prod
        = (HNNExtension.of w)⁻¹ * (commElt w) ^ (n + 1)
  | 0 => by
      simp only [commList, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, commElt, map_one, map_inv,
        show ((1 : ℤˣ) : ℤ) = 1 from rfl, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
        zpow_one]
      group
  | n + 1 => by
      rw [commList, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
        commList_prod w n]
      set P := (commElt w) ^ (n + 1) with hP
      rw [show (commElt w) ^ (n + 1 + 1) = commElt w * P by
        rw [hP, ← pow_succ']]
      simp only [commElt, map_inv,
        show ((1 : ℤˣ) : ℤ) = 1 from rfl, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
        zpow_one]
      group

/-- The chain condition holds: every group letter but the last is `w` or `w⁻¹`,
neither of which lies in the trivial associated subgroup when `w ≠ 1`, so every
implication is vacuous. -/
theorem commList_chain (w : G) (hw : w ≠ 1) :
    ∀ n : ℕ, List.IsChain
      (fun a b : ℤˣ × G =>
        a.2 ∈ HNNExtension.toSubgroup (⊥ : Subgroup G) (⊥ : Subgroup G) a.1 → a.1 = b.1)
      (commList w n)
  | 0 => by
      simp only [commList, List.isChain_cons]
      refine ⟨?_, ?_⟩
      · rintro b hb hmem
        exact absurd ((mem_toSubgroup_iff _ _).1 hmem) (inv_ne_one.2 hw)
      · simp
  | n + 1 => by
      simp only [commList, List.isChain_cons]
      refine ⟨?_, ?_, ?_⟩
      · rintro b - hmem
        exact absurd ((mem_toSubgroup_iff _ _).1 hmem) (inv_ne_one.2 hw)
      · rintro b - hmem
        exact absurd ((mem_toSubgroup_iff _ _).1 hmem) hw
      · exact commList_chain w hw n

/-- The reduced word spelling `⁅w, t⁆ⁿ⁺¹`. -/
def commWord (w : G) (hw : w ≠ 1) (n : ℕ) :
    HNNExtension.NormalWord.ReducedWord G (⊥ : Subgroup G) (⊥ : Subgroup G) where
  head := w
  toList := commList w n
  chain := commList_chain w hw n

/-- **The commutator of a nontrivial base element with the stable letter has
infinite order.**  With trivial associated subgroups every word in the stable
letter is reduced, so Britton applies directly. -/
theorem commElt_pow_ne_one (w : G) (hw : w ≠ 1) (n : ℕ) :
    (commElt w) ^ (n + 1) ≠ 1 := by
  intro h
  have hprod : (commWord w hw n).prod (MulEquiv.refl (⊥ : Subgroup G)) = 1 := by
    show HNNExtension.of w *
      ((commList w n).map fun x : ℤˣ × G =>
        (HNNExtension.t : FreeProd G) ^ (x.1 : ℤ) * HNNExtension.of x.2).prod = 1
    rw [commList_prod w n, ← mul_assoc, mul_inv_cancel, one_mul, h]
  have hmem : (commWord w hw n).prod (MulEquiv.refl (⊥ : Subgroup G))
      ∈ (HNNExtension.of : G →* FreeProd G).range := by
    rw [hprod]
    exact ⟨1, map_one _⟩
  have hnil := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
    (MulEquiv.refl (⊥ : Subgroup G)) (commWord w hw n) hmem
  exact commList_ne_nil w n hnil

/-- **The commutator generates an infinite cyclic subgroup.**  The `ℤ`-form of
`commElt_pow_ne_one`, which is what an HNN layer with cyclic associated
subgroups asks for. -/
theorem commElt_zpow_ne_one (w : G) (hw : w ≠ 1) {p : ℤ} (hp : p ≠ 0) :
    (commElt w) ^ p ≠ 1 := by
  have pos : ∀ q : ℤ, 0 < q → (commElt w) ^ q ≠ 1 := by
    intro q hq
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = ((n + 1 : ℕ) : ℤ) := ⟨(q - 1).toNat, by omega⟩
    rw [zpow_natCast]
    exact commElt_pow_ne_one w hw n
  rcases lt_trichotomy p 0 with hneg | hzero | hpos
  · intro h
    refine pos (-p) (by omega) ?_
    rw [zpow_neg, h, inv_one]
  · exact absurd hzero hp
  · exact pos p hpos

end HNNTrivialAssociated
end GroupApproximation
