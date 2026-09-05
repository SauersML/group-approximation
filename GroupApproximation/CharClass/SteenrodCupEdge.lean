import GroupApproximation.CharClass.SteenrodCochain
import Mathlib.Order.Interval.Finset.Fin

/-!
# The two ends of the cup-`i` family

`⌣₀` is the Alexander–Whitney cup product and `⌣ₘ` on a pair of `m`-cochains is
the identity.  These are the two computations that turn Steenrod's construction
into the squares `Sq^m x = x ⌣ x` and `Sq^0 = id`.

## `⌣₀`

A `0`-cut of a `(p+q)`-simplex is a single vertex `c`, its left family is the
initial segment `Iic c` and its right family the final segment `Ici c`.  So the
left face has `c + 1` vertices, only `c = p` contributes, and the two faces are
the front `p`-face and the back `q`-face of the **vendored** Alexander–Whitney
convention (`frontFace`, `backFace` of
`ThirdParty/.../AlgebraicTopology/AlexanderWhitney.lean`).  `cochainCupI_zero`
is therefore an equality on the nose with `cochainCup`, not merely up to a
convention.

## `⌣ₘ`

An `m`-cut of an `m`-simplex uses every vertex, so both families are everything
and both faces are the simplex itself.  Over `ZMod 2` the single term is
`α(σ) * α(σ) = α(σ)`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass

noncomputable section

/-! ## 1. Singleton cuts -/

variable {N : ℕ}

theorem cutRank_singleton (c x : Fin N) : cutRank ({c} : Finset (Fin N)) x =
    if c < x then 1 else 0 := by
  unfold cutRank
  rw [Finset.filter_singleton]
  split_ifs <;> simp

theorem cutU_singleton (c : Fin N) : cutU ({c} : Finset (Fin N)) = Finset.Iic c := by
  ext x
  rw [mem_cutU, Finset.mem_Iic, Finset.mem_singleton, cutRank_singleton]
  by_cases hlt : c < x
  · rw [if_pos hlt]
    constructor
    · rintro (rfl | h)
      · exact absurd hlt (lt_irrefl _)
      · exact absurd h (by decide)
    · intro hle
      exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)
  · rw [if_neg hlt]
    exact ⟨fun _ => not_lt.1 hlt, fun _ => Or.inr rfl⟩

theorem cutV_singleton (c : Fin N) : cutV ({c} : Finset (Fin N)) = Finset.Ici c := by
  ext x
  rw [mem_cutV, Finset.mem_Ici, Finset.mem_singleton, cutRank_singleton]
  by_cases hlt : c < x
  · rw [if_pos hlt]
    exact ⟨fun _ => le_of_lt hlt, fun _ => Or.inr rfl⟩
  · rw [if_neg hlt]
    constructor
    · rintro (rfl | h)
      · exact le_refl _
      · exact absurd h (by decide)
    · intro hle
      exact Or.inl (le_antisymm (not_lt.1 hlt) hle)

theorem card_cutU_singleton (c : Fin N) :
    (cutU ({c} : Finset (Fin N))).card = (c : ℕ) + 1 := by
  rw [cutU_singleton, Fin.card_Iic]

/-! ## 2. `⌣₀` is the Alexander–Whitney cup product -/

theorem restrictSimplex_id {X : TopCat.{0}} {n : ℕ} (σ : singularSimplices X n) :
    restrictSimplex (𝟙 (⦋n⦌ : SimplexCategory)) σ = σ := by
  unfold restrictSimplex
  rw [op_id, Functor.map_id_apply]

theorem cochainCupI_zero {R : Type} [CommRing R] {X : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup R X p) (ψ : singularCochainGroup R X q) :
    cochainCupI 0 p q (p + q) φ ψ = cochainCup p q φ ψ := by
  apply cochain_ext
  intro σ
  rw [cochainCupI_eval, cochainCup_eval]
  obtain ⟨c₀, hc₀⟩ : ∃ c : Fin (p + q + 1), (c : ℕ) = p := ⟨⟨p, by omega⟩, rfl⟩
  have hmem : ({c₀} : Finset (Fin (p + q + 1))) ∈ cutIndex 0 (p + q) :=
    mem_cutIndex.2 (Finset.card_singleton c₀)
  have hcardU : (cutU ({c₀} : Finset (Fin (p + q + 1)))).card = p + 1 := by
    rw [card_cutU_singleton, hc₀]
  have hcardV : (cutV ({c₀} : Finset (Fin (p + q + 1)))).card = q + 1 := by
    have hcount := cutU_card_add_cutV_card ({c₀} : Finset (Fin (p + q + 1)))
    rw [hcardU, Finset.card_singleton] at hcount
    omega
  have hsum : ∑ S ∈ cutIndex 0 (p + q), faceVal p φ σ (cutU S) * faceVal q ψ σ (cutV S)
      = faceVal p φ σ (cutU ({c₀} : Finset (Fin (p + q + 1))))
        * faceVal q ψ σ (cutV ({c₀} : Finset (Fin (p + q + 1)))) := by
    refine Finset.sum_eq_single _ ?_ ?_
    · intro S hS hne
      obtain ⟨c, rfl⟩ := Finset.card_eq_one.1 (card_of_mem_cutIndex hS)
      refine mul_eq_zero_of_left (faceVal_of_card_ne φ σ ?_) _
      rw [card_cutU_singleton]
      intro hcard
      exact hne (by rw [Fin.ext (show (c : ℕ) = (c₀ : ℕ) by omega)])
    · intro hb
      exact absurd hmem hb
  rw [hsum]
  have hfront : faceOfFinset (cutU ({c₀} : Finset (Fin (p + q + 1)))) hcardU = frontFace p q := by
    refine (eq_faceOfFinset _ hcardU (frontFace p q) (fun i => ?_) ?_).symm
    · rw [cutU_singleton]
      refine Finset.mem_Iic.2 ?_
      have hval : ((frontFace p q).toOrderHom i : ℕ) ≤ (c₀ : ℕ) := by
        rw [frontFace_apply, hc₀]
        exact Nat.lt_succ_iff.1 i.isLt
      exact hval
    · intro i j hij
      have hval : ((frontFace p q).toOrderHom i : ℕ) < ((frontFace p q).toOrderHom j : ℕ) := by
        rw [frontFace_apply, frontFace_apply]
        exact hij
      exact hval
  have hback : faceOfFinset (cutV ({c₀} : Finset (Fin (p + q + 1)))) hcardV = backFace p q := by
    refine (eq_faceOfFinset _ hcardV (backFace p q) (fun i => ?_) ?_).symm
    · rw [cutV_singleton]
      refine Finset.mem_Ici.2 ?_
      have hval : (c₀ : ℕ) ≤ ((backFace p q).toOrderHom i : ℕ) := by
        rw [backFace_apply, hc₀]
        omega
      exact hval
    · intro i j hij
      have hval : ((backFace p q).toOrderHom i : ℕ) < ((backFace p q).toOrderHom j : ℕ) := by
        rw [backFace_apply, backFace_apply]
        have : (i : ℕ) < (j : ℕ) := hij
        omega
      exact hval
  rw [faceVal_of_card p φ σ hcardU, faceVal_of_card q ψ σ hcardV, hfront, hback]
  rfl

/-! ## 3. `⌣ₘ` on a pair of `m`-cochains is the identity -/

theorem cutIndex_self (m : ℕ) : cutIndex m m = {(Finset.univ : Finset (Fin (m + 1)))} := by
  ext S
  rw [mem_cutIndex, Finset.mem_singleton]
  constructor
  · intro h
    refine Finset.card_eq_iff_eq_univ.1 ?_
    rw [h, Fintype.card_fin]
  · intro h
    rw [h, Finset.card_univ, Fintype.card_fin]

theorem cutU_univ (m : ℕ) : cutU (Finset.univ : Finset (Fin (m + 1))) = Finset.univ := by
  ext x
  rw [mem_cutU]
  exact ⟨fun _ => Finset.mem_univ x, fun _ => Or.inl (Finset.mem_univ x)⟩

theorem cutV_univ (m : ℕ) : cutV (Finset.univ : Finset (Fin (m + 1))) = Finset.univ := by
  ext x
  rw [mem_cutV]
  exact ⟨fun _ => Finset.mem_univ x, fun _ => Or.inl (Finset.mem_univ x)⟩

theorem faceOfFinset_univ (m : ℕ)
    (h : (Finset.univ : Finset (Fin (m + 1))).card = m + 1) :
    faceOfFinset (Finset.univ : Finset (Fin (m + 1))) h = 𝟙 (⦋m⦌ : SimplexCategory) := by
  refine (eq_faceOfFinset _ h (𝟙 (⦋m⦌ : SimplexCategory)) (fun i => Finset.mem_univ _) ?_).symm
  intro i j hij
  exact hij

theorem zmod_two_mul_self (x : ZMod 2) : x * x = x := by
  revert x
  decide

/-- **`⌣ₘ` is the identity.**  The only `m`-cut of an `m`-simplex uses every
vertex, both faces are the simplex itself, and squaring is the identity in
`ZMod 2`. -/
theorem cochainCupI_self {X : TopCat.{0}} (m : ℕ)
    (α : singularCochainGroup (ZMod 2) X m) :
    cochainCupI m m m m α α = α := by
  apply cochain_ext
  intro σ
  rw [cochainCupI_eval, cutIndex_self, Finset.sum_singleton, cutU_univ, cutV_univ]
  have hcard : (Finset.univ : Finset (Fin (m + 1))).card = m + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [faceVal_of_card m α σ hcard, faceOfFinset_univ, restrictSimplex_id]
  exact zmod_two_mul_self _

end

end CharClass
end GroupApproximation
