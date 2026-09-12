import GroupApproximation.Algebra.PermutationalWreathSimple
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group

/-!
# Escaping conjugates of one-site lamps in coset wreath products

Let `Γ ≤ G` and let `W = K ≀_{G/Γ} G` be the permutational wreath product of a
lamp group `K` over the coset action of `G` on `G ⧸ Γ`.  This file proves the
algebra behind the nonsoficity of `W` under centralizer normalization
(`Sofic/WreathCentralizerNormalizationSequential`):

* a one-site lamp at the base coset `Γ` commutes with every element of `Γ`
  (`wreath_commute_inl_single_inr`);
* conjugating it by `t` moves it to the coset `t Γ` (`wreath_conj_inl_single`);
* for a nontrivial lamp value, its `t`-conjugate commutes with `γ` only when
  `t⁻¹ γ t ∈ Γ` (`wreath_conj_mem_of_commute`, `wreath_conj_lamp_not_commute`).

It also shows that `W` is finitely generated when `G` and `K` are: the coset
action is transitive, so generators of `G` together with one-site lamps at the
base coset generate `W` (`wreath_quotient_fg`).
-/

namespace GroupApproximation

open SemidirectProduct

/-! ## The base coset -/

/-- The base coset `Γ` in the coset space `G ⧸ Γ`. -/
def wreathBaseCoset {G : Type} [Group G] (Γ : Subgroup G) : G ⧸ Γ :=
  QuotientGroup.mk 1

/-- Translating the base coset by `g` gives the coset `g Γ`. -/
theorem smul_wreathBaseCoset {G : Type} [Group G] (Γ : Subgroup G) (g : G) :
    g • wreathBaseCoset Γ = (QuotientGroup.mk g : G ⧸ Γ) := by
  show (QuotientGroup.mk (g * 1) : G ⧸ Γ) = QuotientGroup.mk g
  rw [mul_one]

/-- An element fixes the base coset exactly when it lies in `Γ`. -/
theorem smul_wreathBaseCoset_eq_iff {G : Type} [Group G] (Γ : Subgroup G) (g : G) :
    g • wreathBaseCoset Γ = wreathBaseCoset Γ ↔ g ∈ Γ := by
  rw [smul_wreathBaseCoset]
  show (QuotientGroup.mk g : G ⧸ Γ) = QuotientGroup.mk 1 ↔ g ∈ Γ
  rw [QuotientGroup.eq]
  simp

/-! ## One-site lamps under conjugation -/

/-- Conjugating a one-site lamp by an element of the acting group moves its
site. -/
theorem wreath_conj_inl_single {K : Type} [Group K] {G : Type} [Group G]
    {X : Type} [MulAction G X] [DecidableEq X] (g : G) (x : X) (k : K) :
    (inr g * inl (Lamp.single x k) * inr g⁻¹ : Wreath K G X) =
      inl (Lamp.single (g • x) k) := by
  rw [← inl_aut]
  exact congrArg inl (lampAut_single g x k)

/-- A one-site lamp commutes with every element of the acting group that fixes
its site. -/
theorem wreath_commute_inl_single_inr {K : Type} [Group K] {G : Type} [Group G]
    {X : Type} [MulAction G X] [DecidableEq X] {g : G} {x : X}
    (hgx : g • x = x) (k : K) :
    Commute (inl (Lamp.single x k) : Wreath K G X) (inr g) := by
  have h := wreath_conj_inl_single (K := K) g x k
  rw [hgx, map_inv, mul_inv_eq_iff_eq_mul] at h
  exact h.symm

/-- Nontrivial one-site lamps with the same value are equal exactly when their
sites are equal. -/
theorem lampSingle_eq_iff_of_ne_one {K : Type} [Group K] {X : Type} [DecidableEq X]
    {x y : X} {k : K} (hk : k ≠ 1) :
    (Lamp.single x k : Lamp K X) = Lamp.single y k ↔ x = y := by
  constructor
  · intro h
    by_contra hxy
    have hval : (Lamp.single x k : Lamp K X).toFun x =
        (Lamp.single y k : Lamp K X).toFun x := by
      rw [h]
    rw [Lamp.single_apply_self, Lamp.single_apply_of_ne hxy] at hval
    exact hk hval
  · rintro rfl
    rfl

/-! ## The escaping conjugate -/

/-- **The algebraic step.**  For `k ≠ 1`, if the one-site lamp `k` at the coset
`t Γ` commutes with `γ` inside `K ≀_{G/Γ} G`, then `γ` fixes `t Γ`, that is
`t⁻¹ γ t ∈ Γ`. -/
theorem wreath_conj_mem_of_commute {G : Type} [Group G] (Γ : Subgroup G)
    [DecidableEq (G ⧸ Γ)] {K : Type} [Group K] {k : K} (hk : k ≠ 1) {t γ : G}
    (hcommW : Commute
      (inl (Lamp.single (t • wreathBaseCoset Γ) k) : Wreath K G (G ⧸ Γ)) (inr γ)) :
    t⁻¹ * γ * t ∈ Γ := by
  have hfix : γ • t • wreathBaseCoset Γ = t • wreathBaseCoset Γ := by
    have h := wreath_conj_inl_single (K := K) γ (t • wreathBaseCoset Γ) k
    rw [map_inv, ← hcommW.eq, mul_inv_cancel_right, inl_inj,
      lampSingle_eq_iff_of_ne_one hk] at h
    exact h.symm
  have hmk : (QuotientGroup.mk (γ * t) : G ⧸ Γ) = QuotientGroup.mk t := by
    rw [← smul_wreathBaseCoset, ← smul_wreathBaseCoset, mul_smul]
    exact hfix
  have hmem : (γ * t)⁻¹ * t ∈ Γ := QuotientGroup.eq.mp hmk
  have heq : t⁻¹ * γ * t = ((γ * t)⁻¹ * t)⁻¹ := by group
  rw [heq]
  exact inv_mem hmem

/-- **The escaping conjugate does not commute.**  If `t⁻¹ γ t ∉ Γ` and `k ≠ 1`,
then the `t`-conjugate of the one-site lamp `k` at the base coset does not
commute with `γ` in `K ≀_{G/Γ} G`. -/
theorem wreath_conj_lamp_not_commute {G : Type} [Group G] (Γ : Subgroup G)
    [DecidableEq (G ⧸ Γ)] {K : Type} [Group K] {k : K} (hk : k ≠ 1) {t γ : G}
    (hesc : t⁻¹ * γ * t ∉ Γ) :
    (inr t * inl (Lamp.single (wreathBaseCoset Γ) k) * (inr t)⁻¹ * inr γ :
        Wreath K G (G ⧸ Γ)) ≠
      inr γ * (inr t * inl (Lamp.single (wreathBaseCoset Γ) k) * (inr t)⁻¹) := by
  intro h
  apply hesc
  refine wreath_conj_mem_of_commute Γ hk ?_
  have hconj := wreath_conj_inl_single (K := K) t (wreathBaseCoset Γ) k
  rw [map_inv] at hconj
  rw [hconj] at h
  exact h

/-! ## Finite generation -/

/-- **Coset wreath products are finitely generated** when the acting group and
the lamp group are: the coset action is transitive, so generators of `G`
together with one-site lamps at the base coset generate. -/
theorem wreath_quotient_fg {G : Type} [Group G] {K : Type} [Group K]
    (Γ : Subgroup G) (hG : Group.FG G) (hK : Group.FG K) :
    Group.FG (Wreath K G (G ⧸ Γ)) := by
  classical
  obtain ⟨SG, hSG⟩ : (⊤ : Subgroup G).FG := hG.out
  obtain ⟨SK, hSK⟩ : (⊤ : Subgroup K).FG := hK.out
  have htrans : ∀ x : G ⧸ Γ, ∃ g : G, g • wreathBaseCoset Γ = x := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨g, smul_wreathBaseCoset Γ g⟩
  refine Group.fg_iff.mpr ⟨_,
    wreath_eq_closure (K := K) (G := G) (X := G ⧸ Γ)
      (wreathBaseCoset Γ) htrans hSG hSK, ?_⟩
  exact ((SG : Set G).toFinite.image _).union ((SK : Set K).toFinite.image _)

end GroupApproximation
