import GroupApproximation.Algebra.LampCountable
import GroupApproximation.Algebra.PermutationalWreathSimple
import GroupApproximation.Sofic.MFNonsoficDoubleEndpoint
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group

/-!
# Coset wreath products over a normalizing pair are not sofic

Let `Γ ≤ G` and let `W = K ≀_{G/Γ} G` be the permutational wreath product of a
countable lamp group `K` over the coset action of a countable group `G`.
Suppose that in every faithful permutation-ultraproduct representation of `G`
the centralizer of `Γ` is normalized by `G`
(`HasSoficCentralizerNormalization Γ`), and that some `t ∈ G` conjugates an
element `γ ∈ Γ` outside `Γ`.  Then `W` is not sofic.

The argument is the wreath form of the free-lamp obstruction in
`Sofic/MFNonsoficDoubleEndpoint`.  A sofic approximation of `W` gives a faithful
representation `ι` of `W` in a universal sofic group, and `ι ∘ inr` is a faithful
representation of `G`.  A nontrivial one-site lamp at the base coset commutes
with `Γ`, because `Γ` fixes that coset.  Normalization makes its `t`-conjugate,
the lamp at the coset `t Γ`, commute with `γ`.  Faithfulness then forces
`γ t Γ = t Γ`, that is `t⁻¹ γ t ∈ Γ`.

The file also shows that `W` is finitely generated when `G` and `K` are: the
coset action is transitive, so generators of `G` together with one-site lamps at
the base coset generate `W`.
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

/-! ## The obstruction -/

/-- **The algebraic step.**  For `k ≠ 1`, if the one-site lamp `k` at the coset
`t Γ` commutes with `γ` inside `K ≀_{G/Γ} G`, then `γ` fixes `t Γ`, that is
`t⁻¹ γ t ∈ Γ`.

Every normalization hypothesis, exact or asymptotic, reaches its contradiction
through this lemma. -/
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

/-- **The faithful-representation step.**  Let `ι` be a faithful representation
of `K ≀_{G/Γ} G` in any group, and `k ≠ 1`.  If the `t`-conjugate of the one-site
lamp `k` at the base coset commutes with the image of `γ`, then `t⁻¹ γ t ∈ Γ`. -/
theorem wreath_conj_mem_of_faithful_commute {G : Type} [Group G] (Γ : Subgroup G)
    [DecidableEq (G ⧸ Γ)] {K : Type} [Group K] {k : K} (hk : k ≠ 1)
    {M : Type*} [Group M] (ι : Wreath K G (G ⧸ Γ) →* M)
    (hι : Function.Injective ι) {t γ : G}
    (hcomm : Commute
      (ι (inr t) * ι (inl (Lamp.single (wreathBaseCoset Γ) k)) * (ι (inr t))⁻¹)
      (ι (inr γ))) :
    t⁻¹ * γ * t ∈ Γ := by
  have hcomm' :
      Commute (ι (inl (Lamp.single (t • wreathBaseCoset Γ) k))) (ι (inr γ)) := by
    rw [← wreath_conj_inl_single t (wreathBaseCoset Γ) k]
    simpa only [map_mul, map_inv] using hcomm
  refine wreath_conj_mem_of_commute Γ hk ?_
  have h := hcomm'.eq
  rw [← map_mul ι, ← map_mul ι] at h
  exact hι h

/-- **Coset wreath products over a normalizing pair are not sofic.**  If the
centralizer of `Γ` is normalized by `G` in every faithful permutation-ultraproduct
representation, and `t⁻¹ γ t ∉ Γ` for some `γ ∈ Γ`, then `K ≀_{G/Γ} G` is not
sofic for every countable group `K` with a nontrivial element. -/
theorem not_isSofic_wreath_of_centralizerNormalization_of_ne_one
    {G : Type} [Group G] [Countable G] (Γ : Subgroup G)
    (hcentralizer : HasSoficCentralizerNormalization Γ)
    {K : Type} [Group K] [Countable K] {k : K} (hk : k ≠ 1)
    {t γ : G} (hγ : γ ∈ Γ) (hesc : t⁻¹ * γ * t ∉ Γ) :
    ¬ IsSofic (Wreath K G (G ⧸ Γ)) := by
  classical
  intro hsofic
  haveI : Countable (G ⧸ Γ) := QuotientGroup.mk_surjective.countable
  obtain ⟨S⟩ :=
    (isSofic_iff_nonempty_soficApproximation (Wreath K G (G ⧸ Γ))).mp hsofic
  let 𝒰 : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have h𝒰 : (𝒰 : Filter ℕ) ≤ Filter.cofinite := Ultrafilter.of_le _
  obtain ⟨ι, hι⟩ := exists_soficEmbedding_of_soficApproximation S h𝒰
  let ρ : G →* UniversalSofic 𝒰 S.model :=
    ι.comp (inr : G →* Wreath K G (G ⧸ Γ))
  have hρ : Function.Injective ρ := hι.comp inr_injective
  let q : UniversalSofic 𝒰 S.model :=
    ι (inl (Lamp.single (wreathBaseCoset Γ) k))
  have hq : ∀ δ : G, δ ∈ Γ → Commute q (ρ δ) := by
    intro δ hδ
    exact (wreath_commute_inl_single_inr
      ((smul_wreathBaseCoset_eq_iff Γ δ).mpr hδ) k).map ι
  exact hesc (wreath_conj_mem_of_faithful_commute Γ hk ι hι
    (hcentralizer 𝒰 S.model ρ hρ q hq t γ hγ))

/-- **The order-two lamp.**  Under centralizer normalization and an escaping
conjugate, the coset wreath product `(ℤ/2ℤ) ≀_{G/Γ} G` is not sofic. -/
theorem not_isSofic_wreath_of_centralizerNormalization
    {G : Type} [Group G] [Countable G] (Γ : Subgroup G)
    (hcentralizer : HasSoficCentralizerNormalization Γ)
    {t γ : G} (hγ : γ ∈ Γ) (hesc : t⁻¹ * γ * t ∉ Γ) :
    ¬ IsSofic (Wreath (Multiplicative (ZMod 2)) G (G ⧸ Γ)) :=
  not_isSofic_wreath_of_centralizerNormalization_of_ne_one Γ hcentralizer
    (k := Multiplicative.ofAdd (1 : ZMod 2))
    (by rw [Ne, ofAdd_eq_one]; decide) hγ hesc

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
