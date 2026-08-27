import GroupApproximation.Sofic.AscendingHNNTelescopeRadical
import GroupApproximation.Algebra.CountableInstances

/-!
# The full telescope radical lies in the MF radical

**Theorem 37.5 and Section 47** of the ascending-HNN dossier, completed.

`Sofic/AscendingHNNTelescopeRadical` collapses one stage: the base copy is
Kazhdan, the stable letter compresses it, and the resulting lamp differences
join two sites differing by the level `-1` copy.  Reaching the whole telescope
`N = ⋃ₙ t⁻ⁿ Γ tⁿ` looks like it needs an induction that iterates the collapse
on successive quotients.  It does not.

The level-`n` copy `Γₙ = t⁻ⁿ Γ tⁿ` is *itself* a Kazhdan subgroup -- it is a
conjugate of the base -- and `tⁿ` compresses it, since `tⁿ Γₙ t⁻ⁿ = Γ ≤ Γₙ`.
So the collapse criterion applies to the pair `(Γₙ, tⁿ)` directly, for every
`n`, with the one-site lamp at the **root** coset as witness: what the
criterion needs is a site fixed by the compressed copy, and the compressed copy
of `Γₙ` is the base, which fixes the root.  Each level therefore contributes
its own collapse commutators with no reference to the previous one, and the
telescope is exhausted because every element of it *is* a level element
(`Quotient.inductionOn` on the mapping telescope).

* `levelSub`, `levelSub_hasKazhdanPropertyT`, `wreathT_pow_compress` -- the
  level-`n` Kazhdan subgroup and its compressor.
* `lampDiff_level_mem_actualCoronaMFResidual` -- one level.
* `lampDiff_mem_actualCoronaMFResidual_of_rightHom_eq` -- **any two sites of
  equal height**: the full lamp-collapse kernel.
* `telescopeRadical_le_actualCoronaMFResidual`, and
  `actualCoronaMFResidual_eq_telescopeRadical` when the visible quotient is MF.

Two sites have equal height exactly when they differ by an element of the
telescope, so the subgroup generated here is the kernel of the pushforward of
the lamp base along the height map -- the `Φ∞` of the dossier.
-/

namespace GroupApproximation
namespace MarkedCompression

open SemidirectProduct MappingTelescope InvolutionCollapseEndpoint
open scoped commutatorElement

variable {Γ₀ : Type} [Group Γ₀] (β : Γ₀ →* Γ₀) (hβ : Function.Injective β)
variable {K₀ : Type} [Group K₀] [DecidableEq (Cosets β hβ)]

/- Quotients of countable groups are countable.  Proved once as
`GroupApproximation.CountableInstances.quotientCountable` and taken here with
the same `local` scope the mirrored copy had. -/
attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

/-! ## The level tower -/

/-- Reversing a lamp difference inverts it. -/
theorem lampDiff_inv (x y : Cosets β hβ) (k₀ : K₀) :
    (lampDiff β hβ x y k₀)⁻¹ = lampDiff β hβ y x k₀ := by
  rw [lampDiff, lampDiff, ← map_inv]
  refine congrArg inl ?_
  rw [mul_inv_rev, inv_inv]

/-- The level-`n` copy of the base group inside the vertical group. -/
def levelHom (n : ℕ) : Γ₀ →* Vertical β hβ :=
  (inl : Telescope β hβ →* Vertical β hβ).comp (level β hβ n)

omit [DecidableEq (Cosets β hβ)] in
@[simp] theorem levelHom_zero_apply (γ : Γ₀) :
    levelHom β hβ 0 γ = iotaVertical β hβ γ := rfl

omit [DecidableEq (Cosets β hβ)] in
include hβ in
theorem levelHom_injective (n : ℕ) : Function.Injective (levelHom β hβ n) :=
  inl_injective.comp (level_injective β hβ n)

omit [DecidableEq (Cosets β hβ)] in
/-- Conjugating the level-`n` copy down by `tⁿ` lands in the base copy: this is
the HNN relation iterated. -/
theorem tpow_conj_levelHom (n : ℕ) (γ : Γ₀) :
    tVertical β hβ ^ n * levelHom β hβ n γ * (tVertical β hβ ^ n)⁻¹
      = iotaVertical β hβ γ := by
  induction n with
  | zero => simp [levelHom_zero_apply]
  | succ n ih =>
      have hstep : (levelHom β hβ (n + 1) γ : Vertical β hβ)
          = (tVertical β hβ)⁻¹ * levelHom β hβ n γ * tVertical β hβ :=
        inl_level_succ β hβ n γ
      rw [pow_succ, hstep]
      calc tVertical β hβ ^ n * tVertical β hβ *
              ((tVertical β hβ)⁻¹ * levelHom β hβ n γ * tVertical β hβ) *
              (tVertical β hβ ^ n * tVertical β hβ)⁻¹
          = tVertical β hβ ^ n * levelHom β hβ n γ *
              (tVertical β hβ ^ n)⁻¹ := by group
        _ = iotaVertical β hβ γ := ih

omit [DecidableEq (Cosets β hβ)] in
/-- The base copy is the level-`n` copy of an iterate: every level contains the
base. -/
theorem levelHom_iterate (n : ℕ) (γ : Γ₀) :
    levelHom β hβ n (iterateHom β n γ) = iotaVertical β hβ γ := by
  refine congrArg (inl : Telescope β hβ →* Vertical β hβ) ?_
  show mk β hβ n (iterateHom β n γ) = mk β hβ 0 γ
  rw [mk_eq_mk_iff]
  rfl

/-- The level-`n` copy inside the wreath product. -/
def levelSub (n : ℕ) : Subgroup (WreathV (K := K₀) β hβ) :=
  ((inr : Vertical β hβ →* WreathV (K := K₀) β hβ).comp
    (levelHom β hβ n)).range

omit [DecidableEq (Cosets β hβ)] in
theorem mem_levelSub_iff {n : ℕ} {w : WreathV (K := K₀) β hβ} :
    w ∈ levelSub (K₀ := K₀) β hβ n ↔ ∃ γ : Γ₀, inr (levelHom β hβ n γ) = w := by
  simp [levelSub, MonoidHom.mem_range]

omit [DecidableEq (Cosets β hβ)] in
include hβ in
/-- Every level copy is isomorphic to the base group, so it inherits property
`(T)`. -/
theorem levelSub_hasKazhdanPropertyT (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀)
    (n : ℕ) :
    HasKazhdanPropertyT.{0, 0} ↥(levelSub (K₀ := K₀) β hβ n) := by
  have hf : Function.Injective
      ((inr : Vertical β hβ →* WreathV (K := K₀) β hβ).comp
        (levelHom β hβ n)) :=
    inr_injective.comp (levelHom_injective β hβ n)
  exact HasKazhdanPropertyT.of_mulEquiv (MonoidHom.ofInjective hf).symm hΓ

omit [DecidableEq (Cosets β hβ)] in
/-- **The `n`-th compressor.**  `tⁿ` conjugates the level-`n` copy onto the
base copy, which sits inside it. -/
theorem wreathT_pow_compress {n : ℕ} {w : WreathV (K := K₀) β hβ}
    (hw : w ∈ levelSub β hβ n) :
    wreathT β hβ ^ n * w * (wreathT β hβ ^ n)⁻¹ ∈ levelSub (K₀ := K₀) β hβ n := by
  obtain ⟨γ, rfl⟩ := (mem_levelSub_iff β hβ).mp hw
  have hconj : wreathT β hβ ^ n *
      (inr (levelHom β hβ n γ) : WreathV (K := K₀) β hβ) *
      (wreathT β hβ ^ n)⁻¹ = inr (iotaVertical β hβ γ) := by
    rw [wreathT, ← map_pow, ← map_inv, ← map_mul, ← map_mul,
      tpow_conj_levelHom]
  rw [hconj]
  exact (mem_levelSub_iff β hβ).mpr ⟨iterateHom β n γ, by rw [levelHom_iterate]⟩

/-! ## The witness at the root coset -/

/-- The one-site lamp at the root coset. -/
def rootLamp (k₀ : K₀) : WreathV (K := K₀) β hβ :=
  inl (Lamp.single (rootCoset β hβ) k₀)

/-- Conjugating the root lamp moves its site. -/
theorem conj_rootLamp (v : Vertical β hβ) (k₀ : K₀) :
    (inr v : WreathV (K := K₀) β hβ) * rootLamp β hβ k₀ * (inr v)⁻¹
      = inl (Lamp.single (v • rootCoset β hβ) k₀) :=
  conj_inl_single K₀ (Vertical β hβ) (Cosets β hβ) _ _ _

/-- **The root lamp is an involutive compression witness for every level.**
The compressed copy of the level-`n` group is the base, and the base fixes the
root coset -- which is exactly the centrality condition. -/
theorem isInvolutiveCompressionWitness_rootLamp {k₀ : K₀} (hk2 : k₀ * k₀ = 1)
    (n : ℕ) :
    IsInvolutiveCompressionWitness (levelSub (K₀ := K₀) β hβ n)
      (wreathT β hβ ^ n) (rootLamp β hβ k₀) := by
  refine ⟨?_, ?_, ?_⟩
  · have hsingle : Lamp.single (rootCoset β hβ) k₀ *
        Lamp.single (rootCoset β hβ) k₀ = 1 := by
      have h1 := map_mul (Lamp.singleHom (K := K₀) (rootCoset β hβ)) k₀ k₀
      rw [hk2, map_one] at h1
      simpa using h1.symm
    rw [rootLamp, ← map_mul, hsingle, map_one]
  · intro w hw
    obtain ⟨γ, rfl⟩ := (mem_levelSub_iff β hβ).mp hw
    have hconj : wreathT β hβ ^ n *
        (inr (levelHom β hβ n γ) : WreathV (K := K₀) β hβ) *
        (wreathT β hβ ^ n)⁻¹ = inr (iotaVertical β hβ γ) := by
      rw [wreathT, ← map_pow, ← map_inv, ← map_mul, ← map_mul,
        tpow_conj_levelHom]
    rw [hconj]
    have hfix : (inr (iotaVertical β hβ γ) : WreathV (K := K₀) β hβ) *
        rootLamp β hβ k₀ * (inr (iotaVertical β hβ γ))⁻¹
        = rootLamp β hβ k₀ := by
      rw [conj_rootLamp, iotaVertical_smul_rootCoset]
      rfl
    exact mul_inv_eq_iff_eq_mul.mp hfix
  · intro w₁ h₁ w₂ h₂
    obtain ⟨γ₁, rfl⟩ := (mem_levelSub_iff β hβ).mp h₁
    obtain ⟨γ₂, rfl⟩ := (mem_levelSub_iff β hβ).mp h₂
    rw [conj_rootLamp, conj_rootLamp]
    have hbase := conj_single_commute (K := K₀) (levelHom β hβ n γ₁)
      (levelHom β hβ n γ₂) (rootCoset β hβ) k₀
    rw [lampAut_single, lampAut_single] at hbase
    exact (show Commute _ _ from hbase).map
      (inl : Lamp K₀ (Cosets β hβ) →* WreathV (K := K₀) β hβ)

/-- The collapse commutator of the root lamp is the lamp difference of the root
with its translate. -/
theorem commutator_rootLamp_eq_lampDiff (n : ℕ) (γ : Γ₀) (k₀ : K₀) :
    ⁅(inr (levelHom β hβ n γ) : WreathV (K := K₀) β hβ), rootLamp β hβ k₀⁆
      = lampDiff β hβ (levelHom β hβ n γ • rootCoset β hβ)
          (rootCoset β hβ) k₀ := by
  rw [commutatorElement_def, conj_rootLamp, rootLamp, ← map_inv, ← map_mul]
  rfl

/-! ## Every level, then every equal-height pair -/

include hβ in
/-- **One level.**  The lamp difference between the root coset and any of its
level-`n` translates lies in the literal MF radical. -/
theorem lampDiff_level_mem_actualCoronaMFResidual
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k₀ : K₀} (hk2 : k₀ * k₀ = 1)
    (n : ℕ) (γ : Γ₀) :
    lampDiff β hβ (levelHom β hβ n γ • rootCoset β hβ) (rootCoset β hβ) k₀
      ∈ actualCoronaMFResidual (WreathV (K := K₀) β hβ) := by
  refine involutiveCollapseDefect_le_actualCoronaMFResidual
    (levelSub_hasKazhdanPropertyT β hβ hΓ n)
    (fun _ hw => wreathT_pow_compress β hβ hw) ?_
  rw [involutiveCollapseDefect, ← commutator_rootLamp_eq_lampDiff]
  exact Subgroup.subset_normalClosure ⟨rootLamp β hβ k₀,
    isInvolutiveCompressionWitness_rootLamp β hβ hk2 n,
    inr (levelHom β hβ n γ), (mem_levelSub_iff β hβ).mpr ⟨γ, rfl⟩, rfl⟩

include hβ in
/-- **The whole telescope, at the root.**  Every element of the telescope is a
level element, so the difference between the root and any of its telescope
translates is invisible. -/
theorem lampDiff_telescope_mem_actualCoronaMFResidual
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k₀ : K₀} (hk2 : k₀ * k₀ = 1)
    (a : Telescope β hβ) :
    lampDiff β hβ ((inl a : Vertical β hβ) • rootCoset β hβ)
        (rootCoset β hβ) k₀
      ∈ actualCoronaMFResidual (WreathV (K := K₀) β hβ) := by
  induction a using Quotient.inductionOn with | h p =>
  obtain ⟨n, γ⟩ := p
  exact lampDiff_level_mem_actualCoronaMFResidual β hβ hΓ hk2 n γ

include hβ in
/-- **Translated.**  The invisible differences are those of a site with a
telescope translate of it, anywhere in the coset space. -/
theorem lampDiff_translate_mem_actualCoronaMFResidual
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k₀ : K₀} (hk2 : k₀ * k₀ = 1)
    (g : Vertical β hβ) (a : Telescope β hβ) :
    lampDiff β hβ ((g * inl a) • rootCoset β hβ) (g • rootCoset β hβ) k₀
      ∈ actualCoronaMFResidual (WreathV (K := K₀) β hβ) := by
  have hconj := (inferInstance :
      (actualCoronaMFResidual (WreathV (K := K₀) β hβ)).Normal).conj_mem _
    (lampDiff_telescope_mem_actualCoronaMFResidual β hβ hΓ hk2 a) (inr g)
  rwa [conj_lampDiff, ← mul_smul] at hconj

include hβ in
/-- **Sections 37 and 47, in full.**  Two sites of equal height differ by an
element of the telescope, and their lamp difference is invisible to every
corona representation.  This is the lamp-collapse kernel `ker Φ∞`, and the
inclusion `R_K ≤ Res_MF` is unconditional. -/
theorem lampDiff_mem_actualCoronaMFResidual_of_rightHom_eq
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k₀ : K₀} (hk2 : k₀ * k₀ = 1)
    {v w : Vertical β hβ} (h : rightHom v = rightHom w) :
    lampDiff β hβ (v • rootCoset β hβ) (w • rootCoset β hβ) k₀
      ∈ actualCoronaMFResidual (WreathV (K := K₀) β hβ) := by
  have hker : v⁻¹ * w ∈ (rightHom : Vertical β hβ →* Multiplicative ℤ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom] at hker
  obtain ⟨a, ha⟩ := hker
  have hw : w = v * inl a := by rw [ha]; group
  have hmem := lampDiff_translate_mem_actualCoronaMFResidual β hβ hΓ hk2 v a
  rw [← hw] at hmem
  have hinv := (actualCoronaMFResidual (WreathV (K := K₀) β hβ)).inv_mem hmem
  rwa [lampDiff_inv] at hinv

/-! ## The radical it generates -/

/-- The differences of a lamp value between two sites of equal height. -/
def equalHeightDiffs (k₀ : K₀) : Set (WreathV (K := K₀) β hβ) :=
  {z | ∃ v w : Vertical β hβ, rightHom v = rightHom w ∧
    z = lampDiff β hβ (v • rootCoset β hβ) (w • rootCoset β hβ) k₀}

/-- **The telescope radical `R_K`.**  The normal subgroup generated by all
equal-height lamp differences: the kernel of the pushforward of the lamp base
along the height map. -/
def telescopeRadical (k₀ : K₀) : Subgroup (WreathV (K := K₀) β hβ) :=
  Subgroup.normalClosure (equalHeightDiffs β hβ k₀)

instance telescopeRadical_normal (k₀ : K₀) :
    (telescopeRadical β hβ k₀).Normal :=
  Subgroup.normalClosure_normal

include hβ in
/-- **`R_K ≤ Res_MF`.**  Unconditionally: property `(T)` of the base and the
HNN relation are the only inputs. -/
theorem telescopeRadical_le_actualCoronaMFResidual
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k₀ : K₀} (hk2 : k₀ * k₀ = 1) :
    telescopeRadical β hβ k₀
      ≤ actualCoronaMFResidual (WreathV (K := K₀) β hβ) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨v, w, h, rfl⟩
  exact lampDiff_mem_actualCoronaMFResidual_of_rightHom_eq β hβ hΓ hk2 h

include hβ in
/-- **The exact radical.**  When the visible quotient is MF, the MF radical of
the wreath product is exactly the telescope radical. -/
theorem actualCoronaMFResidual_eq_telescopeRadical
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k₀ : K₀} (hk2 : k₀ * k₀ = 1)
    (hquot : IsCDEOperatorMF
      (WreathV (K := K₀) β hβ ⧸ telescopeRadical β hβ k₀)) :
    actualCoronaMFResidual (WreathV (K := K₀) β hβ)
      = telescopeRadical β hβ k₀ :=
  actualCoronaMFResidual_eq_of_le_and_quotient_isCDEOperatorMF _
    (telescopeRadical_le_actualCoronaMFResidual β hβ hΓ hk2) hquot

include hβ in
/-- The first-stage radical is part of it: a base move keeps the height. -/
theorem stageRadical_le_telescopeRadical (k₀ : K₀) :
    stageRadical β hβ k₀ ≤ telescopeRadical β hβ k₀ := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨g, γ, rfl⟩
  refine Subgroup.subset_normalClosure
    ⟨g * iotaVertical β hβ γ * tVertical β hβ, g * tVertical β hβ, ?_, ?_⟩
  · have hι : (rightHom : Vertical β hβ →* Multiplicative ℤ)
        (iotaVertical β hβ γ) = 1 := rightHom_inl _
    simp [map_mul, hι]
  · rw [tSite, ← mul_smul, ← mul_smul]

end MarkedCompression
end GroupApproximation
