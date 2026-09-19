import GroupApproximation.Computability.BooneGroupTower
import GroupApproximation.Computability.BooneGroupMachineIndex

/-!
# S5b: the halting subgroup is good at every quadruple

`BooneGroupMachineIndex` (S5a) computes both sides of a quadruple as the two
images of **one and the same** parameter set:

* `twSub_halting_inf_Gsub_src` --- `T_M ⊓ G_{ab}^{MM}` is `twSub` of the image
  of `haltParams` under `embIdx a b M M`;
* `twSub_halting_inf_Gsub_right` --- `T_M ⊓ G_{c0}^{M²,1}` is `twSub` of the
  image of the *same* `haltParams` under `embIdx c 0 M² 1`.

`twSub_map_emb` says `emb` carries `twSub` of a set to `twSub` of its image.
Composing the three gives Simpson's Definition 2 for `T_M` --- goodness --- with
no computation left to do, and `liftedSubgroup_inf_range` (S4) then applies.
-/

namespace GroupApproximation
namespace BooneGroup

open Base MachineIndex

variable (mm : ModularMachine)

/-- **Goodness of the halting subgroup at a right-moving quadruple.**  This is
Simpson's Definition 2 for `T_M`, and it is exactly S5a's two computations read
through `emb`. -/
theorem good_twSub_halting_right {a b c : ℕ} (ha : a < mm.size) (hb : b < mm.size)
    (hq : mm.quad a b = some (c, true)) (hM : (mm.size : ℤ) ≠ 0) :
    Good (twSub mm.haltingSetZ)
      (quadEquiv (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM) := by
  have hM2 : ((mm.size : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 hM
  have he₁ : Function.Injective (emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ)) :=
    emb_injective hM hM
  have he₂ : Function.Injective (emb (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1) :=
    emb_injective hM2 one_ne_zero
  constructor
  · rintro x hx
    obtain ⟨y, hy⟩ := x.2
    have hsym : (MonoidHom.ofInjective he₁).symm x = y := by
      apply (MonoidHom.ofInjective he₁).injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext hy.symm
    have h1 : emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ) y ∈
        twSub mm.haltingSetZ ⊓ Gsub (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ) := by
      rw [hy]
      exact ⟨hx, x.2⟩
    rw [twSub_halting_inf_Gsub_src mm a b] at h1
    have h2 : y ∈ twSub (haltParams mm a b) :=
      (emb_mem_twSub_iff hM hM _ y).mp h1
    have h3 : emb (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1 y ∈
        twSub ((embIdx (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1) '' haltParams mm a b) :=
      (emb_mem_twSub_iff hM2 one_ne_zero _ y).mpr h2
    rw [← twSub_halting_inf_Gsub_right mm ha hb hq] at h3
    have h4 : ((quadEquiv (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM x : _) : BaseGroup)
        = emb (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1
            ((MonoidHom.ofInjective he₁).symm x) := rfl
    rw [h4, hsym]
    exact h3.1
  · rintro z hz
    obtain ⟨y, hy⟩ := z.2
    have hsym : (MonoidHom.ofInjective he₂).symm z = y := by
      apply (MonoidHom.ofInjective he₂).injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext hy.symm
    have h1 : emb (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1 y ∈
        twSub mm.haltingSetZ ⊓ Gsub (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1 := by
      rw [hy]
      exact ⟨hz, z.2⟩
    rw [twSub_halting_inf_Gsub_right mm ha hb hq] at h1
    have h2 : y ∈ twSub (haltParams mm a b) :=
      (emb_mem_twSub_iff hM2 one_ne_zero _ y).mp h1
    have h3 : emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ) y ∈
        twSub ((embIdx (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ))
          '' haltParams mm a b) :=
      (emb_mem_twSub_iff hM hM _ y).mpr h2
    rw [← twSub_halting_inf_Gsub_src mm a b] at h3
    have h4 : (((quadEquiv (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM).symm z : _)
        : BaseGroup) = emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ)
            ((MonoidHom.ofInjective he₂).symm z) := rfl
    rw [h4, hsym]
    exact h3.1

/-- **Goodness of the halting subgroup at a left-moving quadruple.**  This is
Simpson's Definition 2 for `T_M`, and it is exactly S5a's two computations read
through `emb`. -/
theorem good_twSub_halting_left {a b c : ℕ} (ha : a < mm.size) (hb : b < mm.size)
    (hq : mm.quad a b = some (c, false)) (hM : (mm.size : ℤ) ≠ 0) :
    Good (twSub mm.haltingSetZ)
      (quadEquivLeft (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM) := by
  have hM2 : ((mm.size : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 hM
  have he₁ : Function.Injective (emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ)) :=
    emb_injective hM hM
  have he₂ : Function.Injective (emb 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2)) :=
    emb_injective one_ne_zero hM2
  constructor
  · rintro x hx
    obtain ⟨y, hy⟩ := x.2
    have hsym : (MonoidHom.ofInjective he₁).symm x = y := by
      apply (MonoidHom.ofInjective he₁).injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext hy.symm
    have h1 : emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ) y ∈
        twSub mm.haltingSetZ ⊓ Gsub (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ) := by
      rw [hy]
      exact ⟨hx, x.2⟩
    rw [twSub_halting_inf_Gsub_src mm a b] at h1
    have h2 : y ∈ twSub (haltParams mm a b) :=
      (emb_mem_twSub_iff hM hM _ y).mp h1
    have h3 : emb 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2) y ∈
        twSub ((embIdx 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2)) '' haltParams mm a b) :=
      (emb_mem_twSub_iff one_ne_zero hM2 _ y).mpr h2
    rw [← twSub_halting_inf_Gsub_left mm ha hb hq] at h3
    have h4 : ((quadEquivLeft (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM x : _) : BaseGroup)
        = emb 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2)
            ((MonoidHom.ofInjective he₁).symm x) := rfl
    rw [h4, hsym]
    exact h3.1
  · rintro z hz
    obtain ⟨y, hy⟩ := z.2
    have hsym : (MonoidHom.ofInjective he₂).symm z = y := by
      apply (MonoidHom.ofInjective he₂).injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext hy.symm
    have h1 : emb 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2) y ∈
        twSub mm.haltingSetZ ⊓ Gsub 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2) := by
      rw [hy]
      exact ⟨hz, z.2⟩
    rw [twSub_halting_inf_Gsub_left mm ha hb hq] at h1
    have h2 : y ∈ twSub (haltParams mm a b) :=
      (emb_mem_twSub_iff one_ne_zero hM2 _ y).mp h1
    have h3 : emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ) y ∈
        twSub ((embIdx (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ))
          '' haltParams mm a b) :=
      (emb_mem_twSub_iff hM hM _ y).mpr h2
    rw [← twSub_halting_inf_Gsub_src mm a b] at h3
    have h4 : (((quadEquivLeft (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM).symm z : _)
        : BaseGroup) = emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ)
            ((MonoidHom.ofInjective he₂).symm z) := rfl
    rw [h4, hsym]
    exact h3.1

/-- **S5b at a quadruple.**  Feeding goodness into S4: inside the extension that
adjoins the stable letter for this quadruple, the elements of `T_M'` lying in the
base group are exactly those of `T_M`.

This is the statement Simpson's Lemma 7 (S6) consumes. -/
theorem twSub_halting_liftedSubgroup_inf_right {a b c : ℕ} (ha : a < mm.size)
    (hb : b < mm.size) (hq : mm.quad a b = some (c, true))
    (hM : (mm.size : ℤ) ≠ 0) :
    liftedSubgroup (quadEquiv (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM)
        (twSub mm.haltingSetZ) ⊓
      (HNNExtension.of :
        BaseGroup →* HNNExtension BaseGroup
          (Gsub (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ))
          (Gsub (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1)
          (quadEquiv (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM)).range
      = (twSub mm.haltingSetZ).map HNNExtension.of :=
  liftedSubgroup_inf_range _ (good_twSub_halting_right mm ha hb hq hM)

/-- **S5b at a left-moving quadruple.** -/
theorem twSub_halting_liftedSubgroup_inf_left {a b c : ℕ} (ha : a < mm.size)
    (hb : b < mm.size) (hq : mm.quad a b = some (c, false))
    (hM : (mm.size : ℤ) ≠ 0) :
    liftedSubgroup (quadEquivLeft (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM)
        (twSub mm.haltingSetZ) ⊓
      (HNNExtension.of :
        BaseGroup →* HNNExtension BaseGroup
          (Gsub (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ))
          (Gsub 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2))
          (quadEquivLeft (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM)).range
      = (twSub mm.haltingSetZ).map HNNExtension.of :=
  liftedSubgroup_inf_range _ (good_twSub_halting_left mm ha hb hq hM)

/-! ## S6's inductive step

Simpson's Lemma 7 is an induction along a halting computation whose step is the
displayed computation `rᵢ⁻¹ t(α,β) rᵢ = t(α₁,β₁)`.  At the level of the tower
that step is just the defining relation of the HNN extension, read through
`quadEquiv`: the stable letter conjugates the image of `emb a b M M` onto the
image of `emb c 0 M² 1`, which is exactly how `quadEquiv` was defined. -/

/-- **The step of Simpson's Lemma 7.**  The stable letter attached to a
right-moving quadruple carries the source embedding to the target embedding. -/
theorem stable_conj_emb_right (a b c M : ℤ) (hM : M ≠ 0) (g : BaseGroup) :
    (HNNExtension.of (emb c 0 (M ^ 2) 1 g) :
        HNNExtension BaseGroup (Gsub a b M M) (Gsub c 0 (M ^ 2) 1)
          (quadEquiv a b c M hM))
      = HNNExtension.t * HNNExtension.of (emb a b M M g) * HNNExtension.t⁻¹ := by
  have he₁ : Function.Injective (emb a b M M) := emb_injective hM hM
  have hx : (emb a b M M g) ∈ Gsub a b M M := ⟨g, rfl⟩
  have hsym : (MonoidHom.ofInjective he₁).symm ⟨emb a b M M g, hx⟩ = g := by
    apply (MonoidHom.ofInjective he₁).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hcoe : ((quadEquiv a b c M hM ⟨emb a b M M g, hx⟩ : _) : BaseGroup)
      = emb c 0 (M ^ 2) 1 g := by
    show emb c 0 (M ^ 2) 1 ((MonoidHom.ofInjective he₁).symm ⟨emb a b M M g, hx⟩) = _
    rw [hsym]
  have h := HNNExtension.equiv_eq_conj (φ := quadEquiv a b c M hM)
    ⟨emb a b M M g, hx⟩
  rw [hcoe] at h
  exact h

/-- The same for a left-moving quadruple. -/
theorem stable_conj_emb_left (a b c M : ℤ) (hM : M ≠ 0) (g : BaseGroup) :
    (HNNExtension.of (emb 0 c 1 (M ^ 2) g) :
        HNNExtension BaseGroup (Gsub a b M M) (Gsub 0 c 1 (M ^ 2))
          (quadEquivLeft a b c M hM))
      = HNNExtension.t * HNNExtension.of (emb a b M M g) * HNNExtension.t⁻¹ := by
  have he₁ : Function.Injective (emb a b M M) := emb_injective hM hM
  have hx : (emb a b M M g) ∈ Gsub a b M M := ⟨g, rfl⟩
  have hsym : (MonoidHom.ofInjective he₁).symm ⟨emb a b M M g, hx⟩ = g := by
    apply (MonoidHom.ofInjective he₁).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hcoe : ((quadEquivLeft a b c M hM ⟨emb a b M M g, hx⟩ : _) : BaseGroup)
      = emb 0 c 1 (M ^ 2) g := by
    show emb 0 c 1 (M ^ 2) ((MonoidHom.ofInjective he₁).symm ⟨emb a b M M g, hx⟩) = _
    rw [hsym]
  have h := HNNExtension.equiv_eq_conj (φ := quadEquivLeft a b c M hM)
    ⟨emb a b M M g, hx⟩
  rw [hcoe] at h
  exact h

/-- **Lemma 7's step, on basis elements.**  The stable letter carries the basis
element at `embIdx a b M M p` to the one at `embIdx c 0 M² 1 p`. -/
theorem stable_conj_tw_right (a b c M : ℤ) (hM : M ≠ 0) (p : ℤ × ℤ) :
    (HNNExtension.of (tw (embIdx c 0 (M ^ 2) 1 p)) :
        HNNExtension BaseGroup (Gsub a b M M) (Gsub c 0 (M ^ 2) 1)
          (quadEquiv a b c M hM))
      = HNNExtension.t * HNNExtension.of (tw (embIdx a b M M p)) *
          HNNExtension.t⁻¹ := by
  rw [← emb_tw, ← emb_tw]
  exact stable_conj_emb_right a b c M hM (tw p)

/-- The same for a left-moving quadruple. -/
theorem stable_conj_tw_left (a b c M : ℤ) (hM : M ≠ 0) (p : ℤ × ℤ) :
    (HNNExtension.of (tw (embIdx 0 c 1 (M ^ 2) p)) :
        HNNExtension BaseGroup (Gsub a b M M) (Gsub 0 c 1 (M ^ 2))
          (quadEquivLeft a b c M hM))
      = HNNExtension.t * HNNExtension.of (tw (embIdx a b M M p)) *
          HNNExtension.t⁻¹ := by
  rw [← emb_tw, ← emb_tw]
  exact stable_conj_emb_left a b c M hM (tw p)

/-- **One step of Lemma 7's induction, at one level.**  If the basis element on
the target side of a quadruple lies in a subgroup containing the stable letter,
so does the one on the source side --- they differ by conjugation. -/
theorem of_tw_mem_of_target_right (a b c M : ℤ) (hM : M ≠ 0) (p : ℤ × ℤ)
    (A : Subgroup BaseGroup)
    (h : (HNNExtension.of (tw (embIdx c 0 (M ^ 2) 1 p)) :
            HNNExtension BaseGroup (Gsub a b M M) (Gsub c 0 (M ^ 2) 1)
              (quadEquiv a b c M hM))
          ∈ liftedSubgroup (quadEquiv a b c M hM) A) :
    (HNNExtension.of (tw (embIdx a b M M p)) :
        HNNExtension BaseGroup (Gsub a b M M) (Gsub c 0 (M ^ 2) 1)
          (quadEquiv a b c M hM))
      ∈ liftedSubgroup (quadEquiv a b c M hM) A := by
  have ht := t_mem_liftedSubgroup (quadEquiv a b c M hM) A
  have hc := stable_conj_tw_right a b c M hM p
  have hrw : (HNNExtension.of (tw (embIdx a b M M p)) :
      HNNExtension BaseGroup (Gsub a b M M) (Gsub c 0 (M ^ 2) 1)
        (quadEquiv a b c M hM))
      = HNNExtension.t⁻¹ *
          HNNExtension.of (tw (embIdx c 0 (M ^ 2) 1 p)) * HNNExtension.t := by
    rw [hc]
    group
  rw [hrw]
  exact mul_mem (mul_mem (inv_mem ht) h) ht

/-! ### The machine step, in the tower's index coordinates

A configuration `(m,n)` is `embIdx a b M M (u,v)` with `a,b` its residues and
`u,v` its quotients --- that is the division algorithm.  A right-moving step
sends it to `embIdx c 0 M² 1 (u,v)`, the *same* `(u,v)`.  That is why one
stable letter serves the whole residue class, and it is what lets the induction
use `of_tw_mem_of_target_right`. -/

theorem coe_eq_lo_add_hi (n : ℕ) :
    (n : ℤ) = (mm.lo n : ℤ) + (mm.hi n : ℤ) * (mm.size : ℤ) := by
  have h : (n % mm.size) + mm.size * (n / mm.size) = n := Nat.mod_add_div n mm.size
  have h' : ((n % mm.size : ℕ) : ℤ) + (mm.size : ℤ) * ((n / mm.size : ℕ) : ℤ)
      = (n : ℤ) := by exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) h
  show (n : ℤ) = ((n % mm.size : ℕ) : ℤ) + ((n / mm.size : ℕ) : ℤ) * (mm.size : ℤ)
  linarith [h']

/-- A configuration sits at the index the source embedding assigns to its
quotients. -/
theorem coe_eq_embIdx_src (p : ℕ × ℕ) :
    ((p.1 : ℤ), (p.2 : ℤ))
      = embIdx (mm.lo p.1 : ℤ) (mm.lo p.2 : ℤ) (mm.size : ℤ) (mm.size : ℤ)
          ((mm.hi p.1 : ℤ), (mm.hi p.2 : ℤ)) := by
  simp only [embIdx, Prod.mk.injEq]
  exact ⟨coe_eq_lo_add_hi mm p.1, coe_eq_lo_add_hi mm p.2⟩

/-- A right-moving step lands at the index the target embedding assigns to the
same quotients. -/
theorem step_right_eq_embIdx (p : ℕ × ℕ) (c : ℕ) :
    (((mm.hi p.1 * mm.size ^ 2 + c : ℕ) : ℤ), ((mm.hi p.2 : ℕ) : ℤ))
      = embIdx (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1
          ((mm.hi p.1 : ℤ), (mm.hi p.2 : ℤ)) := by
  simp only [embIdx, Prod.mk.injEq]
  constructor
  · push_cast
    ring
  · ring

theorem step_left_eq_embIdx (p : ℕ × ℕ) (c : ℕ) :
    (((mm.hi p.1 : ℕ) : ℤ), ((mm.hi p.2 * mm.size ^ 2 + c : ℕ) : ℤ))
      = embIdx 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2)
          ((mm.hi p.1 : ℤ), (mm.hi p.2 : ℤ)) := by
  simp only [embIdx, Prod.mk.injEq]
  constructor
  · ring
  · push_cast
    ring

/-! ### The step of Lemma 7, at the top of the tower

`stable_conj_tw_right` is the defining relation at one level.  To use it in an
induction that changes quadruple at every step, it has to be read in the group
at the top: `liftUp` carries the whole level up, and `liftUp_t_mem_towerTSub`
says the stable letter it carries lands in `⟨t⟩'`. -/

/-- What a right-moving quadruple's identification does to a basis element. -/
theorem quadEquiv_coe_tw (a b c M : ℤ) (hM : M ≠ 0) (p : ℤ × ℤ)
    (h : tw (embIdx a b M M p) ∈ Gsub a b M M) :
    ((quadEquiv a b c M hM ⟨tw (embIdx a b M M p), h⟩ : Gsub c 0 (M ^ 2) 1) : BaseGroup)
      = tw (embIdx c 0 (M ^ 2) 1 p) := by
  have he₁ : Function.Injective (emb a b M M) := emb_injective hM hM
  have hsym : (MonoidHom.ofInjective he₁).symm ⟨tw (embIdx a b M M p), h⟩ = tw p := by
    apply (MonoidHom.ofInjective he₁).injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext (emb_tw a b M M p).symm
  show emb c 0 (M ^ 2) 1
      ((MonoidHom.ofInjective he₁).symm ⟨tw (embIdx a b M M p), h⟩) = _
  rw [hsym, emb_tw]

/-- The same for a left-moving quadruple. -/
theorem quadEquivLeft_coe_tw (a b c M : ℤ) (hM : M ≠ 0) (p : ℤ × ℤ)
    (h : tw (embIdx a b M M p) ∈ Gsub a b M M) :
    ((quadEquivLeft a b c M hM ⟨tw (embIdx a b M M p), h⟩ : Gsub 0 c 1 (M ^ 2)) :
        BaseGroup)
      = tw (embIdx 0 c 1 (M ^ 2) p) := by
  have he₁ : Function.Injective (emb a b M M) := emb_injective hM hM
  have hsym : (MonoidHom.ofInjective he₁).symm ⟨tw (embIdx a b M M p), h⟩ = tw p := by
    apply (MonoidHom.ofInjective he₁).injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext (emb_tw a b M M p).symm
  show emb 0 c 1 (M ^ 2)
      ((MonoidHom.ofInjective he₁).symm ⟨tw (embIdx a b M M p), h⟩) = _
  rw [hsym, emb_tw]

theorem tw_mem_Gsub_embIdx (a b M N : ℤ) (p : ℤ × ℤ) :
    tw (embIdx a b M N p) ∈ Gsub a b M N :=
  ⟨tw p, emb_tw a b M N p⟩

/-- **Lemma 7's step, at one level of the tower over an arbitrary stage.** -/
theorem of_ι_tw_conj_right (l : List Identification) (a b c M : ℤ) (hM : M ≠ 0)
    (p : ℤ × ℤ) :
    (HNNExtension.of ((tower l).ι (tw (embIdx c 0 (M ^ 2) 1 p))) :
        (tower (quadIdentification a b c M hM :: l)).Carrier)
      = HNNExtension.t * HNNExtension.of ((tower l).ι (tw (embIdx a b M M p))) *
          HNNExtension.t⁻¹ := by
  have h := of_ι_conj l (quadEquiv a b c M hM) (tw (embIdx a b M M p))
    (tw_mem_Gsub_embIdx a b M M p)
  rwa [quadEquiv_coe_tw] at h

theorem of_ι_tw_conj_left (l : List Identification) (a b c M : ℤ) (hM : M ≠ 0)
    (p : ℤ × ℤ) :
    (HNNExtension.of ((tower l).ι (tw (embIdx 0 c 1 (M ^ 2) p))) :
        (tower (quadIdentificationLeft a b c M hM :: l)).Carrier)
      = HNNExtension.t * HNNExtension.of ((tower l).ι (tw (embIdx a b M M p))) *
          HNNExtension.t⁻¹ := by
  have h := of_ι_conj l (quadEquivLeft a b c M hM) (tw (embIdx a b M M p))
    (tw_mem_Gsub_embIdx a b M M p)
  rwa [quadEquivLeft_coe_tw] at h

/-- The same step, read in the group at the top of the tower. -/
theorem ι_tw_conj_top_right (l₁ l₂ : List Identification) (a b c M : ℤ) (hM : M ≠ 0)
    (p : ℤ × ℤ) :
    (tower (l₁ ++ quadIdentification a b c M hM :: l₂)).ι
        (tw (embIdx c 0 (M ^ 2) 1 p))
      = liftUp l₁ (quadIdentification a b c M hM :: l₂) HNNExtension.t *
          (tower (l₁ ++ quadIdentification a b c M hM :: l₂)).ι
            (tw (embIdx a b M M p)) *
          (liftUp l₁ (quadIdentification a b c M hM :: l₂) HNNExtension.t)⁻¹ := by
  rw [← liftUp_ι_apply l₁ (quadIdentification a b c M hM :: l₂)
        (tw (embIdx c 0 (M ^ 2) 1 p)),
    ← liftUp_ι_apply l₁ (quadIdentification a b c M hM :: l₂)
        (tw (embIdx a b M M p)),
    ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ (of_ι_tw_conj_right l₂ a b c M hM p)

theorem ι_tw_conj_top_left (l₁ l₂ : List Identification) (a b c M : ℤ) (hM : M ≠ 0)
    (p : ℤ × ℤ) :
    (tower (l₁ ++ quadIdentificationLeft a b c M hM :: l₂)).ι
        (tw (embIdx 0 c 1 (M ^ 2) p))
      = liftUp l₁ (quadIdentificationLeft a b c M hM :: l₂) HNNExtension.t *
          (tower (l₁ ++ quadIdentificationLeft a b c M hM :: l₂)).ι
            (tw (embIdx a b M M p)) *
          (liftUp l₁ (quadIdentificationLeft a b c M hM :: l₂) HNNExtension.t)⁻¹ := by
  rw [← liftUp_ι_apply l₁ (quadIdentificationLeft a b c M hM :: l₂)
        (tw (embIdx 0 c 1 (M ^ 2) p)),
    ← liftUp_ι_apply l₁ (quadIdentificationLeft a b c M hM :: l₂)
        (tw (embIdx a b M M p)),
    ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ (of_ι_tw_conj_left l₂ a b c M hM p)

/-- **One step of Lemma 7's induction, in the top group.**  If the target basis
element is in `⟨t⟩'`, so is the source one --- they differ by conjugation by the
stable letter of the quadruple's own level, which is itself in `⟨t⟩'`. -/
theorem ι_tw_mem_towerTSub_of_target_right {L : List Identification}
    {a b c M : ℤ} {hM : M ≠ 0} (hmem : quadIdentification a b c M hM ∈ L) (p : ℤ × ℤ)
    (h : (tower L).ι (tw (embIdx c 0 (M ^ 2) 1 p)) ∈ towerTSub L) :
    (tower L).ι (tw (embIdx a b M M p)) ∈ towerTSub L := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hmem
  have hX := liftUp_t_mem_towerTSub (Gsub a b M M) (Gsub c 0 (M ^ 2) 1)
    (quadEquiv a b c M hM) l₁ l₂
  have key : (tower (l₁ ++ quadIdentification a b c M hM :: l₂)).ι
        (tw (embIdx a b M M p))
      = (liftUp l₁ (quadIdentification a b c M hM :: l₂) HNNExtension.t)⁻¹ *
          (tower (l₁ ++ quadIdentification a b c M hM :: l₂)).ι
            (tw (embIdx c 0 (M ^ 2) 1 p)) *
          liftUp l₁ (quadIdentification a b c M hM :: l₂) HNNExtension.t := by
    rw [ι_tw_conj_top_right]
    group
  rw [key]
  exact mul_mem (mul_mem (inv_mem hX) h) hX

theorem ι_tw_mem_towerTSub_of_target_left {L : List Identification}
    {a b c M : ℤ} {hM : M ≠ 0} (hmem : quadIdentificationLeft a b c M hM ∈ L)
    (p : ℤ × ℤ)
    (h : (tower L).ι (tw (embIdx 0 c 1 (M ^ 2) p)) ∈ towerTSub L) :
    (tower L).ι (tw (embIdx a b M M p)) ∈ towerTSub L := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hmem
  have hX := liftUp_t_mem_towerTSub (Gsub a b M M) (Gsub 0 c 1 (M ^ 2))
    (quadEquivLeft a b c M hM) l₁ l₂
  have key : (tower (l₁ ++ quadIdentificationLeft a b c M hM :: l₂)).ι
        (tw (embIdx a b M M p))
      = (liftUp l₁ (quadIdentificationLeft a b c M hM :: l₂) HNNExtension.t)⁻¹ *
          (tower (l₁ ++ quadIdentificationLeft a b c M hM :: l₂)).ι
            (tw (embIdx 0 c 1 (M ^ 2) p)) *
          liftUp l₁ (quadIdentificationLeft a b c M hM :: l₂) HNNExtension.t := by
    rw [ι_tw_conj_top_left]
    group
  rw [key]
  exact mul_mem (mul_mem (inv_mem hX) h) hX

/-! ## `t` lies in the halting subgroup

The easy half of Lemma 7 needs only that `t` itself is in the base subgroup.  For
the halting subgroup that is `halts_zero_zero`: the configuration `(0,0)` halts,
in zero steps. -/

theorem tw_mem_twSub {S : Set (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ S) :
    tw p ∈ twSub S :=
  ⟨FreeGroup.of p, Subgroup.subset_closure ⟨p, hp, rfl⟩, rfl⟩

theorem tGen_mem_twSub_halting : tGen ∈ twSub mm.haltingSetZ :=
  tw_mem_twSub ⟨0, 0, by simp, mm.halts_zero_zero⟩

/-- **The easy half of Lemma 7, for a machine's tower.**  `⟨t⟩'` sits inside the
lift of the halting subgroup at every height. -/
theorem towerTSub_le_towerSub_halting (l : List Identification) :
    towerTSub l ≤ towerSub (twSub mm.haltingSetZ) l :=
  towerTSub_le_towerSub _ (tGen_mem_twSub_halting mm) l

/-! ## Simpson's Lemma 7

The induction runs along a halting computation, from the halting configuration
backwards.  At the base, `t(0,0) = t` is in `⟨t⟩'` by definition.  At each step
the machine's quadruple names a level of the tower, and the stable letter of
*that* level conjugates the configuration's basis element to its successor's;
since that letter is in `⟨t⟩'`, membership travels backwards along the
computation.  Which level to use is read off from the configuration by the
division algorithm --- `coe_eq_embIdx_src` and `step_*_eq_embIdx`. -/

/-- **Simpson's Lemma 7, the hard half, on basis elements.**  If a configuration
halts, its basis element lies in `⟨t⟩'`. -/
theorem ι_tw_mem_towerTSub_of_halts (hM : (mm.size : ℤ) ≠ 0) {p : ℕ × ℕ}
    (hp : mm.Halts p) :
    (tower (machineIdentifications mm hM)).ι (tw ((p.1 : ℤ), (p.2 : ℤ)))
      ∈ towerTSub (machineIdentifications mm hM) := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl =>
      rw [show ((((0, 0) : ℕ × ℕ).1 : ℤ), (((0, 0) : ℕ × ℕ).2 : ℤ))
          = ((0 : ℤ), (0 : ℤ)) by norm_num]
      exact ι_tGen_mem_towerTSub _
  | @head r s h' _ ih =>
      have hlo1 : mm.lo r.1 < mm.size := mm.lo_lt r.1
      have hlo2 : mm.lo r.2 < mm.size := mm.lo_lt r.2
      have h'' : mm.step (r.1, r.2) = some s := h'
      rcases hq : mm.quad (mm.lo r.1) (mm.lo r.2) with _ | ⟨c, dir⟩
      · rw [mm.step_eq_none hq] at h''
        exact absurd h'' (by simp)
      · rw [coe_eq_embIdx_src mm r]
        cases dir
        · have hs : s = (mm.hi r.1, mm.hi r.2 * mm.size ^ 2 + c) :=
            Option.some.inj (h''.symm.trans (mm.step_left hq))
          subst hs
          refine ι_tw_mem_towerTSub_of_target_left
            (quadIdentificationLeft_mem_machineIdentifications hlo1 hlo2 hq) _ ?_
          rw [← step_left_eq_embIdx mm r c]
          exact ih
        · have hs : s = (mm.hi r.1 * mm.size ^ 2 + c, mm.hi r.2) :=
            Option.some.inj (h''.symm.trans (mm.step_right hq))
          subst hs
          refine ι_tw_mem_towerTSub_of_target_right
            (quadIdentification_mem_machineIdentifications hlo1 hlo2 hq) _ ?_
          rw [← step_right_eq_embIdx mm r c]
          exact ih

theorem twSub_halting_le_comap (hM : (mm.size : ℤ) ≠ 0) :
    twSub mm.haltingSetZ ≤
      (towerTSub (machineIdentifications mm hM)).comap
        (tower (machineIdentifications mm hM)).ι := by
  rw [twSub_eq_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨m, n, rfl, hmn⟩ := hq
  exact ι_tw_mem_towerTSub_of_halts mm hM hmn

/-- **Simpson's Lemma 7.**  In `G'_M`, the lift of the halting subgroup is
exactly `⟨t⟩'`.  Both inclusions are now proved: the easy one from `(0,0)`
halting, the hard one by the induction along a halting computation. -/
theorem towerSub_halting_eq_towerTSub (hM : (mm.size : ℤ) ≠ 0) :
    towerSub (twSub mm.haltingSetZ) (machineIdentifications mm hM)
      = towerTSub (machineIdentifications mm hM) :=
  le_antisymm
    (towerSub_le_of_mem _ _ _ (fun _ ha => twSub_halting_le_comap mm hM ha)
      (hasLetters_towerTSub _))
    (towerTSub_le_towerSub_halting mm _)

/-! ## S7: the final group, and Simpson's Theorem 8

`G_M` is `G'_M` with one more stable letter `k`, both of whose associated
subgroups are `⟨t⟩'` and whose identification is the identity.  Britton's Lemma
for that single letter (`conj_t_eq_iff`) says `k` commutes with exactly the
elements of `⟨t⟩'`.  Lemma 7 identifies `⟨t⟩'` with the lift of `T_M`, S4
identifies the part of that lift lying in the base group with `T_M` itself, and
`tw_mem_twSub_iff` reads `T_M` back as the halting set.  Chaining the four gives
Theorem 8: `k` commutes with `t(α,β)` exactly when `(α,β)` halts. -/

/-- Every identification a machine contributes is good for `T_M`.  This is S5b,
read off the two shapes of quadruple. -/
theorem good_of_mem_machineIdentifications (hM : (mm.size : ℤ) ≠ 0)
    {q : Identification} (hq : q ∈ machineIdentifications mm hM) :
    Good (twSub mm.haltingSetZ) q.2.2 := by
  rw [machineIdentifications, List.mem_filterMap] at hq
  obtain ⟨pr, hpr, hval⟩ := hq
  obtain ⟨hb1, hb2⟩ := lt_of_mem_residuePairs hpr
  rcases hquad : mm.quad pr.1 pr.2 with _ | ⟨c, dir⟩
  · rw [hquad] at hval
    exact absurd hval (by simp)
  · rw [hquad] at hval
    have hval' := Option.some.inj hval
    cases dir
    · subst hval'
      exact good_twSub_halting_left mm hb1 hb2 hquad hM
    · subst hval'
      exact good_twSub_halting_right mm hb1 hb2 hquad hM

/-- **S4's hypothesis, discharged for a machine's tower.** -/
theorem goodTower_machine (hM : (mm.size : ℤ) ≠ 0) :
    GoodTower (twSub mm.haltingSetZ) (machineIdentifications mm hM) :=
  goodTower_of_forall_good _ _ fun _ hq => good_of_mem_machineIdentifications mm hM hq

/-- **Simpson's `G_M`.**  `G'_M` with `k` adjoined, commuting with `⟨t⟩'`. -/
noncomputable abbrev FinalGroup (mm : ModularMachine) (hM : (mm.size : ℤ) ≠ 0) : Type :=
  HNNExtension (tower (machineIdentifications mm hM)).Carrier
    (towerTSub (machineIdentifications mm hM))
    (towerTSub (machineIdentifications mm hM)) (MulEquiv.refl _)

/-- The generator `t(α,β)` of the base group, seen in `G_M`. -/
noncomputable def finalTw (mm : ModularMachine) (hM : (mm.size : ℤ) ≠ 0)
    (p : ℤ × ℤ) : FinalGroup mm hM :=
  HNNExtension.of ((tower (machineIdentifications mm hM)).ι (tw p))

/-- **Simpson's Theorem 8.**  In `G_M`, the stable letter `k` commutes with
`t(α,β)` exactly when the configuration `(α,β)` halts.  Everything on the left
is a word in the generators; everything on the right is a fact about the
machine. -/
theorem conj_k_finalTw_eq_iff (hM : (mm.size : ℤ) ≠ 0) (p : ℕ × ℕ) :
    (HNNExtension.t⁻¹ * finalTw mm hM ((p.1 : ℤ), (p.2 : ℤ)) * HNNExtension.t
        : FinalGroup mm hM)
      = finalTw mm hM ((p.1 : ℤ), (p.2 : ℤ)) ↔ mm.Halts p := by
  rw [finalTw, conj_t_eq_iff]
  constructor
  · intro h
    rw [← towerSub_halting_eq_towerTSub mm hM] at h
    have hS4 := towerSub_inf_range (twSub mm.haltingSetZ) _ (goodTower_machine mm hM)
    have hmem : (tower (machineIdentifications mm hM)).ι (tw ((p.1 : ℤ), (p.2 : ℤ)))
        ∈ (twSub mm.haltingSetZ).map (tower (machineIdentifications mm hM)).ι := by
      rw [← hS4]
      exact ⟨h, ⟨_, rfl⟩⟩
    obtain ⟨g, hg, hgeq⟩ := hmem
    rw [(tower (machineIdentifications mm hM)).ι_injective hgeq] at hg
    have hp : ((p.1 : ℤ), (p.2 : ℤ)) ∈ mm.haltingSetZ := tw_mem_twSub_iff.1 hg
    exact (mm.haltsZ_natCast p.1 p.2).1 hp
  · intro h
    exact ι_tw_mem_towerTSub_of_halts mm hM h

end BooneGroup
end GroupApproximation
