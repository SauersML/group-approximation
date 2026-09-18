import GroupApproximation.Manuscript.NonMFNotes.Full.TWW.SubgroupRegularModels
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCyclic.Cosets
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCyclic.InfiniteOrderShift

/-!
# Cyclic extension by a central element of infinite order modulo the subgroup

`non_mf_group_notes.tex`, proof of `thm:fixed-radical-membership`
(tex l. 1376--1378), cyclic extension step, case in which the extending element `k`
commutes with every element of `H` and no positive power of `k` lies in `H`.

Every `x ∈ H ⊔ ⟨k⟩` is then uniquely `a * k ^ p` with `a ∈ H` (`expo`, `hpart`), and
`H ⊔ ⟨k⟩ ≅ H × ℤ`. A model `π` of `H` on the test set of `H`-parts gives the model
`x ↦ shiftBlock p (π a)` on `ZMod (B + 1) × π.carrier`, where `B` bounds the exponents
occurring in the test set. Multiplicativity and star-compatibility are inherited from
`π`, and the exponent bound makes the traces of the non-trivial shifts vanish
(`isModelled_sup_zpowers_of_commute`). No amenability is used.
-/

namespace GroupApproximation.Full.TWWCyclic

open scoped Matrix
open scoped Matrix.Norms.L2Operator

variable {G : Type} [Group G] {H : Subgroup G} {k : G}

theorem eq_zero_of_zpow_mem (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H) {n : ℤ} (hn : k ^ n ∈ H) :
    n = 0 := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast] at hn
    by_contra hne
    have hm : 0 < m := by omega
    exact hinf m hm hn
  · rw [zpow_neg, zpow_natCast, inv_mem_iff] at hn
    by_contra hne
    have hm : 0 < m := by omega
    exact hinf m hm hn

theorem zpow_eq_of_mul_mem (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H) {a : G} (ha : a ∈ H)
    {p n : ℤ} (h : a * k ^ p * k ^ (-n) ∈ H) : n = p := by
  have h1 : a⁻¹ * (a * k ^ p * k ^ (-n)) ∈ H := H.mul_mem (H.inv_mem ha) h
  rw [mul_assoc, inv_mul_cancel_left, ← zpow_add] at h1
  have h2 := eq_zero_of_zpow_mem hinf h1
  omega

open scoped Classical in
/-- The exponent of `k` in `x = a * k ^ p` with `a ∈ H` (`0` if there is none). -/
noncomputable def expo (H : Subgroup G) (k x : G) : ℤ :=
  if h : ∃ n : ℤ, x * k ^ (-n) ∈ H then Classical.choose h else 0

theorem expo_eq (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H) {a : G} (ha : a ∈ H) (p : ℤ) :
    expo H k (a * k ^ p) = p := by
  have hex : ∃ n : ℤ, a * k ^ p * k ^ (-n) ∈ H := by
    refine ⟨p, ?_⟩
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
    exact ha
  rw [expo, dif_pos hex]
  exact zpow_eq_of_mul_mem hinf ha (Classical.choose_spec hex)

/-- The `H`-part `a` of `x = a * k ^ p`. -/
noncomputable def hpart (H : Subgroup G) (k x : G) : G :=
  x * k ^ (-expo H k x)

theorem hpart_eq (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H) {a : G} (ha : a ∈ H) (p : ℤ) :
    hpart H k (a * k ^ p) = a := by
  rw [hpart, expo_eq hinf ha p, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

theorem exists_mul_zpow_of_commute (hc : ∀ h ∈ H, k * h = h * k) {x : G}
    (hx : x ∈ H ⊔ Subgroup.zpowers k) : ∃ a ∈ H, ∃ p : ℤ, x = a * k ^ p := by
  have hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H := fun h hh => by
    rw [hc h hh, mul_inv_cancel_right]
    exact hh
  have hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H := fun h hh => by
    rw [mul_assoc, ← hc h hh, inv_mul_cancel_left]
    exact hh
  exact exists_mul_zpow_of_mem_sup hk hk' hx

theorem mul_zpow_mul_mul_zpow (hc : ∀ h ∈ H, k * h = h * k) (a : G) {b : G} (hb : b ∈ H)
    (p q : ℤ) : a * k ^ p * (b * k ^ q) = a * b * k ^ (p + q) := by
  have hcb : Commute k b := hc b hb
  rw [zpow_add]
  simp only [mul_assoc]
  rw [← mul_assoc (k ^ p) b, (hcb.zpow_left p).eq, mul_assoc]

theorem inv_mul_zpow (hc : ∀ h ∈ H, k * h = h * k) {a : G} (ha : a ∈ H) (p : ℤ) :
    (a * k ^ p)⁻¹ = a⁻¹ * k ^ (-p) := by
  have hca : Commute k a⁻¹ := hc a⁻¹ (H.inv_mem ha)
  rw [mul_inv_rev, ← zpow_neg]
  exact (hca.zpow_left (-p)).eq

open scoped Classical in
/-- The test set of `H`-parts. -/
noncomputable def testSet (H : Subgroup G) (k : G) (F : Finset G) : Finset G :=
  F.image (hpart H k)

theorem mem_testSet_of_eq (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H) {F : Finset G} {a : G}
    (ha : a ∈ H) {p : ℤ} (hx : a * k ^ p ∈ F) : a ∈ testSet H k F := by
  have h : hpart H k (a * k ^ p) ∈ testSet H k F := by
    rw [testSet]
    exact Finset.mem_image_of_mem _ hx
  rwa [hpart_eq hinf ha p] at h

theorem testSet_subset (hc : ∀ h ∈ H, k * h = h * k) (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H)
    {F : Finset G} (hF : ∀ x ∈ F, x ∈ H ⊔ Subgroup.zpowers k) :
    ∀ g ∈ testSet H k F, g ∈ H := by
  intro g hg
  rw [testSet, Finset.mem_image] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  obtain ⟨a, ha, p, rfl⟩ := exists_mul_zpow_of_commute hc (hF x hx)
  rw [hpart_eq hinf ha p]
  exact ha

variable {F' : Finset G} {ε : ℝ}

/-- The tower matrix of `x = a * k ^ p`: the shift by `p` tensored with `π a`. -/
noncomputable def towerMat (H : Subgroup G) (k : G) (B : ℕ)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) (x : G) :
    Matrix (ZMod (B + 1) × π.carrier) (ZMod (B + 1) × π.carrier) ℂ :=
  shiftBlock ((expo H k x : ℤ) : ZMod (B + 1)) (π.map (hpart H k x))

theorem towerMat_mul_zpow (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H) {B : ℕ}
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ))
    {a : G} (ha : a ∈ H) (p : ℤ) :
    towerMat H k B π (a * k ^ p) = shiftBlock ((p : ℤ) : ZMod (B + 1)) (π.map a) := by
  rw [towerMat, expo_eq hinf ha p, hpart_eq hinf ha p]

theorem card_tower {B : ℕ}
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) :
    Fintype.card (ZMod (B + 1) × π.carrier) = (B + 1) * Fintype.card π.carrier := by
  rw [Fintype.card_prod, ZMod.card]

theorem card_tower_pos {B : ℕ}
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) :
    0 < Fintype.card (ZMod (B + 1) × π.carrier) := by
  rw [card_tower π]
  exact Nat.mul_pos (Nat.succ_pos B) π.nonempty

/-! ## The model estimates -/

theorem norm_towerMat_le (hc : ∀ h ∈ H, k * h = h * k) (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H)
    {F : Finset G} {B : ℕ}
    (π : MFTraceRecognition.RegularCharacterModel G (testSet H k F) ε fun _ : G => (1 : ℝ))
    {x : G} (hxS : x ∈ H ⊔ Subgroup.zpowers k) (hx : x ∈ F) :
    ‖towerMat H k B π x‖ ≤ 1 := by
  obtain ⟨a, ha, p, rfl⟩ := exists_mul_zpow_of_commute hc hxS
  rw [towerMat_mul_zpow hinf π ha p]
  exact norm_shiftBlock_le _ zero_le_one (π.bounded a (mem_testSet_of_eq hinf ha hx))

theorem norm_towerMat_mul_sub_le (hc : ∀ h ∈ H, k * h = h * k)
    (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H)
    {F : Finset G} {B : ℕ}
    (π : MFTraceRecognition.RegularCharacterModel G (testSet H k F) ε fun _ : G => (1 : ℝ))
    (hε : 0 < ε) {x y : G} (hxS : x ∈ H ⊔ Subgroup.zpowers k)
    (hyS : y ∈ H ⊔ Subgroup.zpowers k) (hx : x ∈ F) (hy : y ∈ F) :
    ‖towerMat H k B π (x * y) - towerMat H k B π x * towerMat H k B π y‖ ≤ ε := by
  obtain ⟨a, ha, p, rfl⟩ := exists_mul_zpow_of_commute hc hxS
  obtain ⟨b, hb, q, rfl⟩ := exists_mul_zpow_of_commute hc hyS
  rw [mul_zpow_mul_mul_zpow hc a hb p q, towerMat_mul_zpow hinf π (H.mul_mem ha hb) (p + q),
    towerMat_mul_zpow hinf π ha p, towerMat_mul_zpow hinf π hb q, shiftBlock_mul,
    Int.cast_add, shiftBlock_sub]
  exact norm_shiftBlock_le _ hε.le
    (π.multiplicative a (mem_testSet_of_eq hinf ha hx) b (mem_testSet_of_eq hinf hb hy))

theorem norm_towerMat_inv_sub_le (hc : ∀ h ∈ H, k * h = h * k)
    (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H)
    {F : Finset G} {B : ℕ}
    (π : MFTraceRecognition.RegularCharacterModel G (testSet H k F) ε fun _ : G => (1 : ℝ))
    (hε : 0 < ε) {x : G} (hxS : x ∈ H ⊔ Subgroup.zpowers k) (hx : x ∈ F) :
    ‖towerMat H k B π x⁻¹ - (towerMat H k B π x)ᴴ‖ ≤ ε := by
  obtain ⟨a, ha, p, rfl⟩ := exists_mul_zpow_of_commute hc hxS
  rw [inv_mul_zpow hc ha p, towerMat_mul_zpow hinf π (H.inv_mem ha) (-p),
    towerMat_mul_zpow hinf π ha p, shiftBlock_conjTranspose, Int.cast_neg, shiftBlock_sub]
  exact norm_shiftBlock_le _ hε.le (π.star_compatible a (mem_testSet_of_eq hinf ha hx))

theorem norm_trace_towerMat_one_sub_le (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H)
    {F : Finset G} {B : ℕ}
    (π : MFTraceRecognition.RegularCharacterModel G (testSet H k F) ε fun _ : G => (1 : ℝ))
    (h1 : (1 : G) ∈ F) :
    ‖Matrix.trace (towerMat H k B π 1) / (Fintype.card (ZMod (B + 1) × π.carrier) : ℂ) - 1‖
      ≤ ε := by
  have h1' : (1 : G) * k ^ (0 : ℤ) ∈ F := by
    rw [zpow_zero, mul_one]
    exact h1
  have hone : towerMat H k B π 1 = shiftBlock (0 : ZMod (B + 1)) (π.map 1) := by
    have h := towerMat_mul_zpow (B := B) hinf π H.one_mem 0
    rwa [zpow_zero, mul_one, Int.cast_zero] at h
  have hN0 : ((B + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero B)
  rw [hone, trace_shiftBlock_zero, card_tower π, Nat.cast_mul, mul_div_mul_left _ _ hN0]
  have hmem : (1 : G) ∈ testSet H k F := mem_testSet_of_eq hinf H.one_mem h1'
  exact π.trace_correct_one hmem

theorem norm_trace_towerMat_le (hc : ∀ h ∈ H, k * h = h * k)
    (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H) {F : Finset G} {B : ℕ}
    (π : MFTraceRecognition.RegularCharacterModel G (testSet H k F) ε fun _ : G => (1 : ℝ))
    (hε : 0 < ε) {x : G} (hxS : x ∈ H ⊔ Subgroup.zpowers k) (hx : x ∈ F)
    (hB : (expo H k x).natAbs ≤ B) (hne : x ≠ 1) :
    ‖Matrix.trace (towerMat H k B π x) / (Fintype.card (ZMod (B + 1) × π.carrier) : ℂ)‖
      ≤ ε := by
  obtain ⟨a, ha, p, rfl⟩ := exists_mul_zpow_of_commute hc hxS
  rw [expo_eq hinf ha p] at hB
  rw [towerMat_mul_zpow hinf π ha p]
  by_cases hp0 : ((p : ℤ) : ZMod (B + 1)) = 0
  · have hdvd : ((B + 1 : ℕ) : ℤ) ∣ p := (ZMod.intCast_zmod_eq_zero_iff_dvd p (B + 1)).mp hp0
    have hlt : p.natAbs < ((B + 1 : ℕ) : ℤ).natAbs := by
      rw [Int.natAbs_natCast]
      exact Nat.lt_succ_of_le hB
    have hp : p = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hlt
    subst hp
    have hne' : a ≠ 1 := by
      rwa [zpow_zero, mul_one] at hne
    have hN0 : ((B + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero B)
    rw [Int.cast_zero, trace_shiftBlock_zero, card_tower π, Nat.cast_mul,
      mul_div_mul_left _ _ hN0]
    exact π.trace_correct_ne a (mem_testSet_of_eq hinf ha hx) hne'
  · rw [trace_shiftBlock_of_ne hp0, zero_div, norm_zero]
    exact hε.le

/-! ## The model and the extension step -/

/-- **The tower model.** A model of the regular character on the `H`-parts of `F`
gives a model on `F`, when `k` centralizes `H`, has infinite order modulo `H`, and
`B` bounds the exponents of the elements of `F`. -/
noncomputable def towerModel (hc : ∀ h ∈ H, k * h = h * k)
    (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H) {F : Finset G}
    (hF : ∀ x ∈ F, x ∈ H ⊔ Subgroup.zpowers k) (hε : 0 < ε) (B : ℕ)
    (hB : ∀ x ∈ F, (expo H k x).natAbs ≤ B)
    (π : MFTraceRecognition.RegularCharacterModel G (testSet H k F) ε fun _ : G => (1 : ℝ)) :
    MFTraceRecognition.RegularCharacterModel G F ε fun _ : G => (1 : ℝ) where
  carrier := ⟨ZMod (B + 1) × π.carrier, inferInstance, inferInstance⟩
  nonempty := card_tower_pos (B := B) π
  map := towerMat H k B π
  bounded := fun x hx => norm_towerMat_le (B := B) hc hinf π (hF x hx) hx
  multiplicative := fun x hx y hy =>
    norm_towerMat_mul_sub_le (B := B) hc hinf π hε (hF x hx) (hF y hy) hx hy
  star_compatible := fun x hx =>
    norm_towerMat_inv_sub_le (B := B) hc hinf π hε (hF x hx) hx
  trace_correct_one := fun h1 => norm_trace_towerMat_one_sub_le (B := B) hinf π h1
  trace_correct_ne := fun x hx hne =>
    norm_trace_towerMat_le hc hinf π hε (hF x hx) hx (hB x hx) hne

/-- **Cyclic extension by a central element of infinite order modulo `H`.** If `k`
commutes with every element of `H` and no positive power of `k` lies in `H`, then
`IsModelled H` implies `IsModelled (H ⊔ ⟨k⟩)` (`thm:fixed-radical-membership`, cyclic
extension step, central infinite-order case). -/
theorem isModelled_sup_zpowers_of_commute (hc : ∀ h ∈ H, k * h = h * k)
    (hinf : ∀ m : ℕ, 0 < m → k ^ m ∉ H) (hH : TWW.IsModelled H) :
    TWW.IsModelled (H ⊔ Subgroup.zpowers k) := by
  intro F hF ε hε
  obtain ⟨π⟩ := hH (testSet H k F) (testSet_subset hc hinf hF) ε hε
  have hB : ∀ x ∈ F, (expo H k x).natAbs ≤ F.sup fun y => (expo H k y).natAbs :=
    fun x hx => Finset.le_sup (f := fun y => (expo H k y).natAbs) hx
  exact ⟨towerModel hc hinf hF hε _ hB π⟩

end GroupApproximation.Full.TWWCyclic
