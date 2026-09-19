import GroupApproximation.Steinberg.Perfect
import GroupApproximation.Sofic.CentralCoverInheritance

/-!
# The Kervaire--Steinberg central-extension argument

This file formalizes the group-theoretic lifting argument behind the
Kervaire--Steinberg theorem.  It never assumes that the unstable Steinberg
kernel vanishes.  Instead, given an arbitrary central extension of a
Steinberg group, it begins constructing the canonical lifted root elements.

The first substantive step is the separated-root lemma: in a central
extension of `St_I(R)`, arbitrary lifts of two non-addable root elements
commute as soon as there is one index outside their four endpoints.  This is
the first paragraph of the classical splitting proof and is the mechanism
that makes the eventual lifted root elements independent of choices.
-/

namespace GroupApproximation

open scoped commutatorElement

namespace KervaireSteinberg

variable {Y I R : Type*} [Group Y] [Fintype I] [DecidableEq I] [Ring R]

/-- Four indices cannot exhaust `Fin n` when `n ≥ 5`. -/
theorem fin_exists_spare_index {n : ℕ} (hn : 5 ≤ n)
    (i j k l : Fin n) :
    ∃ t : Fin n, t ≠ i ∧ t ≠ j ∧ t ≠ k ∧ t ≠ l := by
  by_contra h
  push Not at h
  let s : Finset (Fin n) := {i, j, k, l}
  have hs : s = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro t
    simp only [s, Finset.mem_insert, Finset.mem_singleton]
    by_cases hi : t = i
    · exact Or.inl hi
    by_cases hj : t = j
    · exact Or.inr (Or.inl hj)
    by_cases hk : t = k
    · exact Or.inr (Or.inr (Or.inl hk))
    exact Or.inr (Or.inr (Or.inr (h t hi hj hk)))
  have hcard : n ≤ 4 := by
    have hle : s.card ≤ 4 := Finset.card_le_four
    rw [hs, Finset.card_fin] at hle
    exact hle
  omega

/-- If the commutators of `a` and `b` with `c` are central, then their
commutator commutes with `c`.  This is the three-subgroup calculation used in
the separated-root argument. -/
theorem commutator_commutes_of_commutators_mem_center
    {a b c : Y}
    (ha : ⁅c, a⁆ ∈ Subgroup.center Y)
    (hb : ⁅c, b⁆ ∈ Subgroup.center Y) :
    Commute ⁅a, b⁆ c := by
  have hba : ⁅b, c⁆ ∈ Subgroup.center Y := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center Y).inv_mem hb
  have hca : ⁅c, a⁆ ∈ Subgroup.center Y := ha
  have hsecond :
      ⁅⁅b, c⁆, c * a * c⁻¹⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp hba (c * a * c⁻¹)).symm
  have hthird :
      ⁅⁅c, a⁆, a * b * a⁻¹⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp hca (a * b * a⁻¹)).symm
  have hhall := commutatorElement_commutatorElement_conj_mul a b c
  rw [hsecond, hthird, mul_one, mul_one] at hhall
  have hconj : Commute ⁅a, b⁆ (b * c * b⁻¹) :=
    commutatorElement_eq_one_iff_commute.mp hhall
  have hcentral : Commute ⁅a, b⁆ ⁅b, c⁆ := by
    change ⁅a, b⁆ * ⁅b, c⁆ = ⁅b, c⁆ * ⁅a, b⁆
    exact Subgroup.mem_center_iff.mp hba ⁅a, b⁆
  have hproduct : Commute ⁅a, b⁆ (⁅b, c⁆ * c) := by
    rw [← conj_eq_commutatorElement_mul, MulAut.conj_apply]
    exact hconj
  have hcancel : Commute ⁅a, b⁆ (⁅b, c⁆⁻¹ * (⁅b, c⁆ * c)) :=
    hcentral.inv_right.mul_right hproduct
  simpa only [inv_mul_cancel_left] using hcancel

/-- Changing either entry of a commutator by a central factor does not change
the commutator. -/
theorem commutator_eq_of_eq_mod_center
    {a a' b b' : Y}
    (ha : a' * a⁻¹ ∈ Subgroup.center Y)
    (hb : b' * b⁻¹ ∈ Subgroup.center Y) :
    ⁅a', b'⁆ = ⁅a, b⁆ := by
  let ca : Y := a' * a⁻¹
  let cb : Y := b' * b⁻¹
  have hca : ca ∈ Subgroup.center Y := ha
  have hcb : cb ∈ Subgroup.center Y := hb
  have hae : ca * a = a' := by
    dsimp [ca]
    group
  have hbe : cb * b = b' := by
    dsimp [cb]
    group
  rw [← hae, ← hbe, commutatorElement_mul_left_eq_conj_mul]
  have hca_all : Commute ca (cb * b) := by
    change ca * (cb * b) = (cb * b) * ca
    exact (Subgroup.mem_center_iff.mp hca (cb * b)).symm
  rw [hca_all.commutator_eq, mul_one]
  have hca_comm : Commute ca ⁅a, cb * b⁆ := by
    change ca * ⁅a, cb * b⁆ = ⁅a, cb * b⁆ * ca
    exact (Subgroup.mem_center_iff.mp hca ⁅a, cb * b⁆).symm
  rw [hca_comm.mul_inv_cancel]
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hacb : Commute a cb := by
    change a * cb = cb * a
    exact Subgroup.mem_center_iff.mp hcb a
  rw [hacb.commutator_eq, one_mul]
  have hcb_comm : Commute cb ⁅a, b⁆ := by
    change cb * ⁅a, b⁆ = ⁅a, b⁆ * cb
    exact (Subgroup.mem_center_iff.mp hcb ⁅a, b⁆).symm
  exact hcb_comm.mul_inv_cancel

/-- In a central extension, the commutator of two lifts depends only on their
images in the quotient. -/
theorem commutator_eq_of_same_projection
    (P : CentralExtension Y (SteinbergGroup I R))
    {a a' b b' : Y}
    (ha : P.projection a = P.projection a')
    (hb : P.projection b = P.projection b') :
    ⁅a, b⁆ = ⁅a', b'⁆ := by
  apply commutator_eq_of_eq_mod_center
  · apply P.ker_le_center
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha]
    simp
  · apply P.ker_le_center
    rw [MonoidHom.mem_ker, map_mul, map_inv, hb]
    simp

/-- The commutator-associativity identity used by Kervaire--Steinberg.  The
hypotheses are the precise commutations supplied by separated roots in the
central cover. -/
theorem commutator_commutator_eq
    (u v w : Y)
    (huw : Commute u w)
    (hpq : Commute ⁅u, v⁆ ⁅v, w⁆)
    (hqwp : Commute ⁅v, w⁆ ⁅w, ⁅u, v⁆⁆) :
    ⁅⁅u, v⁆, w⁆ = ⁅u, ⁅v, w⁆⁆ := by
  have hhall := commutatorElement_conj_commutatorElement_mul u v w
  have hwu : ⁅w, u⁆ = 1 := huw.symm.commutator_eq
  simp only [hwu, commutatorElement_one_right, one_mul] at hhall
  have hwuw : w * u * w⁻¹ = u := huw.symm.mul_inv_cancel
  rw [hwuw] at hhall
  have hvw : v * w * v⁻¹ = ⁅v, w⁆ * w := by
    rw [← conj_eq_commutatorElement_mul, MulAut.conj_apply]
  rw [hvw, commutatorElement_mul_left_eq_conj_mul] at hhall
  have hqp : Commute ⁅v, w⁆ ⁅u, v⁆ := hpq.symm
  rw [hqp.commutator_eq, mul_one] at hhall
  rw [hqwp.mul_inv_cancel] at hhall
  have heq : ⁅u, ⁅v, w⁆⁆ = ⁅w, ⁅u, v⁆⁆⁻¹ :=
    eq_inv_of_mul_eq_one_left hhall
  rw [commutatorElement_inv] at heq
  exact heq.symm

/-- **Separated-root lifts commute.**  Let `Y → St_I(R)` be any central
extension.  If the two roots `(i,j)` and `(k,l)` are non-addable and `t` is
outside their four endpoints, then *every* pair of lifts of
`xᵢⱼ(r), xₖₗ(s)` commutes.

No injectivity of the Steinberg projection occurs here; `Y` is an arbitrary
central cover of the full presented Steinberg group. -/
theorem lifts_commute_of_spare_index
    (P : CentralExtension Y (SteinbergGroup I R))
    (i j k l t : I)
    (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (hti : t ≠ i) (htj : t ≠ j) (htk : t ≠ k) (htl : t ≠ l)
    (r s : R) (y z : Y)
    (hy : P.projection y = SteinbergGroup.x i j hij r)
    (hz : P.projection z = SteinbergGroup.x k l hkl s) :
    Commute y z := by
  obtain ⟨y', hy'⟩ := P.surjective (SteinbergGroup.x i t (Ne.symm hti) 1)
  obtain ⟨y'', hy''⟩ := P.surjective (SteinbergGroup.x t j htj r)
  have hleftImage :
      Commute (P.projection y') (P.projection z) := by
    rw [hy', hz]
    exact SteinbergGroup.x_commute_of_ne
      i t k l (Ne.symm hti) hkl htk hli 1 s
  have hrightImage :
      Commute (P.projection y'') (P.projection z) := by
    rw [hy'', hz]
    exact SteinbergGroup.x_commute_of_ne
      t j k l htj hkl hjk (Ne.symm htl) r s
  have hleftCenter : ⁅z, y'⁆ ∈ Subgroup.center Y := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center Y).inv_mem
      (P.commutator_mem_center hleftImage)
  have hrightCenter : ⁅z, y''⁆ ∈ Subgroup.center Y := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center Y).inv_mem
      (P.commutator_mem_center hrightImage)
  have hcomm : Commute ⁅y', y''⁆ z :=
    commutator_commutes_of_commutators_mem_center hleftCenter hrightCenter
  let c : Y := y * ⁅y', y''⁆⁻¹
  have hcKer : c ∈ P.projection.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [c]
    rw [map_mul, map_inv, map_commutatorElement, hy, hy', hy'',
      SteinbergGroup.x_commutator i t j (Ne.symm hti) htj hij]
    simp
  have hcCenter : c ∈ Subgroup.center Y := P.ker_le_center hcKer
  have hcy : c * ⁅y', y''⁆ = y := by
    dsimp [c]
    group
  rw [← hcy]
  have hcz : Commute c z := by
    change c * z = z * c
    exact (Subgroup.mem_center_iff.mp hcCenter z).symm
  exact hcz.mul_left hcomm

/-- Rank-`n` form of `lifts_commute_of_spare_index`: for `n ≥ 5`, arbitrary
lifts of every pair of non-addable Steinberg roots commute. -/
theorem fin_lifts_commute
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (r s : R) (y z : Y)
    (hy : P.projection y = SteinbergGroup.x i j hij r)
    (hz : P.projection z = SteinbergGroup.x k l hkl s) :
    Commute y z := by
  obtain ⟨t, hti, htj, htk, htl⟩ := fin_exists_spare_index hn i j k l
  exact lifts_commute_of_spare_index P i j k l t hij hkl hjk hli
    hti htj htk htl r s y z hy hz

/-! ## Corrected root lifts

An arbitrary set-theoretic lift of a Steinberg root has a central ambiguity.
Kervaire and Steinberg remove it by expressing the root through a third index
and taking a commutator of arbitrary lifts.  The following definitions begin
that construction. -/

/-- A chosen lift through a central extension.  All results below are
independent of this choice once the commutator correction is applied. -/
noncomputable def lift
    (P : CentralExtension Y (SteinbergGroup I R))
    (g : SteinbergGroup I R) : Y :=
  Classical.choose (P.surjective g)

@[simp] theorem projection_lift
    (P : CentralExtension Y (SteinbergGroup I R))
    (g : SteinbergGroup I R) : P.projection (lift P g) = g :=
  Classical.choose_spec (P.surjective g)

/-- The commutator-corrected lift of `xᵢₗ(r)` through the intermediate index
`j`. -/
noncomputable def correctedRoot
    (P : CentralExtension Y (SteinbergGroup I R))
    (i j l : I) (hij : i ≠ j) (hjl : j ≠ l) (_hil : i ≠ l) (r : R) : Y :=
  ⁅lift P (SteinbergGroup.x i j hij 1),
    lift P (SteinbergGroup.x j l hjl r)⁆

/-- The corrected lift really lies over the intended Steinberg root. -/
@[simp] theorem projection_correctedRoot
    (P : CentralExtension Y (SteinbergGroup I R))
    (i j l : I) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (r : R) :
    P.projection (correctedRoot P i j l hij hjl hil r) =
      SteinbergGroup.x i l hil r := by
  rw [correctedRoot, map_commutatorElement, projection_lift, projection_lift,
    SteinbergGroup.x_commutator i j l hij hjl hil]
  simp

/-- For a fixed intermediate index, the corrected root is independent of the
two arbitrary lifts used to form its defining commutator. -/
theorem correctedRoot_eq_commutator_of_lifts
    (P : CentralExtension Y (SteinbergGroup I R))
    (i j l : I) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (r : R)
    (u z : Y)
    (hu : P.projection u = SteinbergGroup.x i j hij 1)
    (hz : P.projection z = SteinbergGroup.x j l hjl r) :
    correctedRoot P i j l hij hjl hil r = ⁅u, z⁆ := by
  apply commutator_eq_of_eq_mod_center
  · apply P.ker_le_center
    rw [MonoidHom.mem_ker, map_mul, map_inv, projection_lift, hu]
    simp
  · apply P.ker_le_center
    rw [MonoidHom.mem_ker, map_mul, map_inv, projection_lift, hz]
    simp

/-- Corrected roots do not depend on the intermediate index when the two
candidate intermediates are distinct.  The endpoint and off-diagonal
hypotheses then make the four indices pairwise distinct. -/
theorem fin_correctedRoot_eq_of_middle_ne
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (i j k l : Fin n)
    (hij : i ≠ j) (hjl : j ≠ l)
    (hik : i ≠ k) (hkl : k ≠ l)
    (hil : i ≠ l) (hjk : j ≠ k) (r : R) :
    correctedRoot P i j l hij hjl hil r =
      correctedRoot P i k l hik hkl hil r := by
  let u : Y := lift P (SteinbergGroup.x i j hij 1)
  let v : Y := lift P (SteinbergGroup.x j k hjk 1)
  let w : Y := lift P (SteinbergGroup.x k l hkl r)
  have hu : P.projection u = SteinbergGroup.x i j hij 1 := projection_lift P _
  have hv : P.projection v = SteinbergGroup.x j k hjk 1 := projection_lift P _
  have hw : P.projection w = SteinbergGroup.x k l hkl r := projection_lift P _
  have hp : P.projection ⁅u, v⁆ = SteinbergGroup.x i k hik 1 := by
    rw [map_commutatorElement, hu, hv,
      SteinbergGroup.x_commutator i j k hij hjk hik]
    simp
  have hq : P.projection ⁅v, w⁆ = SteinbergGroup.x j l hjl r := by
    rw [map_commutatorElement, hv, hw,
      SteinbergGroup.x_commutator j k l hjk hkl hjl]
    simp
  have hwp : P.projection ⁅w, ⁅u, v⁆⁆ =
      SteinbergGroup.x i l hil (-r) := by
    rw [map_commutatorElement, hw, hp, ← commutatorElement_inv,
      SteinbergGroup.x_commutator i k l hik hkl hil, SteinbergGroup.x_neg]
    simp
  have huw : Commute u w := by
    exact fin_lifts_commute hn P i j k l hij hkl hjk (Ne.symm hil)
      1 r u w hu hw
  have hpq : Commute ⁅u, v⁆ ⁅v, w⁆ := by
    exact fin_lifts_commute hn P i k j l hik hjl (Ne.symm hjk) (Ne.symm hil)
      1 r ⁅u, v⁆ ⁅v, w⁆ hp hq
  have hqwp : Commute ⁅v, w⁆ ⁅w, ⁅u, v⁆⁆ := by
    exact fin_lifts_commute hn P j l i l hjl hil (Ne.symm hil) (Ne.symm hjl)
      r (-r) ⁅v, w⁆ ⁅w, ⁅u, v⁆⁆ hq hwp
  have hjForm : correctedRoot P i j l hij hjl hil r = ⁅u, ⁅v, w⁆⁆ := by
    apply correctedRoot_eq_commutator_of_lifts P i j l hij hjl hil r u ⁅v, w⁆
    · exact hu
    · exact hq
  have hkForm : correctedRoot P i k l hik hkl hil r = ⁅⁅u, v⁆, w⁆ := by
    apply correctedRoot_eq_commutator_of_lifts P i k l hik hkl hil r ⁅u, v⁆ w
    · exact hp
    · exact hw
  rw [hjForm, hkForm]
  exact (commutator_commutator_eq u v w huw hpq hqwp).symm

/-- Corrected roots are independent of the intermediate index, with no
distinctness assumption between the two candidates. -/
theorem fin_correctedRoot_eq
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (i j k l : Fin n)
    (hij : i ≠ j) (hjl : j ≠ l)
    (hik : i ≠ k) (hkl : k ≠ l)
    (hil : i ≠ l) (r : R) :
    correctedRoot P i j l hij hjl hil r =
      correctedRoot P i k l hik hkl hil r := by
  by_cases hjk : j = k
  · subst k
    simp only [correctedRoot]
  · exact fin_correctedRoot_eq_of_middle_ne hn P i j k l
      hij hjl hik hkl hil hjk r

/-- A chosen index distinct from two prescribed endpoints. -/
noncomputable def middleIndex {n : ℕ} (hn : 3 ≤ n)
    (i l : Fin n) : Fin n :=
  Classical.choose (Fin.exists_ne_and_ne_of_two_lt i l (by omega))

theorem middleIndex_ne_left {n : ℕ} (hn : 3 ≤ n) (i l : Fin n) :
    middleIndex hn i l ≠ i :=
  (Classical.choose_spec (Fin.exists_ne_and_ne_of_two_lt i l (by omega))).1

theorem middleIndex_ne_right {n : ℕ} (hn : 3 ≤ n) (i l : Fin n) :
    middleIndex hn i l ≠ l :=
  (Classical.choose_spec (Fin.exists_ne_and_ne_of_two_lt i l (by omega))).2

/-- The canonical corrected lift of a Steinberg root. -/
noncomputable def canonicalRoot
    {n : ℕ} (hn : 3 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (i l : Fin n) (hil : i ≠ l) (r : R) : Y :=
  correctedRoot P i (middleIndex hn i l) l
    (Ne.symm (middleIndex_ne_left hn i l))
    (middleIndex_ne_right hn i l) hil r

@[simp] theorem projection_canonicalRoot
    {n : ℕ} (hn : 3 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (i l : Fin n) (hil : i ≠ l) (r : R) :
    P.projection (canonicalRoot hn P i l hil r) =
      SteinbergGroup.x i l hil r :=
  projection_correctedRoot P i (middleIndex hn i l) l
    (Ne.symm (middleIndex_ne_left hn i l))
    (middleIndex_ne_right hn i l) hil r

/-- Any admissible intermediate computes the canonical corrected root. -/
theorem canonicalRoot_eq_correctedRoot
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (i j l : Fin n) (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l) (r : R) :
    canonicalRoot (by omega) P i l hil r =
      correctedRoot P i j l hij hjl hil r := by
  apply fin_correctedRoot_eq hn P i (middleIndex (by omega) i l) j l
    (Ne.symm (middleIndex_ne_left (by omega) i l))
    (middleIndex_ne_right (by omega) i l) hij hjl hil r

/-- Canonical lifted roots satisfy the separated Steinberg commutation
relation. -/
theorem fin_canonicalRoot_commute
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (r s : R) :
    Commute (canonicalRoot (by omega) P i j hij r)
      (canonicalRoot (by omega) P k l hkl s) := by
  apply fin_lifts_commute hn P i j k l hij hkl hjk hli r s
  · exact projection_canonicalRoot (by omega) P i j hij r
  · exact projection_canonicalRoot (by omega) P k l hkl s

/-- Canonical lifted roots satisfy the adjacent Steinberg commutator
relation. -/
theorem fin_canonicalRoot_commutator
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (i k l : Fin n) (hik : i ≠ k) (hkl : k ≠ l) (hil : i ≠ l)
    (a b : R) :
    ⁅canonicalRoot (by omega) P i k hik a,
      canonicalRoot (by omega) P k l hkl b⁆ =
      canonicalRoot (by omega) P i l hil (a * b) := by
  obtain ⟨j, hji, hjk, hjl, _⟩ := fin_exists_spare_index hn i k l l
  have hij : i ≠ j := Ne.symm hji
  let u : Y := lift P (SteinbergGroup.x i j hij 1)
  let v : Y := lift P (SteinbergGroup.x j k hjk a)
  let w : Y := lift P (SteinbergGroup.x k l hkl b)
  have hu : P.projection u = SteinbergGroup.x i j hij 1 := projection_lift P _
  have hv : P.projection v = SteinbergGroup.x j k hjk a := projection_lift P _
  have hw : P.projection w = SteinbergGroup.x k l hkl b := projection_lift P _
  have hp : P.projection ⁅u, v⁆ = SteinbergGroup.x i k hik a := by
    rw [map_commutatorElement, hu, hv,
      SteinbergGroup.x_commutator i j k hij hjk hik]
    simp
  have hq : P.projection ⁅v, w⁆ = SteinbergGroup.x j l hjl (a * b) := by
    rw [map_commutatorElement, hv, hw,
      SteinbergGroup.x_commutator j k l hjk hkl hjl]
  have hwp : P.projection ⁅w, ⁅u, v⁆⁆ =
      SteinbergGroup.x i l hil (-(a * b)) := by
    rw [map_commutatorElement, hw, hp, ← commutatorElement_inv,
      SteinbergGroup.x_commutator i k l hik hkl hil, SteinbergGroup.x_neg]
  have huw : Commute u w :=
    fin_lifts_commute hn P i j k l hij hkl hjk (Ne.symm hil)
      1 b u w hu hw
  have hpq : Commute ⁅u, v⁆ ⁅v, w⁆ :=
    fin_lifts_commute hn P i k j l hik hjl (Ne.symm hjk) (Ne.symm hil)
      a (a * b) ⁅u, v⁆ ⁅v, w⁆ hp hq
  have hqwp : Commute ⁅v, w⁆ ⁅w, ⁅u, v⁆⁆ :=
    fin_lifts_commute hn P j l i l hjl hil (Ne.symm hil) (Ne.symm hjl)
      (a * b) (-(a * b)) ⁅v, w⁆ ⁅w, ⁅u, v⁆⁆ hq hwp
  have hlhs :
      ⁅canonicalRoot (by omega) P i k hik a,
        canonicalRoot (by omega) P k l hkl b⁆ = ⁅⁅u, v⁆, w⁆ := by
    apply commutator_eq_of_same_projection P
    · rw [projection_canonicalRoot, hp]
    · rw [projection_canonicalRoot, hw]
  have hrhs : canonicalRoot (by omega) P i l hil (a * b) =
      ⁅u, ⁅v, w⁆⁆ := by
    rw [canonicalRoot_eq_correctedRoot hn P i j l hij hjl hil (a * b)]
    exact correctedRoot_eq_commutator_of_lifts P i j l hij hjl hil
      (a * b) u ⁅v, w⁆ hu hq
  rw [hlhs, hrhs]
  exact commutator_commutator_eq u v w huw hpq hqwp

/-- Corrected roots with a fixed intermediate index are additive in the
coefficient. -/
theorem fin_correctedRoot_mul
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (i j l : Fin n) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (a b : R) :
    correctedRoot P i j l hij hjl hil a *
      correctedRoot P i j l hij hjl hil b =
      correctedRoot P i j l hij hjl hil (a + b) := by
  let u : Y := lift P (SteinbergGroup.x i j hij 1)
  let za : Y := lift P (SteinbergGroup.x j l hjl a)
  let zb : Y := lift P (SteinbergGroup.x j l hjl b)
  have hu : P.projection u = SteinbergGroup.x i j hij 1 := projection_lift P _
  have hza : P.projection za = SteinbergGroup.x j l hjl a := projection_lift P _
  have hzb : P.projection zb = SteinbergGroup.x j l hjl b := projection_lift P _
  have hsum : P.projection (za * zb) = SteinbergGroup.x j l hjl (a + b) := by
    rw [map_mul, hza, hzb, SteinbergGroup.x_mul]
  have hq : P.projection ⁅u, zb⁆ = SteinbergGroup.x i l hil b := by
    rw [map_commutatorElement, hu, hzb,
      SteinbergGroup.x_commutator i j l hij hjl hil]
    simp
  have hcomm : Commute za ⁅u, zb⁆ :=
    fin_lifts_commute hn P j l i l hjl hil (Ne.symm hil) (Ne.symm hjl)
      a b za ⁅u, zb⁆ hza hq
  change ⁅u, za⁆ * ⁅u, zb⁆ = correctedRoot P i j l hij hjl hil (a + b)
  rw [correctedRoot_eq_commutator_of_lifts P i j l hij hjl hil
    (a + b) u (za * zb) hu hsum]
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc
    ⁅u, za⁆ * ⁅u, zb⁆ =
        ⁅u, za⁆ * (za * ⁅u, zb⁆ * za⁻¹) := by
          rw [hcomm.mul_inv_cancel]
    _ = ⁅u, za⁆ * za * ⁅u, zb⁆ * za⁻¹ := by
          simp only [mul_assoc]

/-- Canonical lifted roots satisfy the additive Steinberg relation. -/
theorem fin_canonicalRoot_mul
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (i l : Fin n) (hil : i ≠ l) (a b : R) :
    canonicalRoot (by omega) P i l hil a *
      canonicalRoot (by omega) P i l hil b =
      canonicalRoot (by omega) P i l hil (a + b) := by
  exact fin_correctedRoot_mul hn P i (middleIndex (by omega) i l) l
    (Ne.symm (middleIndex_ne_left (by omega) i l))
    (middleIndex_ne_right (by omega) i l) hil a b

/-! ## Splitting every central extension of the Steinberg group -/

/-- Interpret every presented Steinberg generator by its canonical corrected
lift. -/
noncomputable def splittingGeneratorImage
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (g : SteinbergGenerator (Fin n) R) : Y :=
  canonicalRoot (by omega) P g.row g.column g.row_ne_column g.coefficient

private theorem splittingGeneratorImage_kills_relations
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (w : FreeGroup (SteinbergGenerator (Fin n) R))
    (hw : w ∈ SteinbergGroup.relations (I := Fin n) (R := R)) :
    FreeGroup.lift (splittingGeneratorImage hn P) w = 1 := by
  change SteinbergGroup.IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of,
        splittingGeneratorImage]
      change canonicalRoot (by omega) P i j hij a *
          canonicalRoot (by omega) P i j hij b *
          (canonicalRoot (by omega) P i j hij (a + b))⁻¹ = 1
      rw [fin_canonicalRoot_mul hn]
      simp
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of,
        splittingGeneratorImage]
      change ⁅canonicalRoot (by omega) P i j hij a,
        canonicalRoot (by omega) P k l hkl b⁆ = 1
      exact (fin_canonicalRoot_commute hn P i j k l hij hkl hjk hli a b).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement,
        FreeGroup.lift_apply_of, splittingGeneratorImage]
      change ⁅canonicalRoot (by omega) P i j hij a,
          canonicalRoot (by omega) P j k hjk b⁆ *
          (canonicalRoot (by omega) P i k hik (a * b))⁻¹ = 1
      rw [fin_canonicalRoot_commutator hn P i j k hij hjk hik]
      simp

/-- The canonical section of an arbitrary central extension of `St_n(R)`. -/
noncomputable def splittingHom
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R)) :
    SteinbergGroup (Fin n) R →* Y :=
  PresentedGroup.toGroup (f := splittingGeneratorImage hn P)
    (splittingGeneratorImage_kills_relations hn P)

@[simp] theorem splittingHom_x
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (i j : Fin n) (hij : i ≠ j) (r : R) :
    splittingHom hn P (SteinbergGroup.x i j hij r) =
      canonicalRoot (by omega) P i j hij r := by
  change splittingHom hn P (PresentedGroup.of
    (⟨i, j, hij, r⟩ : SteinbergGenerator (Fin n) R)) = _
  simp [splittingHom, splittingGeneratorImage]

/-- **Kervaire--Steinberg splitting theorem.**  For every ring and every
`n ≥ 5`, every central extension of the full presented Steinberg group
`St_n(R)` has a homomorphic section.  No assertion that its own unstable
`K₂(n,R)` kernel vanishes is used or implied. -/
theorem splittingHom_isSection
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R)) :
    P.projection.comp (splittingHom hn P) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, r⟩
  change P.projection
      (splittingHom hn P (SteinbergGroup.x i j hij r)) =
    SteinbergGroup.x i j hij r
  rw [splittingHom_x, projection_canonicalRoot]

/-- Existence form of the splitting theorem. -/
theorem every_centralExtension_splits
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R)) :
    ∃ s : SteinbergGroup (Fin n) R →* Y,
      P.projection.comp s = MonoidHom.id _ :=
  ⟨splittingHom hn P, splittingHom_isSection hn P⟩

/-- The corrected lift of the zero coefficient is the identity, despite the
fact that the original chosen lift of the identity may be a nontrivial
central kernel element. -/
@[simp] theorem correctedRoot_zero
    (P : CentralExtension Y (SteinbergGroup I R))
    (i j l : I) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    correctedRoot P i j l hij hjl hil 0 = 1 := by
  apply commutatorElement_eq_one_iff_commute.mpr
  have hker : lift P (SteinbergGroup.x j l hjl (0 : R)) ∈
      P.projection.ker := by
    rw [MonoidHom.mem_ker, projection_lift, SteinbergGroup.x_zero]
  have hcenter := P.ker_le_center hker
  change Commute (lift P (SteinbergGroup.x i j hij 1))
    (lift P (SteinbergGroup.x j l hjl 0))
  change lift P (SteinbergGroup.x i j hij 1) *
      lift P (SteinbergGroup.x j l hjl 0) =
    lift P (SteinbergGroup.x j l hjl 0) *
      lift P (SteinbergGroup.x i j hij 1)
  exact Subgroup.mem_center_iff.mp hcenter
    (lift P (SteinbergGroup.x i j hij 1))

/-- In rank at least five, corrected lifts of non-addable roots commute. -/
theorem fin_correctedRoot_commute
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (i j m k l p : Fin n)
    (hij : i ≠ j) (hjm : j ≠ m) (him : i ≠ m)
    (hkl : k ≠ l) (hlp : l ≠ p) (hkp : k ≠ p)
    (hmk : m ≠ k) (hpi : p ≠ i) (r s : R) :
    Commute (correctedRoot P i j m hij hjm him r)
      (correctedRoot P k l p hkl hlp hkp s) := by
  apply fin_lifts_commute hn P i m k p him hkp hmk hpi r s
  · exact projection_correctedRoot P i j m hij hjm him r
  · exact projection_correctedRoot P k l p hkl hlp hkp s

end KervaireSteinberg
end GroupApproximation
