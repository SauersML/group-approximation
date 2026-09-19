import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg words over a graded ring: raising the degree bound by one (lane pal-q111, H.L2)

M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, Math. USSR Sb. 45 (1983), Lemma 3.3;
Lavrenov–Sinchuk, arXiv:1909.02637, Prop 5.3.  Take `B = A[t] + 𝔄[t⁻¹]`, graded by the degree in
`t`.  Its homogeneous part of degree `d` is `A tᵈ` for `d ≥ 0` and `𝔄 tᵈ` for `d < 0`.  The homogeneous
Steinberg generators are `x_ij(c tᵈ)`.

This file works in an arbitrary group `G` and needs no ring `B` at all.  A family
`Y i j hij d c` stands for the images of `x_ij(c tᵈ)`.  `Rels 𝔄 Y m` says that `Y` satisfies every
homogeneous Steinberg relation of degree `≤ m`:
* `add`: `Yᵈ_ij(c) Yᵈ_ij(c') = Yᵈ_ij(c + c')`, for `d ≤ m`;
* `r2`: `⁅Yᵈ_ij(c), Yᵉ_jk(c')⁆ = Y^{d+e}_ik(c c')`, for `d, e, d + e ≤ m`;
* `r3`: `⁅Yᵈ_ij(c), Yᵉ_kl(c')⁆ = 1` for `j ≠ k` and `i ≠ l`, with `d, e ≤ m`.
Coefficients of negative degree lie in `𝔄` (`Allowed`).

**Main result.** `Rels.rels_extend`: for `N ≥ 5` and `m ≥ 1`, set
`Y^{m+1}_ij(c) := ⁅Y^m_ih(c), Y¹_hj(1)⁆` for an auxiliary index `h ∉ {i, j}` (`zElt`, `extend`).
If `Y` satisfies the relations of degree `≤ m`, the extended family satisfies those of degree
`≤ m + 1`.  The auxiliary index does not matter (`Rels.zElt_eq`).

The proof is Tulenbaev's.  It rests on one identity: `⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, y z y⁻¹⁆` when `x`
commutes with `z` (`comm_comm_of_commute`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace Graded

open scoped commutatorElement

/-! ### Commutator identities -/

section GroupLemmas

variable {G : Type*} [Group G]

theorem comm_mul_left' (a b c : G) : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  group

theorem comm_mul_right' (a b c : G) : ⁅a, b * c⁆ = ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ := by
  simp only [commutatorElement_def]
  group

/-- **The basic identity.** If `x` commutes with `z`, then `⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, y z y⁻¹⁆`. -/
theorem comm_comm_of_commute (x y z : G) (hxz : Commute x z) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, y * z * y⁻¹⁆ := by
  have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by
    rw [commutatorElement_def]
    group
  have hxz' : x * z * x⁻¹ = z := by
    rw [hxz.eq, mul_inv_cancel_right]
  have h1 : x * ⁅y, z⁆ * x⁻¹ = ⁅⁅x, y⁆ * y, z⁆ := by
    rw [conjugate_commutatorElement, hxy, hxz']
  rw [commutatorElement_def x ⁅y, z⁆, h1]
  simp only [commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.comm_comm_of_commute

theorem conj_eq_comm_mul (y z : G) : y * z * y⁻¹ = ⁅y, z⁆ * z := by
  rw [commutatorElement_def]
  group

theorem commute_comm_of {a b c : G} (hb : Commute a b) (hc : Commute a c) :
    Commute a ⁅b, c⁆ := by
  rw [commutatorElement_def]
  exact ((hb.mul_right hc).mul_right hb.inv_right).mul_right hc.inv_right

theorem comm_eq_one_of_commute {a b : G} (h : Commute a b) : ⁅a, b⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.mpr h

theorem commute_of_comm_eq_one {a b : G} (h : ⁅a, b⁆ = 1) : Commute a b :=
  commutatorElement_eq_one_iff_commute.mp h

theorem conj_eq_of_commute {a b : G} (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]

end GroupLemmas

/-! ### Fresh indices -/

section Fresh

variable {N : ℕ}

theorem exists_fresh (s : Finset (Fin N)) (hs : s.card < N) : ∃ x, x ∉ s := by
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset (Fin N)) ⊆ s := fun x _ => hc x
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at hle
  omega

theorem fresh2 (hN : 3 ≤ N) (i j : Fin N) : ∃ h, h ≠ i ∧ h ≠ j := by
  have h1 := Finset.card_insert_le i ({j} : Finset (Fin N))
  rw [Finset.card_singleton] at h1
  obtain ⟨h, hh⟩ := exists_fresh ({i, j} : Finset (Fin N)) (by omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
  exact ⟨h, hh.1, hh.2⟩

theorem fresh3 (hN : 4 ≤ N) (i j k : Fin N) : ∃ h, h ≠ i ∧ h ≠ j ∧ h ≠ k := by
  have h1 := Finset.card_insert_le i ({j, k} : Finset (Fin N))
  have h2 := Finset.card_insert_le j ({k} : Finset (Fin N))
  rw [Finset.card_singleton] at h2
  obtain ⟨h, hh⟩ := exists_fresh ({i, j, k} : Finset (Fin N)) (by omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
  exact ⟨h, hh.1, hh.2.1, hh.2.2⟩

theorem fresh4 (hN : 5 ≤ N) (i j k l : Fin N) : ∃ h, h ≠ i ∧ h ≠ j ∧ h ≠ k ∧ h ≠ l := by
  have h1 := Finset.card_insert_le i ({j, k, l} : Finset (Fin N))
  have h2 := Finset.card_insert_le j ({k, l} : Finset (Fin N))
  have h3 := Finset.card_insert_le k ({l} : Finset (Fin N))
  rw [Finset.card_singleton] at h3
  obtain ⟨h, hh⟩ := exists_fresh ({i, j, k, l} : Finset (Fin N)) (by omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
  exact ⟨h, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2⟩

/-- A fixed auxiliary index outside `{i, j}`. -/
noncomputable def aux (hN : 3 ≤ N) (i j : Fin N) : Fin N :=
  Classical.choose (fresh2 hN i j)

theorem aux_ne_left (hN : 3 ≤ N) (i j : Fin N) : aux hN i j ≠ i :=
  (Classical.choose_spec (fresh2 hN i j)).1

theorem aux_ne_right (hN : 3 ≤ N) (i j : Fin N) : aux hN i j ≠ j :=
  (Classical.choose_spec (fresh2 hN i j)).2

end Fresh

/-! ### Coefficients and relations -/

section Rels

variable {A : Type*} [CommRing A] (𝔄 : Ideal A)

/-- The coefficient `c` is allowed in `t`-degree `d`: it lies in `𝔄` when `d < 0`. -/
def Allowed (d : ℤ) (c : A) : Prop :=
  d < 0 → c ∈ 𝔄

variable {𝔄}

theorem allowed_of_nonneg {d : ℤ} (hd : 0 ≤ d) (c : A) : Allowed 𝔄 d c :=
  fun h => absurd h (not_lt.mpr hd)

theorem allowed_zero (d : ℤ) : Allowed 𝔄 d (0 : A) :=
  fun _ => 𝔄.zero_mem

theorem Allowed.neg {d : ℤ} {c : A} (h : Allowed 𝔄 d c) : Allowed 𝔄 d (-c) :=
  fun hd => 𝔄.neg_mem (h hd)

theorem Allowed.add {d : ℤ} {c c' : A} (h : Allowed 𝔄 d c) (h' : Allowed 𝔄 d c') :
    Allowed 𝔄 d (c + c') :=
  fun hd => 𝔄.add_mem (h hd) (h' hd)

theorem Allowed.mul {d e : ℤ} {c c' : A} (h : Allowed 𝔄 d c) (h' : Allowed 𝔄 e c') :
    Allowed 𝔄 (d + e) (c * c') := by
  intro hde
  by_cases hd : d < 0
  · exact 𝔄.mul_mem_right c' (h hd)
  · exact 𝔄.mul_mem_left c (h' (by omega))

theorem Allowed.mono {d e : ℤ} {c : A} (h : Allowed 𝔄 d c) (hde : d ≤ e) : Allowed 𝔄 e c :=
  fun he => h (by omega)

/-- A family of candidate images of the homogeneous generators `x_ij(c tᵈ)`. -/
abbrev Fam (G A : Type*) (N : ℕ) : Type _ :=
  ∀ i j : Fin N, i ≠ j → ℤ → A → G

variable (𝔄)

/-- **The homogeneous Steinberg relations of degree `≤ m`.** -/
structure Rels {G : Type*} [Group G] {N : ℕ} (Y : Fam G A N) (m : ℤ) : Prop where
  add : ∀ (i j : Fin N) (hij : i ≠ j) (d : ℤ) (c c' : A), d ≤ m → Allowed 𝔄 d c →
    Allowed 𝔄 d c' → Y i j hij d c * Y i j hij d c' = Y i j hij d (c + c')
  r2 : ∀ (i j k : Fin N) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (d e : ℤ) (c c' : A),
    d ≤ m → e ≤ m → d + e ≤ m → Allowed 𝔄 d c → Allowed 𝔄 e c' →
      ⁅Y i j hij d c, Y j k hjk e c'⁆ = Y i k hik (d + e) (c * c')
  r3 : ∀ (i j k l : Fin N) (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → i ≠ l → ∀ (d e : ℤ) (c c' : A),
    d ≤ m → e ≤ m → Allowed 𝔄 d c → Allowed 𝔄 e c' → ⁅Y i j hij d c, Y k l hkl e c'⁆ = 1

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels

end Rels

/-! ### Consequences at a fixed level -/

section Level

variable {A : Type*} [CommRing A] {𝔄 : Ideal A} {G : Type*} [Group G] {N : ℕ} {Y : Fam G A N}
  {m : ℤ}

theorem Rels.one (h : Rels 𝔄 Y m) {i j : Fin N} (hij : i ≠ j) {d : ℤ} (hd : d ≤ m) :
    Y i j hij d 0 = 1 := by
  have h0 := h.add i j hij d 0 0 hd (allowed_zero d) (allowed_zero d)
  rw [add_zero] at h0
  exact mul_left_cancel (h0.trans (mul_one _).symm)

theorem Rels.neg (h : Rels 𝔄 Y m) {i j : Fin N} (hij : i ≠ j) {d : ℤ} (hd : d ≤ m) {c : A}
    (hc : Allowed 𝔄 d c) : Y i j hij d (-c) = (Y i j hij d c)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [h.add i j hij d (-c) c hd hc.neg hc, neg_add_cancel, h.one hij hd]

theorem Rels.commute (h : Rels 𝔄 Y m) {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hil : i ≠ l) {d e : ℤ} (hd : d ≤ m) (he : e ≤ m) {c c' : A}
    (hc : Allowed 𝔄 d c) (hc' : Allowed 𝔄 e c') : Commute (Y i j hij d c) (Y k l hkl e c') :=
  commute_of_comm_eq_one (h.r3 i j k l hij hkl hjk hil d e c c' hd he hc hc')

/-- **Changing the middle index** (Tulenbaev, Lemma 3.3, the first display). -/
theorem Rels.comm_eq_aux (h : Rels 𝔄 Y m) (hm : 1 ≤ m) {i j h' l : Fin N} (hij : i ≠ j)
    (hih : i ≠ h') (hhj : h' ≠ j) (hil : i ≠ l) (hlj : l ≠ j) (hhl : h' ≠ l) {p q : ℤ}
    (hpq : p + q = m + 1) (hq1 : 1 ≤ q) (hqm : q ≤ m) (c c' : A) :
    ⁅Y i h' hih p c, Y h' j hhj q c'⁆ = ⁅Y i l hil m (c * c'), Y l j hlj 1 1⁆ := by
  have hpm : p ≤ m := by omega
  have hp0 : 0 ≤ p := by omega
  have hyq : Y h' j hhj q c' = ⁅Y h' l hhl (q - 1) c', Y l j hlj 1 1⁆ := by
    rw [h.r2 h' l j hhl hlj hhj (q - 1) 1 c' 1 (by omega) hm (by omega)
      (allowed_of_nonneg (by omega) _) (allowed_of_nonneg (by omega) _), sub_add_cancel, mul_one]
  have hxz : Commute (Y i h' hih p c) (Y l j hlj 1 1) :=
    h.commute hih hlj hhl hij hpm hm (allowed_of_nonneg hp0 _) (allowed_of_nonneg (by omega) _)
  rw [hyq, comm_comm_of_commute _ _ _ hxz, h.r2 i h' l hih hhl hil p (q - 1) c c' hpm (by omega)
    (by omega) (allowed_of_nonneg hp0 _) (allowed_of_nonneg (by omega) _),
    conj_eq_comm_mul (Y h' l hhl (q - 1) c') (Y l j hlj 1 1), ← hyq,
    show p + (q - 1) = m by omega, comm_mul_right']
  have h1 : ⁅Y i l hil m (c * c'), Y h' j hhj q c'⁆ = 1 :=
    h.r3 i l h' j hil hhj hhl.symm hij m q _ _ le_rfl hqm (allowed_of_nonneg (by omega) _)
      (allowed_of_nonneg (by omega) _)
  have hc : Commute (Y h' j hhj q c') ⁅Y i l hil m (c * c'), Y l j hlj 1 1⁆ :=
    commute_comm_of
      (h.commute hhj hil hij.symm hhl hqm le_rfl (allowed_of_nonneg (by omega) _)
        (allowed_of_nonneg (by omega) _))
      (h.commute hhj hlj hlj.symm hhj hqm hm (allowed_of_nonneg (by omega) _)
        (allowed_of_nonneg (by omega) _))
  rw [h1, one_mul, conj_eq_of_commute hc]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.comm_eq_aux

theorem Rels.aux_indep (h : Rels 𝔄 Y m) (hm : 1 ≤ m) {i j h' l : Fin N} (hij : i ≠ j)
    (hih : i ≠ h') (hhj : h' ≠ j) (hil : i ≠ l) (hlj : l ≠ j) (hhl : h' ≠ l) (c : A) :
    ⁅Y i h' hih m c, Y h' j hhj 1 1⁆ = ⁅Y i l hil m c, Y l j hlj 1 1⁆ := by
  have h0 := h.comm_eq_aux hm hij hih hhj hil hlj hhl (p := m) (q := 1) (by ring) le_rfl hm c 1
  rwa [mul_one] at h0

/-- The degree-`(m+1)` element `⁅Y^m_ia(c), Y¹_aj(1)⁆`, for the fixed auxiliary index `a`. -/
noncomputable def zElt (hN : 3 ≤ N) (Y : Fam G A N) (m : ℤ) (i j : Fin N) (c : A) : G :=
  ⁅Y i (aux hN i j) (aux_ne_left hN i j).symm m c, Y (aux hN i j) j (aux_ne_right hN i j) 1 1⁆

/-- The auxiliary index does not matter. -/
theorem Rels.zElt_eq (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) {i j h' : Fin N} (hij : i ≠ j)
    (hih : i ≠ h') (hhj : h' ≠ j) (c : A) :
    ⁅Y i h' hih m c, Y h' j hhj 1 1⁆ = zElt hN Y m i j c := by
  unfold zElt
  by_cases he : h' = aux hN i j
  · subst he
    rfl
  · exact h.aux_indep hm hij hih hhj (aux_ne_left hN i j).symm (aux_ne_right hN i j) he c

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.zElt_eq

/-- `⁅Yᵖ_ih(c), Y^q_hj(c')⁆ = Y^{m+1}_ij(c c')` for `p + q = m + 1` and `1 ≤ q ≤ m`. -/
theorem Rels.comm_eq_zElt (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) (hN4 : 4 ≤ N)
    {i j h' : Fin N} (hij : i ≠ j) (hih : i ≠ h') (hhj : h' ≠ j) {p q : ℤ} (hpq : p + q = m + 1)
    (hq1 : 1 ≤ q) (hqm : q ≤ m) (c c' : A) :
    ⁅Y i h' hih p c, Y h' j hhj q c'⁆ = zElt hN Y m i j (c * c') := by
  obtain ⟨l, hli, hlj, hlh⟩ := fresh3 hN4 i j h'
  rw [h.comm_eq_aux hm hij hih hhj hli.symm hlj hlh.symm hpq hq1 hqm c c']
  exact h.zElt_eq hm hN hij hli.symm hlj (c * c')

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.comm_eq_zElt

/-- `Y^{m+1}_ij` commutes with `Yᵉ_kl` for `e ≤ m`, `j ≠ k`, `i ≠ l`. -/
theorem Rels.zElt_commute (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) (hN5 : 5 ≤ N)
    {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l) {e : ℤ}
    (he : e ≤ m) {c' : A} (hc' : Allowed 𝔄 e c') (c : A) :
    Commute (zElt hN Y m i j c) (Y k l hkl e c') := by
  obtain ⟨h', h1, h2, h3, h4⟩ := fresh4 hN5 i j k l
  rw [← h.zElt_eq hm hN hij h1.symm h2 c]
  have ha : Commute (Y k l hkl e c') (Y i h' h1.symm m c) :=
    (h.commute h1.symm hkl h3 hil le_rfl he (allowed_of_nonneg (by omega) _) hc').symm
  have hb : Commute (Y k l hkl e c') (Y h' j h2 1 1) :=
    (h.commute h2 hkl hjk h4 hm he (allowed_of_nonneg (by omega) _) hc').symm
  exact (commute_comm_of ha hb).symm

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.zElt_commute

/-- `Y^{m+1}_ij` commutes with `Y^{m+1}_kl` for `j ≠ k`, `i ≠ l`. -/
theorem Rels.zElt_commute_zElt (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) (hN5 : 5 ≤ N)
    {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l) (c c' : A) :
    Commute (zElt hN Y m i j c) (zElt hN Y m k l c') := by
  obtain ⟨h', h1, h2, h3, h4⟩ := fresh4 hN5 i j k l
  rw [← h.zElt_eq hm hN hkl h3.symm h4 c']
  exact commute_comm_of
    (h.zElt_commute hm hN hN5 hij h3.symm hjk h1.symm le_rfl (allowed_of_nonneg (by omega) _) c)
    (h.zElt_commute hm hN hN5 hij h4 h2.symm hil hm (allowed_of_nonneg (by omega) _) c)

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.zElt_commute_zElt

theorem Rels.zElt_add (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) (hN5 : 5 ≤ N) {i j : Fin N}
    (hij : i ≠ j) (c c' : A) :
    zElt hN Y m i j c * zElt hN Y m i j c' = zElt hN Y m i j (c + c') := by
  set a := aux hN i j
  have hai : i ≠ a := (aux_ne_left hN i j).symm
  have haj : a ≠ j := aux_ne_right hN i j
  have hz : ∀ x : A, zElt hN Y m i j x = ⁅Y i a hai m x, Y a j haj 1 1⁆ := fun x => rfl
  obtain ⟨l, hli, hlj, hla⟩ := fresh3 (by omega : 4 ≤ N) i j a
  have hcomm : Commute (Y i a hai m c) (zElt hN Y m i j c') := by
    rw [← h.zElt_eq hm hN hij hli.symm hlj c']
    exact commute_comm_of
      (h.commute hai hli.symm hai.symm hli.symm le_rfl le_rfl (allowed_of_nonneg (by omega) _)
        (allowed_of_nonneg (by omega) _))
      (h.commute hai hlj hla.symm hij le_rfl hm (allowed_of_nonneg (by omega) _)
        (allowed_of_nonneg (by omega) _))
  rw [hz (c + c'), ← h.add i a hai m c c' le_rfl (allowed_of_nonneg (by omega) _)
    (allowed_of_nonneg (by omega) _), comm_mul_left', ← hz c', ← hz c,
    conj_eq_of_commute hcomm]
  exact (h.zElt_commute_zElt hm hN hN5 hij hij hij.symm hij c c').eq

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.zElt_add

theorem Rels.zElt_zero (h : Rels 𝔄 Y m) (hN : 3 ≤ N) (i j : Fin N) :
    zElt hN Y m i j 0 = 1 := by
  unfold zElt
  rw [h.one _ le_rfl, commutatorElement_one_left]

theorem Rels.zElt_neg (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) (hN5 : 5 ≤ N) {i j : Fin N}
    (hij : i ≠ j) (c : A) : zElt hN Y m i j (-c) = (zElt hN Y m i j c)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [h.zElt_add hm hN hN5 hij, neg_add_cancel, h.zElt_zero hN]

end Level

/-! ### The extended family -/

section Extend

variable {A : Type*} [CommRing A] {𝔄 : Ideal A} {G : Type*} [Group G] {N : ℕ}

/-- **The extension to degree `m + 1`.** -/
noncomputable def extend (hN : 3 ≤ N) (Y : Fam G A N) (m : ℤ) : Fam G A N :=
  fun i j hij d c => if d = m + 1 then zElt hN Y m i j c else Y i j hij d c

variable {Y : Fam G A N} {m : ℤ}

theorem extend_of_ne (hN : 3 ≤ N) {i j : Fin N} (hij : i ≠ j) {d : ℤ} (hd : d ≠ m + 1) (c : A) :
    extend hN Y m i j hij d c = Y i j hij d c :=
  if_neg hd

theorem extend_top (hN : 3 ≤ N) {i j : Fin N} (hij : i ≠ j) (c : A) :
    extend hN Y m i j hij (m + 1) c = zElt hN Y m i j c :=
  if_pos rfl

theorem extend_of_le (hN : 3 ≤ N) {i j : Fin N} (hij : i ≠ j) {d : ℤ} (hd : d ≤ m) (c : A) :
    extend hN Y m i j hij d c = Y i j hij d c :=
  extend_of_ne hN hij (by omega) c

theorem Rels.extend_add (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) (hN5 : 5 ≤ N)
    (i j : Fin N) (hij : i ≠ j) (d : ℤ) (c c' : A) (hd : d ≤ m + 1) (hc : Allowed 𝔄 d c)
    (hc' : Allowed 𝔄 d c') :
    extend hN Y m i j hij d c * extend hN Y m i j hij d c' = extend hN Y m i j hij d (c + c') := by
  rcases lt_or_eq_of_le hd with hlt | rfl
  · rw [extend_of_le (m := m) hN hij (d := d) (by omega), extend_of_le (m := m) hN hij (d := d) (by omega),
      extend_of_le (m := m) hN hij (d := d) (by omega)]
    exact h.add i j hij d c c' (by omega) hc hc'
  · rw [extend_top, extend_top, extend_top]
    exact h.zElt_add hm hN hN5 hij c c'

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.extend_add

theorem Rels.extend_r3 (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) (hN5 : 5 ≤ N)
    (i j k l : Fin N) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l) (d e : ℤ) (c c' : A)
    (hd : d ≤ m + 1) (he : e ≤ m + 1) (hc : Allowed 𝔄 d c) (hc' : Allowed 𝔄 e c') :
    ⁅extend hN Y m i j hij d c, extend hN Y m k l hkl e c'⁆ = 1 := by
  rcases lt_or_eq_of_le hd with hdlt | rfl <;> rcases lt_or_eq_of_le he with helt | rfl
  · rw [extend_of_le (m := m) hN hij (d := d) (by omega), extend_of_le (m := m) hN hkl (d := e) (by omega)]
    exact h.r3 i j k l hij hkl hjk hil d e c c' (by omega) (by omega) hc hc'
  · rw [extend_of_le (m := m) hN hij (d := d) (by omega), extend_top]
    exact comm_eq_one_of_commute
      (h.zElt_commute hm hN hN5 hkl hij hil.symm hjk.symm (by omega) hc c').symm
  · rw [extend_top, extend_of_le (m := m) hN hkl (d := e) (by omega)]
    exact comm_eq_one_of_commute (h.zElt_commute hm hN hN5 hij hkl hjk hil (by omega) hc' c)
  · rw [extend_top, extend_top]
    exact comm_eq_one_of_commute (h.zElt_commute_zElt hm hN hN5 hij hkl hjk hil c c')

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.extend_r3

theorem Rels.extend_commute (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) (hN5 : 5 ≤ N)
    {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l) {d e : ℤ}
    (hd : d ≤ m + 1) (he : e ≤ m + 1) {c c' : A} (hc : Allowed 𝔄 d c) (hc' : Allowed 𝔄 e c') :
    Commute (extend hN Y m i j hij d c) (extend hN Y m k l hkl e c') :=
  commute_of_comm_eq_one (h.extend_r3 hm hN hN5 i j k l hij hkl hjk hil d e c c' hd he hc hc')

/-- `⁅Y^m_ih(x), Y^{1+e}_hk(c')⁆ = Y'^{m+1+e}_ik(x c')` for `e ≤ 0`, in the extended family. -/
theorem Rels.comm_top_eq_extend (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) (hN5 : 5 ≤ N)
    {i h' k : Fin N} (hih : i ≠ h') (hhk : h' ≠ k) (hik : i ≠ k) {e : ℤ} (he : e ≤ 0)
    {c' : A} (hc' : Allowed 𝔄 e c') (x : A) :
    ⁅Y i h' hih m x, Y h' k hhk (1 + e) c'⁆ = extend hN Y m i k hik (m + 1 + e) (x * c') := by
  rcases lt_or_eq_of_le he with helt | rfl
  · rw [extend_of_le (m := m) hN hik (d := m + 1 + e) (by omega),
      h.r2 i h' k hih hhk hik m (1 + e) x c' le_rfl (by omega) (by omega) (allowed_of_nonneg (by omega) _) (fun h1 => hc' (by omega)),
      show m + (1 + e) = m + 1 + e by ring]
  · rw [show m + 1 + 0 = m + 1 by ring, extend_top]
    exact h.comm_eq_zElt hm hN (by omega) hik hih hhk (by omega) (by omega) (by omega) x c'

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.comm_top_eq_extend

/-- **Relation `R2_{m+1,e}`, `e ≤ 0`.** -/
theorem Rels.zElt_r2_left (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) (hN5 : 5 ≤ N)
    {i j k : Fin N} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {e : ℤ} (he : e ≤ 0) {c' : A}
    (hc' : Allowed 𝔄 e c') (c : A) :
    ⁅zElt hN Y m i j c, Y j k hjk e c'⁆ = extend hN Y m i k hik (m + 1 + e) (c * c') := by
  obtain ⟨h', h1, h2, h3⟩ := fresh3 (by omega : 4 ≤ N) i j k
  have hih : i ≠ h' := h1.symm
  have hhj : h' ≠ j := h2
  have hhk : h' ≠ k := h3
  have hc'1 : Allowed 𝔄 (1 + e) c' := fun h1 => hc' (by omega)
  have hW_neg : ∀ x : A, extend hN Y m i k hik (m + 1 + e) (-x) =
      (extend hN Y m i k hik (m + 1 + e) x)⁻¹ := by
    intro x
    refine eq_inv_of_mul_eq_one_left ?_
    rw [h.extend_add hm hN hN5 i k hik (m + 1 + e) (-x) x (by omega)
      (allowed_of_nonneg (by omega) _) (allowed_of_nonneg (by omega) _), neg_add_cancel]
    rcases lt_or_eq_of_le he with helt | rfl
    · rw [extend_of_le (m := m) hN hik (d := m + 1 + e) (by omega), h.one hik (d := m + 1 + e) (by omega)]
    · rw [show m + 1 + 0 = m + 1 by ring, extend_top, h.zElt_zero hN]
  have hby : ⁅Y h' j hhj 1 1, Y j k hjk e c'⁆ = Y h' k hhk (1 + e) c' := by
    rw [h.r2 h' j k hhj hjk hhk 1 e 1 c' hm (by omega) (by omega)
      (allowed_of_nonneg (by omega) _) hc', one_mul]
  -- the key computation, for an arbitrary coefficient `x`
  have key : ∀ x : A, ⁅Y j k hjk e c', (zElt hN Y m i j x)⁻¹⁆ =
      extend hN Y m i k hik (m + 1 + e) (x * c') := by
    intro x
    have hya : Commute (Y j k hjk e c') (Y i h' hih m x) :=
      h.commute hjk hih hik.symm hhj.symm (by omega) le_rfl hc' (allowed_of_nonneg (by omega) _)
    have hinv : (zElt hN Y m i j x)⁻¹ = ⁅Y h' j hhj 1 1, Y i h' hih m x⁆ := by
      rw [← h.zElt_eq hm hN hij hih hhj x, commutatorElement_inv]
    rw [hinv, comm_comm_of_commute _ _ _ hya,
      conj_eq_comm_mul (Y h' j hhj 1 1) (Y i h' hih m x), ← hinv,
      ← commutatorElement_inv (Y h' j hhj 1 1) (Y j k hjk e c'), hby, comm_mul_right']
    have hvZ : Commute (Y h' k hhk (1 + e) c') (zElt hN Y m i j x) :=
      (h.zElt_commute hm hN hN5 hij hhk hhj.symm hik (by omega) hc'1 x).symm
    have hv1 : ⁅(Y h' k hhk (1 + e) c')⁻¹, (zElt hN Y m i j x)⁻¹⁆ = 1 :=
      comm_eq_one_of_commute hvZ.inv_left.inv_right
    have hav : ⁅Y i h' hih m x, Y h' k hhk (1 + e) c'⁆ =
        extend hN Y m i k hik (m + 1 + e) (x * c') :=
      h.comm_top_eq_extend hm hN hN5 hih hhk hik he hc' x
    have hvW : Commute (Y h' k hhk (1 + e) c') (extend hN Y m i k hik (m + 1 + e) (x * c')) := by
      have hc := h.extend_commute hm hN hN5 hhk hik hik.symm hhk (d := 1 + e) (e := m + 1 + e)
        (by omega) (by omega) (c := c') (c' := x * c') hc'1 (allowed_of_nonneg (by omega) _)
      rw [extend_of_le (m := m) hN hhk (d := 1 + e) (by omega)] at hc
      exact hc
    have hv2 : ⁅(Y h' k hhk (1 + e) c')⁻¹, Y i h' hih m x⁆ =
        extend hN Y m i k hik (m + 1 + e) (x * c') := by
      rw [commutatorElement_inv_left, hav, hvW.inv_left.eq, inv_mul_cancel_right]
    have hZW : Commute (zElt hN Y m i j x) (extend hN Y m i k hik (m + 1 + e) (x * c')) := by
      have hc := h.extend_commute hm hN hN5 hij hik hij.symm hik (d := m + 1) (e := m + 1 + e)
        le_rfl (by omega) (c := x) (c' := x * c') (allowed_of_nonneg (by omega) _)
        (allowed_of_nonneg (by omega) _)
      rw [extend_top] at hc
      exact hc
    rw [hv1, one_mul, hv2, inv_inv, hZW.inv_left.eq, inv_mul_cancel_right]
  -- conclude
  have hneg := key (-c)
  rw [h.zElt_neg hm hN hN5 hij, inv_inv, neg_mul, hW_neg] at hneg
  rw [← commutatorElement_inv (Y j k hjk e c') (zElt hN Y m i j c), hneg, inv_inv]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.zElt_r2_left

/-- **Relation `R2_{d,m+1}`, `d ≤ 0`.** -/
theorem Rels.zElt_r2_right (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) (hN5 : 5 ≤ N)
    {i j k : Fin N} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {d : ℤ} (hd : d ≤ 0) {c : A}
    (hc : Allowed 𝔄 d c) (c' : A) :
    ⁅Y i j hij d c, zElt hN Y m j k c'⁆ = extend hN Y m i k hik (d + (m + 1)) (c * c') := by
  obtain ⟨h', h1, h2, h3⟩ := fresh3 (by omega : 4 ≤ N) i j k
  have hih : i ≠ h' := h1.symm
  have hjh : j ≠ h' := h2.symm
  have hhk : h' ≠ k := h3
  have hxz : Commute (Y i j hij d c) (Y h' k hhk 1 1) :=
    h.commute hij hhk hjh hik (by omega) hm hc (allowed_of_nonneg (by omega) _)
  have hallow : Allowed 𝔄 (d + m) (c * c') := hc.mul (allowed_of_nonneg (by omega) c')
  rw [← h.zElt_eq hm hN hjk hjh hhk c', comm_comm_of_commute _ _ _ hxz,
    h.r2 i j h' hij hjh hih d m c c' (by omega) le_rfl (by omega) hc
      (allowed_of_nonneg (by omega) _),
    conj_eq_comm_mul (Y j h' hjh m c') (Y h' k hhk 1 1), h.zElt_eq hm hN hjk hjh hhk c', comm_mul_right']
  have hwZ : ⁅Y i h' hih (d + m) (c * c'), zElt hN Y m j k c'⁆ = 1 :=
    comm_eq_one_of_commute
      (h.zElt_commute hm hN hN5 hjk hih hik.symm hjh (by omega) hallow c').symm
  have hwz : ⁅Y i h' hih (d + m) (c * c'), Y h' k hhk 1 1⁆ =
      extend hN Y m i k hik (d + (m + 1)) (c * c') := by
    rcases lt_or_eq_of_le hd with hlt | rfl
    · rw [extend_of_le (m := m) hN hik (d := d + (m + 1)) (by omega),
        h.r2 i h' k hih hhk hik (d + m) 1 (c * c') 1 (by omega) hm (by omega) hallow (allowed_of_nonneg (by omega) _), mul_one,
        show d + m + 1 = d + (m + 1) by ring]
    · rw [show (0 : ℤ) + (m + 1) = m + 1 by ring, extend_top]
      have := h.comm_eq_zElt hm hN (by omega) hik hih hhk (p := 0 + m) (q := 1) (by ring) le_rfl
        hm (c * c') 1
      rwa [mul_one] at this
  have hZW : Commute (zElt hN Y m j k c') (extend hN Y m i k hik (d + (m + 1)) (c * c')) := by
    have := h.extend_commute hm hN hN5 hjk hik hik.symm hjk (d := m + 1) (e := d + (m + 1))
      le_rfl (by omega) (c := c') (c' := c * c') (allowed_of_nonneg (by omega) _)
      (allowed_of_nonneg (by omega) _)
    rwa [extend_top] at this
  rw [hwZ, one_mul, hwz, conj_eq_of_commute hZW]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.zElt_r2_right

theorem Rels.extend_r2 (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) (hN5 : 5 ≤ N)
    (i j k : Fin N) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (d e : ℤ) (c c' : A)
    (hd : d ≤ m + 1) (he : e ≤ m + 1) (hde : d + e ≤ m + 1) (hc : Allowed 𝔄 d c)
    (hc' : Allowed 𝔄 e c') :
    ⁅extend hN Y m i j hij d c, extend hN Y m j k hjk e c'⁆ =
      extend hN Y m i k hik (d + e) (c * c') := by
  rcases lt_or_eq_of_le hd with hdlt | rfl
  · rcases lt_or_eq_of_le he with helt | rfl
    · rw [extend_of_le (m := m) hN hij (d := d) (by omega), extend_of_le (m := m) hN hjk (d := e) (by omega)]
      rcases lt_or_eq_of_le hde with hdelt | hdeq
      · rw [extend_of_le (m := m) hN hik (d := d + e) (by omega)]
        exact h.r2 i j k hij hjk hik d e c c' (by omega) (by omega) (by omega) hc hc'
      · rw [hdeq, extend_top]
        exact h.comm_eq_zElt hm hN (by omega) hik hij hjk hdeq (by omega) (by omega) c c'
    · rw [extend_of_le (m := m) hN hij (d := d) (by omega), extend_top]
      exact h.zElt_r2_right hm hN hN5 hij hjk hik (by omega) hc c'
  · rw [extend_top, extend_of_le (m := m) hN hjk (d := e) (by omega)]
    exact h.zElt_r2_left hm hN hN5 hij hjk hik (by omega) hc' c

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.extend_r2

/-- **Tulenbaev, Lemma 3.3 (one step).** For `N ≥ 5` and `m ≥ 1`, the extension of a family
satisfying the homogeneous Steinberg relations of degree `≤ m` satisfies those of degree
`≤ m + 1`. -/
theorem Rels.rels_extend (h : Rels 𝔄 Y m) (hm : 1 ≤ m) (hN : 3 ≤ N) (hN5 : 5 ≤ N) :
    Rels 𝔄 (extend hN Y m) (m + 1) where
  add i j hij d c c' hd hc hc' := h.extend_add hm hN hN5 i j hij d c c' hd hc hc'
  r2 i j k hij hjk hik d e c c' hd he hde hc hc' :=
    h.extend_r2 hm hN hN5 i j k hij hjk hik d e c c' hd he hde hc hc'
  r3 i j k l hij hkl hjk hil d e c c' hd he hc hc' :=
    h.extend_r3 hm hN hN5 i j k l hij hkl hjk hil d e c c' hd he hc hc'

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Rels.rels_extend

end Extend

end Graded
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
