import GroupApproximation.Sofic.ProjectionCompressionCollapse
import GroupApproximation.Sofic.TorsionCompressionCollapse

/-!
# Torsion witnesses collapse at every order

The involutive collapse endpoint discharges the analytic gate of the
torsion-collapse program for witnesses of order two.  This file closes
the remaining orders unconditionally: every finite-order compression
witness with commuting orbit is identified with its entire orbit in
every corona representation.

No new analysis appears.  The represented witness `v` satisfies
`v ^ m = 1`, so its spectral projections are the explicit Fourier
idempotents `m⁻¹ • ∑_t ζ^{jt} • v^t` for a primitive `m`-th root of
unity `ζ` — finite linear algebra, no functional calculus.  Each is a
self-adjoint idempotent commuting with everything the powers of `v`
commute with, and conjugation carries the idempotents of `v` to the
idempotents of the conjugated witness; the projection-orbit collapse of
`Sofic/ProjectionCompressionCollapse` therefore fixes every idempotent
under the Kazhdan image, and the Fourier reconstruction of `v` from its
idempotents fixes `v` itself.  This discharges the `hkill` gate of
`Sofic/TorsionCompressionCollapse`: the full torsion-collapse defect
lies in the literal MF radical whenever `L` is Kazhdan and `s` is a
one-sided compressor.
-/

namespace GroupApproximation
namespace TorsionSpectralCollapse

open Finset

/-! ## Modular power bookkeeping -/

theorem pow_mod_of_pow_eq_one {A : Type*} [Monoid A] {v : A} {m : ℕ}
    (hv : v ^ m = 1) (a : ℕ) : v ^ a = v ^ (a % m) := by
  conv_lhs => rw [← Nat.div_add_mod a m]
  rw [pow_add, pow_mul, hv, one_pow, one_mul]

theorem pow_eq_pow_of_mod_eq {A : Type*} [Monoid A] {v : A} {m : ℕ}
    (hv : v ^ m = 1) {a b : ℕ} (hab : a % m = b % m) :
    v ^ a = v ^ b := by
  rw [pow_mod_of_pow_eq_one hv a, pow_mod_of_pow_eq_one hv b, hab]

theorem val_add_mod {M : ℕ} [NeZero M] (a b : ZMod M) :
    (ZMod.val a + ZMod.val b) % M = ZMod.val (a + b) % M := by
  rw [ZMod.val_add]
  exact (Nat.mod_mod_of_dvd _ dvd_rfl).symm

/-- The inverse-through-star identity in a unitary coercion. -/
theorem unitary_coe_inv {A : Type*} [Monoid A] [StarMul A]
    (u : unitary A) :
    ((u⁻¹ : unitary A) : A) = star (u : A) := by
  rw [← unitary.star_eq_inv, unitary.coe_star]

/-! ## The character sum -/

/-- Summing a character of `ZMod M` built from a primitive `M`-th root of
unity over the whole group gives `M` at the trivial character and zero
otherwise. -/
theorem char_sum (M : ℕ) [NeZero M] {ζ : ℂ} (hprim : IsPrimitiveRoot ζ M)
    (s : ZMod M) :
    (∑ j : ZMod M, ζ ^ (ZMod.val j * ZMod.val s)) =
      if s = 0 then (M : ℂ) else 0 := by
  classical
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 :=
    ⟨M - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne M))).symm⟩
  have hterm : ∀ j : ZMod (M' + 1),
      ζ ^ (ZMod.val j * ZMod.val s) = (ζ ^ ZMod.val s) ^ ZMod.val j := by
    intro j
    rw [← pow_mul, Nat.mul_comm]
  have hrange : (∑ j : ZMod (M' + 1), ζ ^ (ZMod.val j * ZMod.val s)) =
      ∑ i ∈ Finset.range (M' + 1), (ζ ^ ZMod.val s) ^ i := by
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j]
    exact Fin.sum_univ_eq_sum_range (fun i ↦ (ζ ^ ZMod.val s) ^ i) (M' + 1)
  rw [hrange]
  by_cases hs : s = 0
  · subst hs
    rw [if_pos rfl, ZMod.val_zero, pow_zero]
    simp [Finset.sum_const, Finset.card_range]
  · rw [if_neg hs]
    have hvpos : ZMod.val s ≠ 0 := fun h ↦ hs ((ZMod.val_eq_zero s).mp h)
    have hx1 : ζ ^ ZMod.val s ≠ 1 :=
      hprim.pow_ne_one_of_pos_of_lt hvpos (ZMod.val_lt s)
    rw [geom_sum_eq hx1]
    have hxM : (ζ ^ ZMod.val s) ^ (M' + 1) = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    rw [hxM, sub_self, zero_div]

/-! ## Fourier idempotents of a finite-order unitary -/

section Fourier

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {M : ℕ} [NeZero M] {ζ : ℂ} {v : A}

/-- The `j`-th Fourier idempotent of an element with `v ^ M = 1`. -/
noncomputable def fourierIdem (ζ : ℂ) (M : ℕ) [NeZero M] (v : A)
    (j : ZMod M) : A :=
  (M : ℂ)⁻¹ • ∑ t : ZMod M, ζ ^ (ZMod.val j * ZMod.val t) • v ^ ZMod.val t

theorem fourier_char_mul (hζM : ζ ^ M = 1) (j a b : ZMod M) :
    ζ ^ (ZMod.val j * ZMod.val a) * ζ ^ (ZMod.val j * ZMod.val b) =
      ζ ^ (ZMod.val j * ZMod.val (a + b)) := by
  rw [← pow_add, ← Nat.mul_add,
    pow_eq_pow_of_mod_eq hζM (Nat.ModEq.mul_left (ZMod.val j)
      (val_add_mod a b))]

theorem fourier_pow_mul (hvM : v ^ M = 1) (a b : ZMod M) :
    v ^ ZMod.val a * v ^ ZMod.val b = v ^ ZMod.val (a + b) := by
  rw [← pow_add, pow_eq_pow_of_mod_eq hvM (val_add_mod a b)]

theorem fourier_term_mul (hζM : ζ ^ M = 1) (hvM : v ^ M = 1)
    (j t u : ZMod M) :
    (ζ ^ (ZMod.val j * ZMod.val t) • v ^ ZMod.val t) *
      (ζ ^ (ZMod.val j * ZMod.val u) • v ^ ZMod.val u) =
    ζ ^ (ZMod.val j * ZMod.val (t + u)) • v ^ ZMod.val (t + u) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, fourier_char_mul hζM,
    fourier_pow_mul hvM]

theorem fourier_char_inv (hζM : ζ ^ M = 1) (j t : ZMod M) :
    ζ ^ (ZMod.val j * ZMod.val t) * ζ ^ (ZMod.val j * ZMod.val (-t)) =
      1 := by
  rw [fourier_char_mul hζM, add_neg_cancel]
  have h0 : ZMod.val j * ZMod.val (0 : ZMod M) = 0 := by
    rw [ZMod.val_zero, Nat.mul_zero]
  rw [h0, pow_zero]

theorem fourier_pow_inv (hvM : v ^ M = 1) (t : ZMod M) :
    v ^ ZMod.val t * v ^ ZMod.val (-t) = 1 := by
  rw [fourier_pow_mul hvM, add_neg_cancel, ZMod.val_zero, pow_zero]

theorem fourier_term_star (hζM : ζ ^ M = 1) (hζnorm : ‖ζ‖ = 1)
    (hv : v ∈ unitary A) (hvM : v ^ M = 1) (j t : ZMod M) :
    star (ζ ^ (ZMod.val j * ZMod.val t) • v ^ ZMod.val t) =
      ζ ^ (ZMod.val j * ZMod.val (-t)) • v ^ ZMod.val (-t) := by
  rw [star_smul]
  congr 1
  · show star (ζ ^ (ZMod.val j * ZMod.val t)) =
      ζ ^ (ZMod.val j * ZMod.val (-t))
    have hz1 : ‖ζ ^ (ZMod.val j * ZMod.val t)‖ = 1 := by
      rw [norm_pow, hζnorm, one_pow]
    have hc : ζ ^ (ZMod.val j * ZMod.val t) *
        star (ζ ^ (ZMod.val j * ZMod.val t)) = 1 := by
      have := Complex.mul_conj (ζ ^ (ZMod.val j * ZMod.val t))
      rw [Complex.normSq_eq_norm_sq, hz1] at this
      simpa using this
    calc star (ζ ^ (ZMod.val j * ZMod.val t)) =
        (ζ ^ (ZMod.val j * ZMod.val t))⁻¹ :=
          (inv_eq_of_mul_eq_one_right hc).symm
      _ = ζ ^ (ZMod.val j * ZMod.val (-t)) :=
          inv_eq_of_mul_eq_one_right (fourier_char_inv hζM j t)
  · have h1 : v ^ ZMod.val t * v ^ ZMod.val (-t) = 1 :=
      fourier_pow_inv hvM t
    have hmem : v ^ ZMod.val t ∈ unitary A := pow_mem hv _
    calc star (v ^ ZMod.val t) =
        star (v ^ ZMod.val t) * (v ^ ZMod.val t * v ^ ZMod.val (-t)) := by
          rw [h1, mul_one]
      _ = (star (v ^ ZMod.val t) * v ^ ZMod.val t) * v ^ ZMod.val (-t) := by
          rw [mul_assoc]
      _ = v ^ ZMod.val (-t) := by
          rw [unitary.star_mul_self_of_mem hmem, one_mul]

/-- The Fourier idempotents are self-adjoint. -/
theorem star_fourierIdem (hζM : ζ ^ M = 1) (hζnorm : ‖ζ‖ = 1)
    (hv : v ∈ unitary A) (hvM : v ^ M = 1) (j : ZMod M) :
    star (fourierIdem ζ M v j) = fourierIdem ζ M v j := by
  unfold fourierIdem
  rw [star_smul, star_inv₀, star_natCast, star_sum]
  congr 1
  rw [Finset.sum_congr rfl fun t _ ↦
    fourier_term_star hζM hζnorm hv hvM j t]
  exact Fintype.sum_equiv (Equiv.neg (ZMod M)) _ _
    (fun t ↦ by rw [Equiv.neg_apply])

/-- The Fourier idempotents are idempotent. -/
theorem fourierIdem_mul_self (hζM : ζ ^ M = 1) (hvM : v ^ M = 1)
    (j : ZMod M) :
    fourierIdem ζ M v j * fourierIdem ζ M v j = fourierIdem ζ M v j := by
  unfold fourierIdem
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun u _ ↦
    fourier_term_mul hζM hvM j t u]
  have hinner : ∀ t : ZMod M,
      (∑ u : ZMod M,
        ζ ^ (ZMod.val j * ZMod.val (t + u)) • v ^ ZMod.val (t + u)) =
      ∑ u : ZMod M, ζ ^ (ZMod.val j * ZMod.val u) • v ^ ZMod.val u := by
    intro t
    exact Fintype.sum_equiv (Equiv.addLeft t) _ _
      (fun u ↦ by rw [Equiv.coe_addLeft])
  rw [Finset.sum_congr rfl fun t _ ↦ hinner t, Finset.sum_const,
    Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  field_simp

/-- Everything commuting with `v` commutes with its Fourier idempotents. -/
theorem commute_fourierIdem {g : A} (hgv : Commute g v) (j : ZMod M) :
    Commute g (fourierIdem ζ M v j) := by
  unfold fourierIdem
  refine Commute.smul_right ?_ _
  refine Commute.sum_right _ _ _ fun t _ ↦ ?_
  exact Commute.smul_right (hgv.pow_right _) _

/-- Fourier idempotents of commuting finite-order elements commute. -/
theorem commute_fourierIdem_fourierIdem {v₁ v₂ : A} (h : Commute v₁ v₂)
    (j j' : ZMod M) :
    Commute (fourierIdem ζ M v₁ j) (fourierIdem ζ M v₂ j') := by
  unfold fourierIdem
  refine Commute.smul_right (Commute.smul_left ?_ _) _
  refine Commute.sum_left _ _ _ fun t _ ↦ ?_
  refine Commute.sum_right _ _ _ fun u _ ↦ ?_
  exact Commute.smul_right (Commute.smul_left (h.pow_pow _ _) _) _

theorem conj_pow {g v : A} (hg1 : g * star g = 1) (hg2 : star g * g = 1)
    (n : ℕ) : g * v ^ n * star g = (g * v * star g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mul_one, hg1]
  | succ n ih =>
      calc g * v ^ (n + 1) * star g
          = g * v ^ n * (star g * g) * (v * star g) := by
            rw [hg2, mul_one, pow_succ]
            noncomm_ring
        _ = (g * v ^ n * star g) * (g * v * star g) := by noncomm_ring
        _ = (g * v * star g) ^ (n + 1) := by rw [ih, pow_succ]

/-- Conjugation carries the Fourier idempotents of `v` to the Fourier
idempotents of the conjugated element. -/
theorem conj_fourierIdem {g : A} (hg1 : g * star g = 1)
    (hg2 : star g * g = 1) (j : ZMod M) :
    g * fourierIdem ζ M v j * star g =
      fourierIdem ζ M (g * v * star g) j := by
  unfold fourierIdem
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [mul_smul_comm, smul_mul_assoc, conj_pow hg1 hg2]

/-- Fourier reconstruction: the element is recovered from its
idempotents. -/
theorem fourierIdem_reconstruct (hprim : IsPrimitiveRoot ζ M)
    (hvM : v ^ M = 1) :
    (∑ j : ZMod M, ζ ^ (ZMod.val j * ZMod.val (-1 : ZMod M)) •
      fourierIdem ζ M v j) = v := by
  classical
  have hζM : ζ ^ M = 1 := hprim.pow_eq_one
  have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  unfold fourierIdem
  have hstep : ∀ j : ZMod M,
      ζ ^ (ZMod.val j * ZMod.val (-1 : ZMod M)) •
        ((M : ℂ)⁻¹ •
          ∑ t : ZMod M, ζ ^ (ZMod.val j * ZMod.val t) • v ^ ZMod.val t) =
      (M : ℂ)⁻¹ • ∑ t : ZMod M,
        ζ ^ (ZMod.val j * ZMod.val (-1 + t)) • v ^ ZMod.val t := by
    intro j
    rw [smul_comm, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [smul_smul, fourier_char_mul hζM]
  rw [Finset.sum_congr rfl fun j _ ↦ hstep j, ← Finset.smul_sum,
    Finset.sum_comm]
  have hinner : ∀ t : ZMod M,
      (∑ j : ZMod M,
        ζ ^ (ZMod.val j * ZMod.val (-1 + t)) • v ^ ZMod.val t) =
      (if (-1 + t : ZMod M) = 0 then (M : ℂ) else 0) • v ^ ZMod.val t := by
    intro t
    rw [← Finset.sum_smul, char_sum M hprim (-1 + t)]
  rw [Finset.sum_congr rfl fun t _ ↦ hinner t]
  rw [Finset.sum_eq_single (1 : ZMod M)]
  · rw [if_pos (by rw [neg_add_cancel]), smul_smul,
      inv_mul_cancel₀ hM0, one_smul]
    have h1 : ((1 : ℕ) : ZMod M) = (1 : ZMod M) := Nat.cast_one
    rw [← h1, ZMod.val_natCast]
    conv_rhs => rw [← pow_one v]
    exact (pow_mod_of_pow_eq_one hvM 1).symm
  · intro t _ ht
    rw [if_neg fun hc ↦ ht (neg_add_eq_zero.mp hc).symm, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Fourier

/-! ## The unconditional torsion collapse -/

/-- **Unconditional collapse of torsion witnesses.**  For a countable
ambient group, a Kazhdan subgroup with a one-sided compressor, and a
finite-order witness with commuting orbit, every collapse commutator is
invisible in every corona representation.  This discharges the collapse
gate of `Sofic/TorsionCompressionCollapse` at every order, extending the
involutive endpoint from order two. -/
theorem actualCoronaMFInvisible_of_torsionWitness {E : Type} [Group E]
    [Countable E] {L : Subgroup E} (hT : HasKazhdanPropertyT.{0, 0} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L) {k : E}
    (hk : TorsionCompressionCollapse.IsTorsionCompressionWitness L s k)
    {γ : E} (hγ : γ ∈ L) :
    ActualCoronaMFInvisible ⁅γ, k⁆ := by
  classical
  obtain ⟨⟨m, hm, hkm⟩, hcent, horb⟩ := hk
  haveI : NeZero m := ⟨hm.ne'⟩
  intro X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hζdef
  have hprim : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm.ne'
  have hζM : ζ ^ m = 1 := hprim.pow_eq_one
  have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζM hm.ne'
  set v : NormMatrixCStarCorona (fun n ↦ X n) :=
    ((rho k : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
      NormMatrixCStarCorona (fun n ↦ X n)) with hvdef
  have hvmem : v ∈ unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
    (rho k).2
  have hvM : v ^ m = 1 := by
    have hpow : rho k ^ m = 1 := by rw [← map_pow, hkm, map_one]
    rw [hvdef, ← SubmonoidClass.coe_pow, hpow]
    rfl
  -- the A-level commute transfer
  have hcoe_commute : ∀ a b : E, Commute a b →
      Commute
        ((rho a : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n))
        ((rho b : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) := by
    intro a b hab
    have h := (hab.map rho).eq
    exact congrArg
      (fun u : unitary (NormMatrixCStarCorona (fun n ↦ X n)) ↦
        (u : NormMatrixCStarCorona (fun n ↦ X n))) h
  -- conjugated witness values
  have hconj_val : ∀ δ : E,
      ((rho δ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * v *
        star ((rho δ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) =
      ((rho (δ * k * δ⁻¹) :
          unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) := by
    intro δ
    rw [map_mul, map_mul, map_inv]
    have hcoe : ((rho δ * rho k * (rho δ)⁻¹ :
        unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) =
        ((rho δ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * v *
          (((rho δ)⁻¹ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) := rfl
    rw [hcoe, unitary_coe_inv]
  -- collapse each Fourier idempotent
  have hfix : ∀ (j : ZMod m), ∀ δ ∈ L,
      ((rho δ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * fourierIdem ζ m v j =
        fourierIdem ζ m v j *
          ((rho δ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) := by
    intro j
    refine ProjectionCompressionCollapse.corona_projection_collapse L hT
      hcomp X hX rho (fourierIdem ζ m v j)
      (star_fourierIdem hζM hζnorm hvmem hvM j)
      (fourierIdem_mul_self hζM hvM j) ?_ ?_
    · intro δ hδ
      exact (commute_fourierIdem
        (hcoe_commute _ _ (hcent δ hδ)) j).eq
    · intro δ₁ hδ₁ δ₂ hδ₂
      have hg1 : ∀ δ : E,
          ((rho δ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
              NormMatrixCStarCorona (fun n ↦ X n)) *
            star ((rho δ :
                unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
              NormMatrixCStarCorona (fun n ↦ X n)) = 1 :=
        fun δ ↦ unitary.mul_star_self_of_mem (rho δ).2
      have hg2 : ∀ δ : E,
          star ((rho δ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
              NormMatrixCStarCorona (fun n ↦ X n)) *
            ((rho δ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
              NormMatrixCStarCorona (fun n ↦ X n)) = 1 :=
        fun δ ↦ unitary.star_mul_self_of_mem (rho δ).2
      rw [conj_fourierIdem (hg1 δ₁) (hg2 δ₁) j,
        conj_fourierIdem (hg1 δ₂) (hg2 δ₂) j,
        hconj_val δ₁, hconj_val δ₂]
      exact commute_fourierIdem_fourierIdem
        (hcoe_commute _ _ (horb δ₁ hδ₁ δ₂ hδ₂)) j j
  -- reconstruct and conclude
  have hgv : Commute
      ((rho γ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) v := by
    rw [← fourierIdem_reconstruct hprim hvM]
    refine Commute.sum_right _ _ _ fun j _ ↦ ?_
    exact Commute.smul_right (hfix j γ hγ) _
  have hunit : rho γ * rho k = rho k * rho γ := Subtype.ext hgv.eq
  have hcommU : ⁅rho γ, rho k⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr hunit
  rw [map_commutatorElement]
  exact hcommU

/-! ## Unconditional endpoints -/

/-- **The full torsion-collapse defect lies in the MF radical**, with no
analytic hypothesis: the collapse gate of
`Sofic/TorsionCompressionCollapse` is discharged at every order. -/
theorem torsionCollapseDefect_le_actualCoronaMFResidual_of_kazhdan
    {E : Type} [Group E] [Countable E] {L : Subgroup E}
    (hT : HasKazhdanPropertyT.{0, 0} ↥L) {s : E}
    (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L) :
    TorsionCompressionCollapse.torsionCollapseDefect L s ≤
      actualCoronaMFResidual E := by
  refine TorsionCompressionCollapse.torsionCollapseDefect_le_actualCoronaMFResidual
    L s ?_
  rintro x ⟨k, hk, γ, hγ, rfl⟩
  exact actualCoronaMFInvisible_of_torsionWitness hT hcomp hk hγ

/-- **Exact MF radical from the torsion collapse**: if the defect
quotient is MF, the torsion-collapse defect is exactly the literal MF
radical. -/
theorem actualCoronaMFResidual_eq_torsionCollapseDefect_of_kazhdan
    {E : Type} [Group E] [Countable E] {L : Subgroup E}
    (hT : HasKazhdanPropertyT.{0, 0} ↥L) {s : E}
    (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (hquot : IsCDEOperatorMF
      (E ⧸ TorsionCompressionCollapse.torsionCollapseDefect L s)) :
    actualCoronaMFResidual E =
      TorsionCompressionCollapse.torsionCollapseDefect L s :=
  actualCoronaMFResidual_eq_of_le_and_quotient_isCDEOperatorMF
    (TorsionCompressionCollapse.torsionCollapseDefect L s)
    (torsionCollapseDefect_le_actualCoronaMFResidual_of_kazhdan hT hcomp)
    hquot

end TorsionSpectralCollapse
end GroupApproximation
