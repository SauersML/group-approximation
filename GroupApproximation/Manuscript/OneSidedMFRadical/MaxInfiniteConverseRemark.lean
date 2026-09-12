import GroupApproximation.Sofic.MarkedCompressionGroup
import GroupApproximation.Monsters.LiteralBaseCompleteness
import GroupApproximation.Sofic.LiteralBaseP13PropertyTBridge
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Meta.AxiomGuard

/-!
# The converse remark after `prop:max-infinite`

`non_mf_groups_exist.tex`, the paragraph beginning

> A group can satisfy the hypothesis of Proposition~`prop:max-infinite` and be
> MF.  The ascending HNN extension `V` of `ℤ³ ⋊ SL₃(ℤ)` along `(v,A) ↦ (2v,A)`,
> used in Section~`sec:amenable-nonqd`, has the faithful matrix realization …
> and reduction modulo odd integers separates its elements, so `V` is
> residually finite and MF.  So the lamps of Section~`sec:amenable-nonqd` are
> necessary for the non-MF conclusion there.

`V` is `MarkedCompression.Vertical conjD conjD_injective`: the mapping
telescope of the doubling self-embedding of `Γ̄ = ℤ³ ⋊ SL₃(ℤ)`, extended by the
shift.  That is the same group Section `sec:amenable-nonqd` builds its witness
over, before the lamps are attached, which is what makes the remark's last
sentence a comparison rather than a coincidence.

## What is proved, and by which route

The remark's content is that `V` satisfies the hypothesis of
`prop:max-infinite` and is MF.  Both are proved here.

**The printed matrix realization is deliberately not formalized.**  The
paper's route to residual finiteness is the faithful embedding of `V` into
`GL₄(ℤ[1/2])` followed by reduction modulo odd primes.  That embedding is a
*device* for residual finiteness, not part of the claim, and formalizing it
would cost a separate injectivity argument — the stable-letter exponent has to
be recovered, for instance from the `2`-adic valuation of the determinant.
The proof below reaches residual finiteness directly, by congruence quotients
over the integers, so the census should record a **route difference** on that
sentence and not a gap.

## The congruence route

`MarkedCompressionGroup.verticalLift` is the universal property of the
ascending HNN extension: a homomorphism `g : Γ̄ →* H` together with an element
`c : H` conjugating like `α` extends to `V →* H`.  Its own docstring says it
exists to turn congruence quotients of `Γ̄` compatible with `α` into finite
quotients of `V`, and that is exactly what happens here.

Everything stays over `ℤ`; `ℤ[1/2]` never appears.  `Γ̄` consists of integral
units with integral inverses (`gammaBar_isIntegralUnit`), so entrywise
reduction modulo `m` lands in the finite group `GL₄(ZMod m)`.  The conjugating
element is `diag(2,2,2,1)`, whose inverse over `ZMod m` is written down
directly from the inverse of `2` rather than obtained by reducing the
non-integral `D⁻¹`.  Compatibility comes from the identity `D x = y D` between
*integral* matrices, which reduces.

Separation splits by the stable-letter exponent: a nonzero exponent is caught
by the height homomorphism to `ℤ`, and a nontrivial telescope element is
`level n x` with `x ≠ 1`, whose reduction survives modulo any odd prime not
dividing one nonzero integer entry of `x - 1`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace MaxInfiniteConverse

open ExplicitLinearModel MarkedCompression MappingTelescope

noncomputable section

/-- **The printed group `V`**: the ascending HNN extension of `Γ̄` along the
doubling self-embedding. -/
abbrev V : Type := Vertical conjD conjD_injective

instance : Countable V := inferInstance

/-! ## Reduction of integral units modulo `m` -/

section Reduction

variable (m : ℕ)

/-- The image of `ℤ` in `ℚ`, as a subring. -/
def Zsub : Subring ℚ := (Int.castRingHom ℚ).range

theorem intCast_mem_Zsub (a : ℤ) : ((a : ℚ)) ∈ Zsub := ⟨a, rfl⟩

/-- `ℤ` is its own image in `ℚ`. -/
def zsubEquiv : ℤ ≃+* Zsub :=
  RingEquiv.ofBijective (Int.castRingHom ℚ).rangeRestrict
    ⟨fun a b h ↦ by
      have h' : ((a : ℚ)) = ((b : ℚ)) := congrArg Subtype.val h
      exact_mod_cast h',
     (Int.castRingHom ℚ).rangeRestrict_surjective⟩

/-- Reduction `ℤ → ZMod m`, transported to the subring of integer rationals. -/
def redRing : Zsub →+* ZMod m :=
  (Int.castRingHom (ZMod m)).comp (zsubEquiv.symm : Zsub →+* ℤ)

theorem redRing_intCast (a : ℤ) (h : ((a : ℚ)) ∈ Zsub) :
    redRing m ⟨(a : ℚ), h⟩ = (a : ZMod m) := by
  have hz : zsubEquiv a = ⟨(a : ℚ), h⟩ := Subtype.ext rfl
  rw [redRing, RingHom.comp_apply, ← hz]
  simp

theorem redRing_val (a : ℤ) (q : ℚ) (h : q ∈ Zsub) (hq : q = (a : ℚ)) :
    redRing m ⟨q, h⟩ = (a : ZMod m) := by
  subst hq
  exact redRing_intCast m a h

/-- The `Zsub`-valued matrix underlying an integral rational matrix. -/
def toZsub (M : Mat) (h : IsIntegral M) : Matrix (Fin 4) (Fin 4) Zsub :=
  fun i j ↦ ⟨M i j, h i j⟩

theorem toZsub_val (M : Mat) (h : IsIntegral M) (i j : Fin 4) :
    ((toZsub M h i j : Zsub) : ℚ) = M i j := rfl

theorem toZsub_one : toZsub 1 isIntegral_one = 1 := by
  ext i j
  show (1 : Mat) i j = (((1 : Matrix (Fin 4) (Fin 4) Zsub) i j : Zsub) : ℚ)
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem toZsub_mul (M N : Mat) (hM : IsIntegral M) (hN : IsIntegral N)
    (hMN : IsIntegral (M * N)) :
    toZsub (M * N) hMN = toZsub M hM * toZsub N hN := by
  ext i j
  show (M * N) i j = (((toZsub M hM * toZsub N hN) i j : Zsub) : ℚ)
  rw [Matrix.mul_apply, Matrix.mul_apply]
  push_cast
  rfl

/-- Entrywise reduction of an integral matrix. -/
def redMat (M : Mat) (h : IsIntegral M) : Matrix (Fin 4) (Fin 4) (ZMod m) :=
  (redRing m).mapMatrix (toZsub M h)

theorem redMat_congr {M N : Mat} (hM : IsIntegral M) (hN : IsIntegral N)
    (h : M = N) : redMat m M hM = redMat m N hN := by
  subst h; rfl

theorem redMat_one : redMat m 1 isIntegral_one = 1 := by
  rw [redMat, toZsub_one, map_one]

theorem redMat_mul (M N : Mat) (hM : IsIntegral M) (hN : IsIntegral N)
    (hMN : IsIntegral (M * N)) :
    redMat m (M * N) hMN = redMat m M hM * redMat m N hN := by
  rw [redMat, redMat, redMat, toZsub_mul M N hM hN hMN, map_mul]

theorem redMat_apply (M : Mat) (h : IsIntegral M) (i j : Fin 4) (a : ℤ)
    (ha : ((a : ℚ)) = M i j) : redMat m M h i j = (a : ZMod m) := by
  rw [redMat, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact redRing_val m a (M i j) (h i j) ha.symm

/-- An integral unit reduces to a unit of the finite matrix ring. -/
def redUnit (u : Matˣ) (h : IsIntegralUnit u) :
    (Matrix (Fin 4) (Fin 4) (ZMod m))ˣ where
  val := redMat m (u : Mat) h.1
  inv := redMat m ((u⁻¹ : Matˣ) : Mat) h.2
  val_inv := by
    have hprod : ((u : Mat)) * ((u⁻¹ : Matˣ) : Mat) = 1 := u.mul_inv
    have hI : IsIntegral (((u : Mat)) * ((u⁻¹ : Matˣ) : Mat)) := by
      rw [hprod]; exact isIntegral_one
    rw [← redMat_mul m _ _ h.1 h.2 hI,
      redMat_congr m hI isIntegral_one hprod, redMat_one]
  inv_val := by
    have hprod : (((u⁻¹ : Matˣ) : Mat)) * ((u : Mat)) = 1 := u.inv_mul
    have hI : IsIntegral ((((u⁻¹ : Matˣ) : Mat)) * ((u : Mat))) := by
      rw [hprod]; exact isIntegral_one
    rw [← redMat_mul m _ _ h.2 h.1 hI,
      redMat_congr m hI isIntegral_one hprod, redMat_one]

theorem redUnit_val (u : Matˣ) (h : IsIntegralUnit u) :
    ((redUnit m u h : (Matrix (Fin 4) (Fin 4) (ZMod m))ˣ) :
      Matrix (Fin 4) (Fin 4) (ZMod m)) = redMat m (u : Mat) h.1 := rfl

/-- Reduction as a group homomorphism on the affine base. -/
def redHom : gammaBar →* (Matrix (Fin 4) (Fin 4) (ZMod m))ˣ where
  toFun g := redUnit m (g : Matˣ) (gammaBar_isIntegralUnit g.2)
  map_one' := by
    apply Units.ext
    rw [redUnit_val]
    exact redMat_one m
  map_mul' g h := by
    apply Units.ext
    rw [redUnit_val, Units.val_mul, redUnit_val, redUnit_val]
    exact redMat_mul m _ _ _ _ _

theorem redHom_val (g : gammaBar) :
    ((redHom m g : (Matrix (Fin 4) (Fin 4) (ZMod m))ˣ) :
      Matrix (Fin 4) (Fin 4) (ZMod m)) =
      redMat m ((g : Matˣ) : Mat) (gammaBar_isIntegralUnit g.2).1 := rfl

end Reduction

/-! ## The hypothesis of `prop:max-infinite` -/

/-- The printed subgroup `Γ`: the level-zero copy of `Γ̄` in `V`. -/
def baseCopy : Subgroup V := (iotaVertical conjD conjD_injective).range

/-- The printed compressing element `t`: the stable letter. -/
def stable : V := tVertical conjD conjD_injective

/-- **Property `(T)` for the printed subgroup.**  `Γ̄` is isomorphic to the
literal twenty-relator affine base, whose property `(T)` is unconditional
(`LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT`), and the level-zero
copy is isomorphic to `Γ̄`. -/
theorem baseCopy_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} ↥baseCopy := by
  have hgamma : HasKazhdanPropertyT.{0, 0} gammaBar :=
    HasKazhdanPropertyT.of_mulEquiv LiteralBaseCompleteness.baseAffineEquiv.symm
      LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT
  exact HasKazhdanPropertyT.of_mulEquiv
    (MonoidHom.ofInjective (iotaVertical_injective conjD conjD_injective)).symm
    hgamma

/-- **The compression is strict.**  Conjugating the level-zero copy by the
stable letter is the image of `α`, and `v1G` is outside that image. -/
theorem baseCopy_conj_lt :
    baseCopy.map (MulAut.conj stable).toMonoidHom < baseCopy := by
  have hle : baseCopy.map (MulAut.conj stable).toMonoidHom ≤ baseCopy := by
    rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩
    exact ⟨conjD γ, by
      rw [← vertical_compress conjD conjD_injective γ]
      rfl⟩
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hmem : iotaVertical conjD conjD_injective v1G ∈
      baseCopy.map (MulAut.conj stable).toMonoidHom := by
    rw [heq]; exact ⟨v1G, rfl⟩
  obtain ⟨_, ⟨γ, rfl⟩, hconj⟩ := hmem
  have hval : iotaVertical conjD conjD_injective (conjD γ) =
      iotaVertical conjD conjD_injective v1G := by
    rw [← vertical_compress conjD conjD_injective γ]
    exact hconj
  exact v1G_not_mem_range
    ⟨γ, iotaVertical_injective conjD conjD_injective hval⟩

/-! ## Residual finiteness -/

/-! ## The doubling matrix reduces to the explicit diagonal -/

theorem dM_eq_diagonal :
    dM = Matrix.diagonal fun i : Fin 4 ↦ if i = 3 then (1 : ℚ) else 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dM, Matrix.diagonal]

theorem dM_isIntegral : IsIntegral dM := by
  rw [dM_eq_diagonal]
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    by_cases hi : i = 3
    · exact ⟨1, by simp [hi]⟩
    · exact ⟨2, by simp [hi]⟩
  · rw [Matrix.diagonal_apply_ne _ hij]
    exact ⟨0, by simp⟩

theorem redMat_dM (m : ℕ) :
    redMat m dM dM_isIntegral =
      Matrix.diagonal fun i ↦ if i = 3 then 1 else (2 : ZMod m) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    by_cases hi : i = 3
    · rw [redMat_apply m dM dM_isIntegral i i 1 (by rw [dM_eq_diagonal]; simp [hi])]
      simp [hi]
    · rw [redMat_apply m dM dM_isIntegral i i 2 (by rw [dM_eq_diagonal]; simp [hi])]
      simp [hi]
  · rw [Matrix.diagonal_apply_ne _ hij,
      redMat_apply m dM dM_isIntegral i j 0 (by rw [dM_eq_diagonal]; simp [hij])]
    simp

/-- The conjugating element in the finite quotient: the reduction of `D`,
made a unit from the invertibility of `2` modulo an odd `m`. -/
def dRed (m : ℕ) (hm : Nat.Coprime 2 m) :
    (Matrix (Fin 4) (Fin 4) (ZMod m))ˣ where
  val := redMat m dM dM_isIntegral
  inv := Matrix.diagonal fun i ↦
    if i = 3 then 1 else ((ZMod.unitOfCoprime 2 hm)⁻¹ : (ZMod m)ˣ)
  val_inv := by
    rw [redMat_dM, Matrix.diagonal_mul_diagonal]
    refine Matrix.diagonal_eq_diagonal_iff.mpr fun i ↦ ?_
    by_cases hi : i = 3
    · simp [hi]
    · simp only [hi, if_false]
      have h2 : ((ZMod.unitOfCoprime 2 hm : (ZMod m)ˣ) : ZMod m) = 2 := rfl
      rw [← h2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  inv_val := by
    rw [redMat_dM, Matrix.diagonal_mul_diagonal]
    refine Matrix.diagonal_eq_diagonal_iff.mpr fun i ↦ ?_
    by_cases hi : i = 3
    · simp [hi]
    · simp only [hi, if_false]
      have h2 : ((ZMod.unitOfCoprime 2 hm : (ZMod m)ˣ) : ZMod m) = 2 := rfl
      rw [← h2, ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem dRed_val (m : ℕ) (hm : Nat.Coprime 2 m) :
    ((dRed m hm : (Matrix (Fin 4) (Fin 4) (ZMod m))ˣ) :
      Matrix (Fin 4) (Fin 4) (ZMod m)) = redMat m dM dM_isIntegral := rfl

/-- **The compatibility `verticalLift` asks for.**  It comes from the identity
`D x = (α x) D` between *integral* matrices, reduced. -/
theorem redHom_conjD (m : ℕ) (hm : Nat.Coprime 2 m) (x : gammaBar) :
    redHom m (conjD x) = dRed m hm * redHom m x * (dRed m hm)⁻¹ := by
  have hxint := gammaBar_isIntegralUnit x.2
  have hcint := gammaBar_isIntegralUnit (conjD x).2
  have hmatrix : ((conjD x : gammaBar) : Matˣ) * dU = dU * (x : Matˣ) := by
    have : ((conjD x : gammaBar) : Matˣ) = dU * (x : Matˣ) * dU⁻¹ := rfl
    rw [this]
    group
  have hval : (((conjD x : gammaBar) : Matˣ) : Mat) * dM =
      dM * ((x : Matˣ) : Mat) := congrArg Units.val hmatrix
  have hI1 : IsIntegral ((((conjD x : gammaBar) : Matˣ) : Mat) * dM) :=
    by rw [hval]; exact isIntegral_mul dM_isIntegral hxint.1
  have hstep : redMat m _ hcint.1 * redMat m dM dM_isIntegral =
      redMat m dM dM_isIntegral * redMat m _ hxint.1 := by
    rw [← redMat_mul m _ _ hcint.1 dM_isIntegral hI1,
      redMat_congr m hI1 (isIntegral_mul dM_isIntegral hxint.1) hval,
      redMat_mul m _ _ dM_isIntegral hxint.1]
  refine (eq_mul_inv_iff_mul_eq).mpr ?_
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, redHom_val, redHom_val, dRed_val]
  exact hstep

/-! ## The finite quotients of `V` -/

/-- The congruence quotient of `V` at an odd modulus. -/
def congruence (m : ℕ) (hm : Nat.Coprime 2 m) :
    V →* (Matrix (Fin 4) (Fin 4) (ZMod m))ˣ :=
  verticalLift conjD conjD_injective (redHom m) (dRed m hm) (redHom_conjD m hm)

/-! ## Separation -/

/-- Reduction separates a nontrivial element of the affine base at some odd
modulus: two distinct integer entries stay distinct modulo any prime larger
than their difference. -/
theorem exists_redHom_ne_one (x : gammaBar) (hx : x ≠ 1) :
    ∃ m : ℕ, Nat.Coprime 2 m ∧ redHom m x ≠ 1 := by
  have hxint := gammaBar_isIntegralUnit x.2
  have hmat : ((x : Matˣ) : Mat) ≠ ((1 : Matˣ) : Mat) := by
    intro h
    exact hx (Subtype.ext (Units.ext h))
  obtain ⟨i, j, hij⟩ : ∃ i j, ((x : Matˣ) : Mat) i j ≠ (1 : Mat) i j := by
    by_contra hcon
    push Not at hcon
    exact hmat (by ext i j; exact hcon i j)
  obtain ⟨a, ha⟩ := hxint.1 i j
  obtain ⟨b, hb⟩ := ExplicitLinearModel.isIntegral_one i j
  have hab : a ≠ b := by
    intro h
    exact hij (by rw [← ha, ← hb, h])
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max 3 ((a - b).natAbs + 1))
  have hp3 : 3 ≤ p := le_trans (le_max_left _ _) hple
  have hcop : Nat.Coprime 2 p := by
    have hne : (2 : ℕ) ≠ p := by omega
    exact (Nat.coprime_primes Nat.prime_two hp).mpr hne
  refine ⟨p, hcop, ?_⟩
  intro hone
  have h1 : redMat p ((x : Matˣ) : Mat) hxint.1 = 1 := by
    have := congrArg (fun u : (Matrix (Fin 4) (Fin 4) (ZMod p))ˣ ↦
      (u : Matrix (Fin 4) (Fin 4) (ZMod p))) hone
    rwa [redHom_val, Units.val_one] at this
  have hentry : (a : ZMod p) = (b : ZMod p) := by
    rw [← redMat_apply p _ hxint.1 i j a ha,
      ← redMat_apply p (1 : Mat) ExplicitLinearModel.isIntegral_one i j b hb,
      h1, redMat_one]
  have hdvd : ((p : ℤ)) ∣ b - a :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a b p).mp hentry
  have hne0 : b - a ≠ 0 := sub_ne_zero_of_ne (Ne.symm hab)
  have hle : (p : ℤ) ≤ |b - a| := Int.le_of_dvd (abs_pos.mpr hne0)
    ((dvd_abs _ _).mpr hdvd)
  have hlt : ((a - b).natAbs : ℤ) < (p : ℤ) := by
    have hh : (a - b).natAbs + 1 ≤ p := le_trans (le_max_right _ _) hple
    exact_mod_cast Nat.lt_of_succ_le hh
  have habs : |b - a| = ((a - b).natAbs : ℤ) := by
    rw [Int.abs_eq_natAbs, ← Int.natAbs_neg, neg_sub]
  omega

/-! ## Residual finiteness, and MF -/

/-- **`V` is residually finite.**  The stable-letter exponent is caught by the
height homomorphism to `ℤ`; a nontrivial telescope element is `level n x` with
`x ≠ 1`, and its congruence quotient survives at a suitable odd modulus. -/
theorem residuallyFinite : Group.ResiduallyFinite V := by
  refine Group.residuallyFinite_of_forall_exists_finite_monoidHom.{0} ?_
  intro v hv
  by_cases hheight : (SemidirectProduct.rightHom v : Multiplicative ℤ) = 1
  · -- the telescope part is nontrivial
    have hleft : v = SemidirectProduct.inl v.left := by
      have := SemidirectProduct.inl_left_mul_inr_right v
      rw [show v.right = 1 from hheight] at this
      simpa using this.symm
    obtain ⟨⟨n, x⟩, hnx⟩ := MappingTelescope.mk_surjective conjD conjD_injective v.left
    dsimp only at hnx
    have hx : x ≠ 1 := by
      intro hx1
      apply hv
      rw [hleft, ← hnx, hx1, ← MappingTelescope.one_eq_mk, map_one]
    obtain ⟨m, hcop, hne⟩ := exists_redHom_ne_one x hx
    refine ⟨(Matrix (Fin 4) (Fin 4) (ZMod m))ˣ, inferInstance, ?_,
      congruence m hcop, ?_⟩
    · haveI : NeZero m := ⟨by
        rintro rfl
        simp [Nat.Coprime] at hcop⟩
      infer_instance
    · rw [hleft, ← hnx]
      have hlevel : (MappingTelescope.mk conjD conjD_injective n x) =
          MappingTelescope.level conjD conjD_injective n x := rfl
      rw [hlevel, congruence,
        verticalLift_inl_level conjD conjD_injective (redHom m) (dRed m hcop)
          (redHom_conjD m hcop) n x]
      intro hcon
      refine hne ?_
      have h2 : redHom m x =
          ((dRed m hcop) ^ n) *
            (((dRed m hcop) ^ n)⁻¹ * redHom m x * ((dRed m hcop) ^ n)) *
            ((dRed m hcop) ^ n)⁻¹ := by group
      rw [hcon] at h2
      simpa using h2
  · -- the stable-letter exponent is nonzero
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 0 < N ∧
        ((Multiplicative.toAdd (SemidirectProduct.rightHom v) : ℤ) : ZMod N) ≠ 0 := by
      refine ⟨(Multiplicative.toAdd
        (SemidirectProduct.rightHom v)).natAbs + 1, by omega, ?_⟩
      intro hcon
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcon
      have hz : Multiplicative.toAdd (SemidirectProduct.rightHom v) ≠ 0 := by
        intro h0
        exact hheight (by
          have : SemidirectProduct.rightHom v = Multiplicative.ofAdd (0 : ℤ) := by
            rw [← h0]; rfl
          simpa using this)
      have := Int.le_of_dvd (abs_pos.mpr hz) ((dvd_abs _ _).mpr hcon)
      rw [Int.abs_eq_natAbs] at this
      omega
    obtain ⟨hNpos, hNne⟩ := hN
    haveI : NeZero N := ⟨by omega⟩
    refine ⟨Multiplicative (ZMod N), inferInstance, inferInstance,
      (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod N))).comp
        SemidirectProduct.rightHom, ?_⟩
    intro hcon
    exact hNne (by simpa using congrArg Multiplicative.toAdd hcon)

/-- **`V` is MF.**  Residual finiteness plus countability, through the
manuscript's `lem:rfmf`. -/
theorem isOperatorMF : IsOperatorMF V := by
  haveI := residuallyFinite
  exact isOperatorMF_of_residuallyFinite

/-! ## The printed remark -/

/-- **The concrete content at `V`.** -/
def PrintedAscendingHNNIsMF : Prop :=
  Countable V ∧
    HasKazhdanPropertyT.{0, 0} ↥baseCopy ∧
    baseCopy.map (MulAut.conj stable).toMonoidHom < baseCopy ∧
    Group.ResiduallyFinite V ∧
    IsOperatorMF V

theorem manuscriptAscendingHNNIsMF : PrintedAscendingHNNIsMF :=
  ⟨inferInstance, baseCopy_hasKazhdanPropertyT, baseCopy_conj_lt,
    residuallyFinite, isOperatorMF⟩

/-- **The printed remark: a group can satisfy the hypothesis of
`prop:max-infinite` and be MF.** -/
def PrintedMaxInfiniteConverseRemark : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Countable G),
    (∃ (Γ : Subgroup G) (t : G),
        HasKazhdanPropertyT.{0, 0} ↥Γ ∧
          Γ.map (MulAut.conj t).toMonoidHom < Γ) ∧
      IsOperatorMF G

theorem manuscriptMaxInfiniteConverseRemark : PrintedMaxInfiniteConverseRemark :=
  ⟨V, inferInstance, inferInstance,
    ⟨baseCopy, stable, baseCopy_hasKazhdanPropertyT, baseCopy_conj_lt⟩,
    isOperatorMF⟩

end

end MaxInfiniteConverse
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation
open GroupApproximation.Manuscript.OneSidedMFRadical

#audit_closed_axioms
  MaxInfiniteConverse.manuscriptMaxInfiniteConverseRemark
#audit_closed_axioms MaxInfiniteConverse.manuscriptAscendingHNNIsMF
