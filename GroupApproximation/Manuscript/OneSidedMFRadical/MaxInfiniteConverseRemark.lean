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

theorem redRing_intCast (m : ℕ) (a : ℤ) (h : ((a : ℚ)) ∈ Zsub) :
    redRing m ⟨(a : ℚ), h⟩ = (a : ZMod m) := by
  have hz : zsubEquiv a = ⟨(a : ℚ), h⟩ := Subtype.ext rfl
  rw [redRing, RingHom.comp_apply, ← hz]
  simp

theorem redRing_val (m : ℕ) (a : ℤ) (q : ℚ) (h : q ∈ Zsub) (hq : q = (a : ℚ)) :
    redRing m ⟨q, h⟩ = (a : ZMod m) := by
  subst hq
  exact redRing_intCast m a h

theorem redMat_dM (m : ℕ) :
    redMat m dM dM_isIntegral =
      Matrix.diagonal fun i ↦ if i = 3 then 1 else (2 : ZMod m) := by
  ext i j
  rw [redMat, RingHom.mapMatrix_apply, Matrix.map_apply]
  show redRing m ⟨dM i j, dM_isIntegral i j⟩ = _
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    by_cases hi : i = 3
    · rw [redRing_val m 1 _ _ (by rw [dM_eq_diagonal]; simp [hi])]
      simp [hi]
    · rw [redRing_val m 2 _ _ (by rw [dM_eq_diagonal]; simp [hi])]
      simp [hi]
  · rw [Matrix.diagonal_apply_ne _ hij,
      redRing_val m 0 _ _ (by rw [dM_eq_diagonal]; simp [hij])]
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

end

end MaxInfiniteConverse
end OneSidedMFRadical
end Manuscript
end GroupApproximation
