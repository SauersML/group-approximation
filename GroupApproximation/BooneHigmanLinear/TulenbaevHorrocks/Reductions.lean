import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Field
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Localization.Away.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Horrocks for `St_N`: the reductions of Tulenbaev Thm 5.1(a) and Cor 5.2(a) (lane pal-q111)

M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, Math. USSR Sb. 45 (1983), §5, read at
source.  This file proves, for every commutative ring `A`:

* `stHorrocksAt_of_localGlobal` (T 5.1(a), p. 152).  The Horrocks property of `St_N` over `A`
  (`StHorrocksAt`) follows from the local–global principle (`Tulenbaev.StLocalGlobalStatementAt`,
  T Thm 2.1, sk-k2-loc) and the Horrocks property over the local rings `A_𝔪`
  (`StLocalHorrocksStatementAt`, T Prop 4.3(a)).  A common image of `α ∈ St_N(A[X])` and
  `β ∈ St_N(A[X⁻¹])` is locally constant on both sides, hence constant on both sides.
* `stMonicInjAt_of_horrocks_of_excision` (T 5.2(a), p. 152–153).  Monic injectivity
  (`StMonicInjAt`) over `A` follows from `StHorrocksAt A N` and Zariski excision for `St_N` over
  `A[Y]` (`StExcisionAt`, verbatim `PaninAffine.StZariskiExcisionAt`, board piece F.4).
  - Here `Y = X⁻¹`, `g = reverse f` (so `f = Xⁿ g(X⁻¹)` and `g(0) = 1`), and the comaximal
    non-zero-divisors are `g` and `Y`.
  - Excision moves `α`, which dies where `f` is inverted, to some `γ ∈ St_N(A[Y])` with the same
    image in `St_N(A[X,X⁻¹])` that dies in `St_N(A[Y]_g)`.
  - Horrocks makes `α = γ` constant; `A → A[Y]_g` is split by `Y ↦ 0`, so the constant is `1`.
  - Tulenbaev's route through Prop 1.4(b) and Prop 1.6 is not needed.
* `stMonicInjStatement_of`: H.b for every commutative ring (`horrocksMonicAt_of_stMonicInjAt` in
  `FieldCorollaries` converts it to the board's `HorrocksMonicAt`).

What remains of piece H is `StLocalHorrocksStatementAt 5`, i.e. T Prop 4.3(a) over local rings
(T §§3–4), with the field case at the residue field supplied by `stHorrocksAt_of_const`
(`stHorrocksAt_of_fieldNK` in `FieldCorollaries`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic Polynomial
open GroupApproximation.BooneHigmanLinear.Tulenbaev

/-- **Zariski excision for `St_N` at one ring** (verbatim `PaninAffine.StZariskiExcisionAt`, board
piece F.4, owner bh-pal-linear-char0), restated so that this file does not import `PaninAffine`. -/
def StExcisionAt (A : Type) [CommRing A] (N : ℕ) : Prop :=
  ∀ a b : A, a ∈ nonZeroDivisors A → b ∈ nonZeroDivisors A → IsCoprime a b →
    ∀ β : SteinbergGroup (Fin N) (Localization.Away b),
      ringMap (IsLocalization.Away.awayToAwayLeft b a :
          Localization.Away b →+* Localization.Away (a * b)) β = 1 →
        ∃ γ : SteinbergGroup (Fin N) A,
          ringMap (algebraMap A (Localization.Away a)) γ = 1 ∧
            ringMap (algebraMap A (Localization.Away b)) γ = β

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StExcisionAt

section Laurent

variable {A : Type} [CommRing A]

theorem toLaurentNeg_apply (p : A[X]) :
    toLaurentNeg A p = LaurentPolynomial.invert (Polynomial.toLaurent p) := by
  rw [toLaurentNeg_eq]
  rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.toLaurentNeg_apply

theorem T_one_mul_T_neg_one :
    (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1) : LaurentPolynomial A) = 1 := by
  rw [← LaurentPolynomial.T_add]
  simp [LaurentPolynomial.T_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.T_one_mul_T_neg_one

/-- `f(T) = T^{deg f} · (reverse f)(T⁻¹)`. -/
theorem toLaurentPos_eq_toLaurentNeg_reverse (f : A[X]) :
    toLaurentPos A f = toLaurentNeg A f.reverse * LaurentPolynomial.T (f.natDegree : ℤ) := by
  rw [toLaurentNeg_apply, LaurentPolynomial.toLaurent_reverse, map_mul, LaurentPolynomial.invert_T,
    LaurentPolynomial.involutive_invert (Polynomial.toLaurent f), mul_assoc,
    ← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero, mul_one, toLaurentPos_eq]

#audit_axioms
  GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.toLaurentPos_eq_toLaurentNeg_reverse

/-- `X` as a unit of `A[X]_X`. -/
noncomputable def unitX (A : Type) [CommRing A] : (Localization.Away (X : A[X]))ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (X : A[X])) (X : A[X])).unit

theorem unitX_val : ((unitX A : (Localization.Away (X : A[X]))ˣ) : Localization.Away (X : A[X])) =
    algebraMap A[X] (Localization.Away (X : A[X])) X :=
  IsUnit.unit_spec _

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.unitX_val

/-- `A[X] → A[X]_X`, `a ↦ a`, `X ↦ X⁻¹`. -/
noncomputable def negHom (A : Type) [CommRing A] : A[X] →+* Localization.Away (X : A[X]) :=
  Polynomial.eval₂RingHom ((algebraMap A[X] (Localization.Away (X : A[X]))).comp Polynomial.C)
    (((unitX A)⁻¹ : (Localization.Away (X : A[X]))ˣ) : Localization.Away (X : A[X]))

theorem negHom_C (a : A) : negHom A (Polynomial.C a) =
    algebraMap A[X] (Localization.Away (X : A[X])) (Polynomial.C a) := by
  rw [negHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply]

theorem negHom_X : negHom A X = (((unitX A)⁻¹ : (Localization.Away (X : A[X]))ˣ) :
    Localization.Away (X : A[X])) := by
  rw [negHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

/-- `A[T,T⁻¹] → A[Y]_Y`, `T ↦ Y⁻¹`: the inverse of `Y ↦ T⁻¹`. -/
noncomputable def laurentToAway (A : Type) [CommRing A] :
    LaurentPolynomial A →+* Localization.Away (X : A[X]) :=
  IsLocalization.Away.lift (S := LaurentPolynomial A) (X : A[X]) (g := negHom A)
    (by rw [negHom_X]; exact Units.isUnit _)

theorem laurentToAway_toLaurent (p : A[X]) :
    laurentToAway A (Polynomial.toLaurent p) = negHom A p := by
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent, laurentToAway, IsLocalization.Away.lift_eq]

/-- `A[Y]_Y → A[T,T⁻¹]`, `Y ↦ T⁻¹`. -/
noncomputable def awayToLaurent (A : Type) [CommRing A] :
    Localization.Away (X : A[X]) →+* LaurentPolynomial A :=
  IsLocalization.Away.lift (S := Localization.Away (X : A[X])) (X : A[X]) (g := toLaurentNeg A)
    (by simp only [toLaurentNeg, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X];
        exact LaurentPolynomial.isUnit_T _)

theorem awayToLaurent_comp_algebraMap :
    (awayToLaurent A).comp (algebraMap A[X] (Localization.Away (X : A[X]))) = toLaurentNeg A :=
  IsLocalization.Away.lift_comp _ _

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.awayToLaurent_comp_algebraMap

theorem toLaurentNeg_X : toLaurentNeg A X = LaurentPolynomial.T (-1) := by
  simp only [toLaurentNeg, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

/-- `Y ↦ T⁻¹ ↦ Y` is the localization map. -/
theorem laurentToAway_comp_toLaurentNeg :
    (laurentToAway A).comp (toLaurentNeg A) = algebraMap A[X] (Localization.Away (X : A[X])) := by
  apply Polynomial.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, toLaurentNeg_apply, Polynomial.toLaurent_C, LaurentPolynomial.invert_C,
      ← Polynomial.toLaurent_C, laurentToAway_toLaurent, negHom_C]
  · rw [RingHom.comp_apply, toLaurentNeg_X]
    have h1 : laurentToAway A (LaurentPolynomial.T 1) =
        (((unitX A)⁻¹ : (Localization.Away (X : A[X]))ˣ) : Localization.Away (X : A[X])) := by
      rw [← Polynomial.toLaurent_X, laurentToAway_toLaurent, negHom_X]
    have h2 := congrArg (laurentToAway A) (T_one_mul_T_neg_one (A := A))
    rw [map_mul, map_one, h1] at h2
    calc laurentToAway A (LaurentPolynomial.T (-1))
        = ((unitX A : (Localization.Away (X : A[X]))ˣ) : Localization.Away (X : A[X])) *
            ((((unitX A)⁻¹ : (Localization.Away (X : A[X]))ˣ) : Localization.Away (X : A[X])) *
              laurentToAway A (LaurentPolynomial.T (-1))) := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
      _ = algebraMap A[X] (Localization.Away (X : A[X])) X := by rw [h2, mul_one, unitX_val]

#audit_axioms
  GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.laurentToAway_comp_toLaurentNeg

/-- `T ↦ Y⁻¹ ↦ T` is the identity of `A[T,T⁻¹]`. -/
theorem awayToLaurent_comp_laurentToAway :
    (awayToLaurent A).comp (laurentToAway A) = RingHom.id (LaurentPolynomial A) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (X : A[X]))
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent, RingHom.id_apply,
      laurentToAway_toLaurent, negHom_C]
    rw [← RingHom.comp_apply (awayToLaurent A), awayToLaurent_comp_algebraMap, toLaurentNeg_apply,
      Polynomial.toLaurent_C, LaurentPolynomial.invert_C]
  · simp only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent, RingHom.id_apply,
      laurentToAway_toLaurent, negHom_X]
    rw [Polynomial.toLaurent_X]
    have hu : awayToLaurent A ((unitX A : (Localization.Away (X : A[X]))ˣ) :
        Localization.Away (X : A[X])) = LaurentPolynomial.T (-1) := by
      rw [unitX_val, ← RingHom.comp_apply (awayToLaurent A), awayToLaurent_comp_algebraMap,
        toLaurentNeg_X]
    calc awayToLaurent A ((((unitX A)⁻¹ : (Localization.Away (X : A[X]))ˣ) :
          Localization.Away (X : A[X])))
        = awayToLaurent A ((((unitX A)⁻¹ : (Localization.Away (X : A[X]))ˣ) :
            Localization.Away (X : A[X]))) *
              (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1) := by
          rw [mul_comm (LaurentPolynomial.T (-1)), T_one_mul_T_neg_one, mul_one]
      _ = awayToLaurent A ((((unitX A)⁻¹ : (Localization.Away (X : A[X]))ˣ) :
            Localization.Away (X : A[X])) * (unitX A : (Localization.Away (X : A[X]))ˣ)) *
              LaurentPolynomial.T 1 := by
          rw [map_mul, hu, mul_assoc]
      _ = LaurentPolynomial.T 1 := by rw [Units.inv_mul, map_one, one_mul]

#audit_axioms
  GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.awayToLaurent_comp_laurentToAway

/-- The coefficient map `A[T,T⁻¹] → A'[T,T⁻¹]`. -/
noncomputable def laurentMap {A' : Type} [CommRing A'] (e : A →+* A') :
    LaurentPolynomial A →+* LaurentPolynomial A' :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp e) (LaurentPolynomial.isUnit_T 1).unit

theorem unitT_inv_val {A' : Type} [CommRing A'] :
    ((((LaurentPolynomial.isUnit_T 1).unit : (LaurentPolynomial A')ˣ)⁻¹ :
      (LaurentPolynomial A')ˣ) : LaurentPolynomial A') = LaurentPolynomial.T (-1) :=
  Units.inv_eq_of_mul_eq_one_right (by rw [IsUnit.unit_spec]; exact T_one_mul_T_neg_one)

theorem laurentMap_comp_toLaurentPos {A' : Type} [CommRing A'] (e : A →+* A') :
    (laurentMap e).comp (toLaurentPos A) = (toLaurentPos A').comp (Polynomial.mapRingHom e) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [laurentMap, toLaurentPos, LaurentPolynomial.eval₂_C]
  · simp only [laurentMap, toLaurentPos, RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, Polynomial.coe_mapRingHom, Polynomial.map_X, LaurentPolynomial.eval₂_T,
      zpow_one, IsUnit.unit_spec]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.laurentMap_comp_toLaurentPos

theorem laurentMap_comp_toLaurentNeg {A' : Type} [CommRing A'] (e : A →+* A') :
    (laurentMap e).comp (toLaurentNeg A) = (toLaurentNeg A').comp (Polynomial.mapRingHom e) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [laurentMap, toLaurentNeg, LaurentPolynomial.eval₂_C]
  · simp only [laurentMap, toLaurentNeg, RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, Polynomial.coe_mapRingHom, Polynomial.map_X, LaurentPolynomial.eval₂_T,
      zpow_neg, zpow_one]
    exact unitT_inv_val

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.laurentMap_comp_toLaurentNeg

theorem evalRingHom_zero_comp_mapRingHom {A' : Type} [CommRing A'] (e : A →+* A') :
    (Polynomial.evalRingHom (0 : A')).comp (Polynomial.mapRingHom e) =
      e.comp (Polynomial.evalRingHom (0 : A)) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp

theorem evalRingHom_zero_comp_C' :
    (Polynomial.evalRingHom (0 : A)).comp Polynomial.C = RingHom.id A := by
  ext a
  simp

end Laurent

/-! ### T 5.1(a) from the local–global principle and the local case -/

/-- **T Thm 5.1(a) from T Thm 2.1 and T Prop 4.3(a).** -/
theorem stHorrocksAt_of_localGlobal {n₀ : ℕ} (hLG : StLocalGlobalStatementAt n₀)
    (hLoc : StLocalHorrocksStatementAt n₀) (A : Type) [CommRing A] (N : ℕ) (hN : n₀ ≤ N) :
    StHorrocksAt A N := by
  have hconst : ∀ α β : SteinbergGroup (Fin N) A[X],
      ringMap (toLaurentPos A) α = ringMap (toLaurentNeg A) β →
        α = ringMap (Polynomial.C : A →+* A[X]) (ringMap (Polynomial.evalRingHom (0 : A)) α) ∧
          β = ringMap (Polynomial.C : A →+* A[X]) (ringMap (Polynomial.evalRingHom (0 : A)) β) := by
    intro α β h
    have hloc : ∀ (M : Ideal A) [M.IsMaximal],
        ∃ γ : SteinbergGroup (Fin N) (Localization.AtPrime M),
          ringMap (Polynomial.C : Localization.AtPrime M →+* (Localization.AtPrime M)[X]) γ =
              ringMap (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime M))) α ∧
            ringMap (Polynomial.C : Localization.AtPrime M →+* (Localization.AtPrime M)[X]) γ =
              ringMap (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime M))) β := by
      intro M _
      refine (hLoc (Localization.AtPrime M) N hN).2.2 _ _ ?_
      rw [ringMap_ringMap, ringMap_ringMap, ← laurentMap_comp_toLaurentPos,
        ← laurentMap_comp_toLaurentNeg, ← ringMap_ringMap, ← ringMap_ringMap, h]
    have hev : ∀ (M : Ideal A) [M.IsMaximal] (δ : SteinbergGroup (Fin N) A[X])
        (γ : SteinbergGroup (Fin N) (Localization.AtPrime M)),
        ringMap (Polynomial.C : Localization.AtPrime M →+* (Localization.AtPrime M)[X]) γ =
            ringMap (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime M))) δ →
          ringMap (algebraMap A (Localization.AtPrime M))
              (ringMap (Polynomial.evalRingHom (0 : A)) δ) = γ := by
      intro M _ δ γ hγ
      rw [ringMap_ringMap, ← evalRingHom_zero_comp_mapRingHom, ← ringMap_ringMap, ← hγ,
        ringMap_ringMap, evalRingHom_zero_comp_C', ringMap_id, MonoidHom.id_apply]
    refine ⟨hLG A N hN α fun M _ => ?_, hLG A N hN β fun M _ => ?_⟩
    · obtain ⟨γ, hγ, -⟩ := hloc M
      rw [hev M α γ hγ, hγ]
    · obtain ⟨γ, -, hγ⟩ := hloc M
      rw [hev M β γ hγ, hγ]
  have key : ∀ α β : SteinbergGroup (Fin N) A[X],
      ringMap (toLaurentPos A) α = ringMap (toLaurentNeg A) β →
        ∃ γ : SteinbergGroup (Fin N) A,
          ringMap (Polynomial.C : A →+* A[X]) γ = α ∧
            ringMap (Polynomial.C : A →+* A[X]) γ = β := by
    intro α β h
    obtain ⟨hα, hβ⟩ := hconst α β h
    refine ⟨ringMap (Polynomial.evalRingHom (0 : A)) α, hα.symm, ?_⟩
    have h2 : ringMap (Polynomial.evalRingHom (0 : A)) α =
        ringMap (Polynomial.evalRingHom (0 : A)) β := by
      apply ringMap_laurentC_injective N
      have h' := h
      rw [hα, hβ, ringMap_ringMap, ringMap_ringMap, toLaurentPos_comp_C, toLaurentNeg_comp_C] at h'
      exact h'
    rw [h2]
    exact hβ.symm
  refine ⟨?_, ?_, key⟩
  · refine (injective_iff_map_eq_one _).mpr fun α hα => ?_
    obtain ⟨γ, hγα, hγ1⟩ := key α 1 (by rw [hα, map_one])
    rw [← hγα, hγ1]
  · refine (injective_iff_map_eq_one _).mpr fun β hβ => ?_
    obtain ⟨γ, hγ1, hγβ⟩ := key 1 β (by rw [hβ, map_one])
    rw [← hγβ, hγ1]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stHorrocksAt_of_localGlobal

/-- **H.a** from LG and T Prop 4.3(a). -/
theorem stHorrocksStatement_of {n₀ : ℕ} (hLG : StLocalGlobalStatementAt n₀)
    (hLoc : StLocalHorrocksStatementAt n₀) : StHorrocksStatementAt n₀ :=
  fun A _ N hN => stHorrocksAt_of_localGlobal hLG hLoc A N hN

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stHorrocksStatement_of

/-! ### T Cor 5.2(a) from Horrocks and Zariski excision -/

/-- `α ↦ (α(X) as an element of `St_N(A[Y]_Y)`) ↦ St_N(A[Y]_{gY})`, for `g = reverse f`. -/
noncomputable def rhoMap {A : Type} [CommRing A] (f : A[X]) :
    A[X] →+* Localization.Away (f.reverse * X) :=
  (IsLocalization.Away.awayToAwayLeft (S := Localization.Away (X : A[X])) (X : A[X]) f.reverse).comp
    ((laurentToAway A).comp (toLaurentPos A))

/-- **T Cor 5.2(a) from T Thm 5.1(a) and Zariski excision over `A[Y]`.** -/
theorem stMonicInjAt_of_horrocks_of_excision {A : Type} [CommRing A] {N : ℕ}
    (hH : StHorrocksAt A N) (hExc : StExcisionAt A[X] N) : StMonicInjAt A N := by
  intro f hf α hα
  have hg0 : f.reverse.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_reverse, hf.leadingCoeff]
  have hgnz : f.reverse ∈ nonZeroDivisors A[X] :=
    Polynomial.mem_nonzeroDivisors_of_coeff_mem 0 (by rw [hg0]; exact one_mem _)
  have hXnz : (X : A[X]) ∈ nonZeroDivisors A[X] := Polynomial.X_mem_nonzeroDivisors
  have hcop : IsCoprime f.reverse (X : A[X]) := by
    obtain ⟨q, hq⟩ : (X : A[X]) ∣ f.reverse - 1 := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, hg0, Polynomial.coeff_one_zero, sub_self]
    exact ⟨1, -q, by rw [one_mul, neg_mul, ← sub_eq_add_neg, mul_comm q, ← hq, sub_sub_cancel]⟩
  have hρf : IsUnit (rhoMap f f) := by
    have h2 : laurentToAway A (toLaurentNeg A f.reverse) =
        algebraMap A[X] (Localization.Away (X : A[X])) f.reverse := by
      rw [← RingHom.comp_apply, laurentToAway_comp_toLaurentNeg]
    simp only [rhoMap, RingHom.comp_apply]
    rw [toLaurentPos_eq_toLaurentNeg_reverse f, map_mul, map_mul, h2,
      IsLocalization.Away.awayToAwayLeft_eq]
    exact (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (f.reverse * X))
      (f.reverse * X) (dvd_mul_right f.reverse X)).mul
      ((LaurentPolynomial.isUnit_T _).map
        ((IsLocalization.Away.awayToAwayLeft (S := Localization.Away (X : A[X])) (X : A[X])
          f.reverse).comp (laurentToAway A)))
  have hβ : ringMap (IsLocalization.Away.awayToAwayLeft (X : A[X]) f.reverse :
      Localization.Away (X : A[X]) →+* Localization.Away (f.reverse * X))
        (ringMap ((laurentToAway A).comp (toLaurentPos A)) α) = 1 := by
    rw [ringMap_ringMap]
    change ringMap (rhoMap f) α = 1
    rw [← IsLocalization.Away.lift_comp (S := Localization.Away f) f hρf, ← ringMap_ringMap, hα,
      map_one]
  obtain ⟨γ, hγg, hγX⟩ := hExc f.reverse X hgnz hXnz hcop _ hβ
  have hLN : ringMap (toLaurentPos A) α = ringMap (toLaurentNeg A) γ := by
    have h := congrArg (ringMap (awayToLaurent A)) hγX
    rw [ringMap_ringMap, ringMap_ringMap, awayToLaurent_comp_algebraMap, ← RingHom.comp_assoc,
      awayToLaurent_comp_laurentToAway, RingHom.id_comp] at h
    exact h.symm
  obtain ⟨δ, hδα, hδγ⟩ := hH.2.2 α γ hLN
  have hev : IsUnit (Polynomial.evalRingHom (0 : A) f.reverse) := by
    rw [Polynomial.coe_evalRingHom, ← Polynomial.coeff_zero_eq_eval_zero, hg0]
    exact isUnit_one
  have hinj : Function.Injective (ringMap (I := Fin N)
      ((algebraMap A[X] (Localization.Away f.reverse)).comp (Polynomial.C : A →+* A[X]))) :=
    ringMap_injective_of_leftInverse _
      (IsLocalization.Away.lift (S := Localization.Away f.reverse) f.reverse
        (g := Polynomial.evalRingHom (0 : A)) hev) fun a => by
      rw [RingHom.comp_apply, IsLocalization.Away.lift_eq, Polynomial.coe_evalRingHom,
        Polynomial.eval_C]
  have hδ : δ = 1 := by
    apply hinj
    rw [← ringMap_ringMap, hδγ, hγg, map_one]
  rw [← hδα, hδ, map_one]

#audit_axioms
  GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stMonicInjAt_of_horrocks_of_excision

/-- **H.b for all commutative rings** from LG, T Prop 4.3(a) and Zariski excision (F.4). -/
theorem stMonicInjStatement_of {n₀ : ℕ} (hLG : StLocalGlobalStatementAt n₀)
    (hLoc : StLocalHorrocksStatementAt n₀)
    (hExc : ∀ (A : Type) [CommRing A] (N : ℕ), n₀ ≤ N → StExcisionAt A[X] N) :
    StMonicInjStatementAt n₀ :=
  fun A _ N hN => stMonicInjAt_of_horrocks_of_excision
    (stHorrocksAt_of_localGlobal hLG hLoc A N hN) (hExc A N hN)

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stMonicInjStatement_of

end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
