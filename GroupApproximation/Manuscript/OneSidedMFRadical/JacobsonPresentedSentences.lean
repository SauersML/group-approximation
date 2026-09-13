import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonPresented
import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonKernelFinitary

/-!
# The printed sentences about `J = F_2⟨s,t | ts=1⟩`

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`
(tex lines 1122--1134):

> The Toeplitz--Jacobson algebra `J = F_2⟨s,t | ts=1⟩` has `1-st ≠ 0` of order two, while
> `J/J(1-st)J ≅ F_2[z,z^{-1}] ≠ 0`, so `1-st` is not full and Theorem `thm:full-defect-ring`
> does not apply; Proposition `prop:torsion-defect-ring` shows that `EL_n(J)` is not MF for
> `n ≥ 4`.  For `J` the inclusion of Proposition `prop:torsion-defect-ring` is an equality.
> The algebra `J` acts faithfully on `V = F_2^{(ℕ)}` by the shift, `e = 1-st` is the
> projection onto the first vector `b_0` of the standard basis `(b_j)`, and `JeJ` is the
> ring of matrices with finitely many nonzero entries in this basis.  Let `GL_fs(V^n)` be the
> group of automorphisms `g` of `V^n` such that `g-I` has finite matrix support in this
> basis, …  The kernel of `EL_n(J) → EL_n(F_2[z,z^{-1}])` lies in `GL_fs(V^n)`.

The carriers `JacobsonSymbol.manuscriptSentence_*` state these sentences for the operator
model `jacobsonAlgebra`.  Here they are stated for the presented algebra
`ToeplitzJacobson = F_2⟨s,t⟩/(ts = 1)` and transported along
`jacobsonEquiv : J ≃+* jacobsonAlgebra`:

* two-sided ideals and relative elementary groups move along a ring isomorphism
  (`mem_span_singleton_map_iff`, `map_relativeElementary_of_equiv`);
* `J(1-st)J` corresponds to the operator defect ideal (`mem_presDefectIdeal_iff`), so the
  symbol `J → F_2[z,z^{-1}]` has kernel `J(1-st)J` (`ker_presSymbol`);
* the reduction `EL_n(J) → EL_n(F_2[z,z^{-1}])` is the operator reduction precomposed with
  `EL_n(jacobsonEquiv)` (`presSymbolMap_apply`), which gives the kernel, its action on
  `V^n`, and `Rad_MF(EL_n(J)) = EL_n(J,J(1-st)J)` (`presMfHomKernel_eq`).
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace JacobsonPresented

open TorsionComplementaryIdempotents JacobsonSymbol FinitaryLinear JacobsonLaurent

attribute [local instance] FullDefectRing.countable_elementaryGroup

noncomputable section

/-! ## Transport along a ring isomorphism -/

section Transport

theorem map_one_sub_mul {R S F : Type*} [Ring R] [Ring S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (a b : R) : f (1 - a * b) = 1 - f a * f b := by
  rw [map_sub, map_one, map_mul]

theorem two_nsmul_eq_zero_of_zmodTwo {A : Type*} [Ring A] [Algebra (ZMod 2) A] (x : A) :
    (2 : ℕ) • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]

theorem span_singleton_le_comap {R S : Type*} [Ring R] [Ring S] (φ : R ≃+* S) (a : R) :
    TwoSidedIdeal.span {a} ≤ TwoSidedIdeal.comap φ (TwoSidedIdeal.span {φ a}) :=
  TwoSidedIdeal.span_le.mpr (Set.singleton_subset_iff.mpr
    ((TwoSidedIdeal.mem_comap φ).mpr (TwoSidedIdeal.subset_span (Set.mem_singleton (φ a)))))

theorem mem_span_singleton_map_iff {R S : Type*} [Ring R] [Ring S] (φ : R ≃+* S) (a x : R) :
    x ∈ TwoSidedIdeal.span {a} ↔ φ x ∈ TwoSidedIdeal.span {φ a} := by
  refine ⟨fun hx ↦ (TwoSidedIdeal.mem_comap φ).mp (span_singleton_le_comap φ a hx), fun hx ↦ ?_⟩
  have h := (TwoSidedIdeal.mem_comap φ.symm).mp (span_singleton_le_comap φ.symm (φ a) hx)
  rwa [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply] at h

theorem elementaryCoefficientEquiv_elGen {ι R S : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
    [Ring S] (φ : R ≃+* S) (i j : ι) (hij : i ≠ j) (a : R) :
    elementaryCoefficientEquiv φ (elGen i j hij a) = elGen i j hij (φ a) :=
  Subtype.ext (elementaryMatrixUnitMap_elementaryUnit φ.toRingHom i j hij a)

/-- A ring isomorphism carrying `I` onto `J` carries `EL_ι(R,I)` onto `EL_ι(S,J)`. -/
theorem map_relativeElementary_of_equiv {ι R S : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
    [Ring S] (φ : R ≃+* S) {I : TwoSidedIdeal R} {J : TwoSidedIdeal S}
    (hIJ : ∀ x, x ∈ I ↔ φ x ∈ J) :
    (relativeElementary ι I).map (elementaryCoefficientEquiv φ).toMonoidHom =
      relativeElementary ι J := by
  unfold relativeElementary
  rw [Subgroup.map_normalClosure _ (elementaryCoefficientEquiv φ).toMonoidHom
    (elementaryCoefficientEquiv φ).surjective]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨i, j, hij, a, ha, rfl⟩, rfl⟩
    exact ⟨i, j, hij, φ a, (hIJ a).mp ha, elementaryCoefficientEquiv_elGen φ i j hij a⟩
  · rintro ⟨i, j, hij, b, hb, rfl⟩
    refine ⟨elGen i j hij (φ.symm b), ⟨i, j, hij, φ.symm b, (hIJ _).mpr ?_, rfl⟩,
      (elementaryCoefficientEquiv_elGen φ i j hij (φ.symm b)).trans
        (congrArg (elGen i j hij) (φ.apply_symm_apply b))⟩
    rw [RingEquiv.apply_symm_apply]
    exact hb

theorem mem_relativeElementary_of_equiv_iff {ι R S : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] [Ring S] (φ : R ≃+* S) {I : TwoSidedIdeal R} {J : TwoSidedIdeal S}
    (hIJ : ∀ x, x ∈ I ↔ φ x ∈ J) (g : elementaryGroup ι R) :
    g ∈ relativeElementary ι I ↔ elementaryCoefficientEquiv φ g ∈ relativeElementary ι J := by
  rw [← map_relativeElementary_of_equiv φ hIJ]
  exact (Subgroup.mem_map_iff_mem (f := (elementaryCoefficientEquiv φ).toMonoidHom)
    (elementaryCoefficientEquiv φ).injective).symm

end Transport

/-! ## The defect ideal and the symbol -/

/-- The printed ideal `J(1-st)J`. -/
abbrev presDefectIdeal : TwoSidedIdeal ToeplitzJacobson :=
  TwoSidedIdeal.span {(1 : ToeplitzJacobson) - presS * presT}

theorem jacobsonEquiv_one_sub :
    jacobsonEquiv ((1 : ToeplitzJacobson) - presS * presT) = 1 - jacobsonS * jacobsonT :=
  (map_one_sub_mul jacobsonEquiv presS presT).trans
    (congrArg₂ (fun u v : ↥jacobsonAlgebra ↦ 1 - u * v) jacobsonEquiv_presS jacobsonEquiv_presT)

theorem presDefect_ne_zero : (1 : ToeplitzJacobson) - presS * presT ≠ 0 := fun h ↦
  jacobson_one_sub_ne_zero (jacobsonEquiv_one_sub.symm.trans
    ((congrArg (fun x ↦ jacobsonEquiv x) h).trans (map_zero jacobsonEquiv)))

theorem presDefect_two_nsmul : (2 : ℕ) • ((1 : ToeplitzJacobson) - presS * presT) = 0 :=
  two_nsmul_eq_zero_of_zmodTwo _

theorem mem_presDefectIdeal_iff (x : ToeplitzJacobson) :
    x ∈ presDefectIdeal ↔ jacobsonEquiv x ∈ defectIdeal := by
  have h := mem_span_singleton_map_iff jacobsonEquiv ((1 : ToeplitzJacobson) - presS * presT) x
  rw [jacobsonEquiv_one_sub] at h
  exact h

/-- The symbol `J → F_2[z,z^{-1}]`, `s ↦ z`, `t ↦ z^{-1}`. -/
def presSymbol : ToeplitzJacobson →+* BinaryLaurent := symbol.comp jacobsonEquiv.toRingHom

theorem presSymbol_apply (x : ToeplitzJacobson) : presSymbol x = symbol (jacobsonEquiv x) := rfl

theorem presSymbol_presS : presSymbol presS = LaurentPolynomial.T 1 := by
  rw [presSymbol_apply, jacobsonEquiv_presS, symbol_jacobsonS]

theorem presSymbol_presT : presSymbol presT = LaurentPolynomial.T (-1) := by
  rw [presSymbol_apply, jacobsonEquiv_presT, symbol_jacobsonT]

theorem presSymbol_surjective : Function.Surjective presSymbol := fun y ↦
  (symbol_surjective y).elim fun x hx ↦ ⟨jacobsonEquiv.symm x, by
    rw [presSymbol_apply, RingEquiv.apply_symm_apply]
    exact hx⟩

theorem ker_presSymbol : TwoSidedIdeal.ker presSymbol = presDefectIdeal := by
  ext x
  have h := TwoSidedIdeal.mem_ker symbol (x := jacobsonEquiv x)
  rw [ker_symbol] at h
  rw [TwoSidedIdeal.mem_ker, presSymbol_apply, ← h]
  exact (mem_presDefectIdeal_iff x).symm

theorem presDefectIdeal_ringCon : presDefectIdeal.ringCon = RingCon.ker presSymbol := by
  have h : (TwoSidedIdeal.ker presSymbol).ringCon = RingCon.ker presSymbol :=
    RingCon.ext fun _ _ ↦ (TwoSidedIdeal.ker_ringCon presSymbol).trans
      (RingCon.ker_apply presSymbol).symm
  rw [ker_presSymbol] at h
  exact h

/-- **`J/J(1-st)J ≅ F_2[z,z^{-1}]`.** -/
theorem nonempty_presQuotientEquiv :
    Nonempty (presDefectIdeal.ringCon.Quotient ≃+* BinaryLaurent) := by
  rw [presDefectIdeal_ringCon]
  exact ⟨RingCon.quotientKerEquivOfSurjective presSymbol presSymbol_surjective⟩

theorem presQuotient_nontrivial : Nontrivial presDefectIdeal.ringCon.Quotient := by
  obtain ⟨e⟩ := nonempty_presQuotientEquiv
  exact e.symm.injective.nontrivial

/-- **`1 - st` is not full.** -/
theorem presDefectIdeal_ne_top : presDefectIdeal ≠ ⊤ := by
  intro h
  have h1 : (1 : ToeplitzJacobson) ∈ TwoSidedIdeal.ker presSymbol := by
    rw [ker_presSymbol, h]
    exact TwoSidedIdeal.mem_top
  rw [TwoSidedIdeal.mem_ker, map_one] at h1
  exact one_ne_zero h1

/-- **`EL_n(J)` is not MF for `n ≥ 4`.** -/
theorem presElementaryNotMF (n : ℕ) (hn : 4 ≤ n) :
    ¬ IsCDEOperatorMF (elementaryGroup (Fin n) ToeplitzJacobson) :=
  not_isCDEOperatorMF_of_pair presS presT presT_mul_presS (by norm_num) presDefect_two_nsmul
    presDefect_ne_zero hn

/-! ## The universal property of the presentation -/

theorem presAlgHom_ext {A : Type*} [Semiring A] [Algebra (ZMod 2) A]
    {φ ψ : ToeplitzJacobson →ₐ[ZMod 2] A} (hS : φ presS = ψ presS) (hT : φ presT = ψ presT) :
    φ = ψ := by
  refine RingQuot.ringQuot_ext' (ZMod 2) φ ψ (FreeAlgebra.hom_ext (funext fun i ↦ ?_))
  fin_cases i
  · exact hS
  · exact hT

/-- **`J = F_2⟨s,t | ts=1⟩`**: an `F_2`-algebra map out of `J` is a pair `a, b` with
`ba = 1`, and nothing else. -/
theorem exists_unique_algHom (A : Type) [Semiring A] [Algebra (ZMod 2) A] (a b : A)
    (hab : b * a = 1) :
    ∃! φ : ToeplitzJacobson →ₐ[ZMod 2] A, φ presS = a ∧ φ presT = b := by
  have hrel : ∀ ⦃x y : FreeJ⦄, TSRelation x y →
      FreeAlgebra.lift (ZMod 2) ![a, b] x = FreeAlgebra.lift (ZMod 2) ![a, b] y := by
    intro x y h
    cases h
    rw [map_mul, map_one, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
    exact hab
  have hS : RingQuot.liftAlgHom (ZMod 2) ⟨FreeAlgebra.lift (ZMod 2) ![a, b], hrel⟩ presS = a :=
    (RingQuot.liftAlgHom_mkAlgHom_apply (ZMod 2) (FreeAlgebra.lift (ZMod 2) ![a, b]) hrel
      (FreeAlgebra.ι (ZMod 2) (0 : Fin 2))).trans (FreeAlgebra.lift_ι_apply ![a, b] 0)
  have hT : RingQuot.liftAlgHom (ZMod 2) ⟨FreeAlgebra.lift (ZMod 2) ![a, b], hrel⟩ presT = b :=
    (RingQuot.liftAlgHom_mkAlgHom_apply (ZMod 2) (FreeAlgebra.lift (ZMod 2) ![a, b]) hrel
      (FreeAlgebra.ι (ZMod 2) (1 : Fin 2))).trans (FreeAlgebra.lift_ι_apply ![a, b] 1)
  exact ⟨RingQuot.liftAlgHom (ZMod 2) ⟨FreeAlgebra.lift (ZMod 2) ![a, b], hrel⟩, ⟨hS, hT⟩,
    fun ψ hψ ↦ presAlgHom_ext (hψ.1.trans hS.symm) (hψ.2.trans hT.symm)⟩

/-! ## The shift action -/

theorem shiftRep_one_sub :
    shiftRep ((1 : ToeplitzJacobson) - presS * presT) = 1 - shiftUp * shiftDown :=
  (map_one_sub_mul shiftRep presS presT).trans
    (congrArg₂ (fun u v : Module.End (ZMod 2) JacobsonSpace ↦ 1 - u * v)
      shiftRep_presS shiftRep_presT)

/-- **`e = 1 - st` is the projection onto `b_0 = X^0`.** -/
theorem presE_apply_X_pow (N : ℕ) :
    shiftRep ((1 : ToeplitzJacobson) - presS * presT) (Polynomial.X ^ N) =
      if N = 0 then 1 else 0 :=
  (congrArg (fun T : Module.End (ZMod 2) JacobsonSpace ↦ T (Polynomial.X ^ N))
    shiftRep_one_sub).trans (jacobsonE_apply_X_pow N)

/-- **`JeJ` is the ring of finite matrices.** -/
theorem mem_presDefectIdeal_iff_isFiniteMatrix (x : ToeplitzJacobson) :
    x ∈ presDefectIdeal ↔ IsFiniteMatrix (shiftRep x) :=
  (mem_presDefectIdeal_iff x).trans (mem_defectIdeal_iff (jacobsonEquiv x))

/-! ## `EL_n(J) → EL_n(F_2[z,z^{-1}])` and its kernel -/

/-- The reduction `EL_n(J) → EL_n(F_2[z,z^{-1}])`. -/
abbrev presSymbolMap (n : ℕ) :
    elementaryGroup (Fin n) ToeplitzJacobson →* elementaryGroup (Fin n) BinaryLaurent :=
  elementaryGroupMap presSymbol

theorem presSymbolMap_apply (n : ℕ) (g : elementaryGroup (Fin n) ToeplitzJacobson) :
    presSymbolMap n g = symbolMap n (elementaryCoefficientEquiv jacobsonEquiv g) :=
  Subtype.ext (Units.ext (Matrix.ext fun _ _ ↦ rfl))

theorem presKer_eq (n : ℕ) (hn : 2 ≤ n) :
    (presSymbolMap n).ker = relativeElementary (Fin n) presDefectIdeal := by
  ext g
  rw [MonoidHom.mem_ker, presSymbolMap_apply, ← MonoidHom.mem_ker, ker_symbolMap_eq n hn]
  exact (mem_relativeElementary_of_equiv_iff jacobsonEquiv mem_presDefectIdeal_iff g).symm

/-- The action of `EL_n(J)` on `V^n`, by the shift action in each matrix entry. -/
def presBlockAct (n : ℕ) :
    elementaryGroup (Fin n) ToeplitzJacobson →* (BinaryPower n ≃ₗ[ZMod 2] BinaryPower n) :=
  (blockAct n).comp (elementaryCoefficientEquiv jacobsonEquiv).toMonoidHom

theorem presBlockAct_apply (n : ℕ) (g : elementaryGroup (Fin n) ToeplitzJacobson)
    (x : BinaryPower n) (i : Fin n) :
    presBlockAct n g x i =
      ∑ j, shiftRep (((g : (Matrix (Fin n) (Fin n) ToeplitzJacobson)ˣ) :
        Matrix (Fin n) (Fin n) ToeplitzJacobson) i j) (x j) := rfl

theorem presBlockAct_injective (n : ℕ) : Function.Injective (presBlockAct n) :=
  (blockAct_injective n).comp (elementaryCoefficientEquiv jacobsonEquiv).injective

/-- **The kernel of `EL_n(J) → EL_n(F_2[z,z^{-1}])` lies in `GL_fs(V^n)`.** -/
theorem presBlockAct_mem_binaryGLfs {n : ℕ} {g : elementaryGroup (Fin n) ToeplitzJacobson}
    (hg : g ∈ (presSymbolMap n).ker) : presBlockAct n g ∈ binaryGLfs n := by
  have h : elementaryCoefficientEquiv jacobsonEquiv g ∈ (symbolMap n).ker := by
    rw [MonoidHom.mem_ker, ← presSymbolMap_apply]
    exact MonoidHom.mem_ker.mp hg
  exact blockAct_mem_binaryGLfs_of_mem_ker h

theorem presMap_relativeElementary_eq (n : ℕ) (hn : 2 ≤ n) :
    (relativeElementary (Fin n) presDefectIdeal).map (presBlockAct n) = binaryGLfs n := by
  rw [presBlockAct, ← Subgroup.map_map,
    map_relativeElementary_of_equiv jacobsonEquiv mem_presDefectIdeal_iff]
  exact map_relativeElementary_eq n hn

/-- **For `J` the inclusion of `prop:torsion-defect-ring` is an equality**:
`Rad_MF(EL_n(J)) = EL_n(J, J(1-st)J)` for `n ≥ 4`. -/
theorem presMfHomKernel_eq (n : ℕ) (hn : 4 ≤ n) :
    MFQuotientUnits.mfHomKernel (elementaryGroup (Fin n) ToeplitzJacobson) =
      relativeElementary (Fin n) presDefectIdeal := by
  refine le_antisymm (fun g hg ↦ ?_) (relativeElementary_le_mfHomKernel presS presT
    presT_mul_presS (by norm_num) presDefect_two_nsmul hn)
  rw [← presKer_eq n (by omega)]
  exact MonoidHom.mem_ker.mpr ((MFQuotientUnits.mem_mfHomKernel_iff g).mp hg _
    (manuscriptSentence_laurentElementaryResiduallyFiniteMF n).2 (presSymbolMap n))

/-! ## The printed endpoints -/

/-- **Printed (tex 1122--1126).**  `J = F_2⟨s,t | ts=1⟩`: the relation `ts = 1` holds and
an `F_2`-algebra map out of `J` is exactly a pair `a, b` with `ba = 1`; `1 - st ≠ 0` has
order two; `J/J(1-st)J ≅ F_2[z,z^{-1}] ≠ 0` through the symbol `s ↦ z`, `t ↦ z^{-1}`, whose
kernel is `J(1-st)J`, so `1 - st` is not full; and `EL_n(J)` is not MF for `n ≥ 4`. -/
def PrintedToeplitzJacobsonAlgebra : Prop :=
  presT * presS = 1 ∧
    (∀ (A : Type) [Semiring A] [Algebra (ZMod 2) A] (a b : A), b * a = 1 →
      ∃! φ : ToeplitzJacobson →ₐ[ZMod 2] A, φ presS = a ∧ φ presT = b) ∧
    (1 : ToeplitzJacobson) - presS * presT ≠ 0 ∧
    (2 : ℕ) • ((1 : ToeplitzJacobson) - presS * presT) = 0 ∧
    presSymbol presS = LaurentPolynomial.T 1 ∧ presSymbol presT = LaurentPolynomial.T (-1) ∧
    Function.Surjective presSymbol ∧
    TwoSidedIdeal.ker presSymbol =
      TwoSidedIdeal.span {(1 : ToeplitzJacobson) - presS * presT} ∧
    Nonempty ((TwoSidedIdeal.span {(1 : ToeplitzJacobson) - presS * presT}).ringCon.Quotient ≃+*
      BinaryLaurent) ∧
    Nontrivial ((TwoSidedIdeal.span {(1 : ToeplitzJacobson) - presS * presT}).ringCon.Quotient) ∧
    TwoSidedIdeal.span {(1 : ToeplitzJacobson) - presS * presT} ≠ ⊤ ∧
    ∀ n : ℕ, 4 ≤ n → ¬ IsCDEOperatorMF (elementaryGroup (Fin n) ToeplitzJacobson)

theorem manuscriptSentence_toeplitzJacobsonAlgebra : PrintedToeplitzJacobsonAlgebra :=
  ⟨presT_mul_presS, exists_unique_algHom, presDefect_ne_zero, presDefect_two_nsmul,
    presSymbol_presS, presSymbol_presT, presSymbol_surjective, ker_presSymbol,
    nonempty_presQuotientEquiv, presQuotient_nontrivial, presDefectIdeal_ne_top,
    presElementaryNotMF⟩

/-- **Printed (tex 1127--1131).**  `J` acts faithfully on `V = F_2[X]` by the shift,
`e = 1 - st` is the projection onto `b_0 = X^0`, and `JeJ` is the ring of matrices with
finitely many nonzero entries in the basis `b_j = X^j`. -/
def PrintedToeplitzJacobsonShiftAction : Prop :=
  Function.Injective shiftRep ∧ shiftRep presS = shiftUp ∧ shiftRep presT = shiftDown ∧
    (∀ N : ℕ, shiftRep ((1 : ToeplitzJacobson) - presS * presT) (Polynomial.X ^ N) =
      if N = 0 then 1 else 0) ∧
    ∀ x : ToeplitzJacobson,
      x ∈ TwoSidedIdeal.span {(1 : ToeplitzJacobson) - presS * presT} ↔
        IsFiniteMatrix (shiftRep x)

theorem manuscriptSentence_toeplitzJacobsonShiftAction : PrintedToeplitzJacobsonShiftAction :=
  ⟨shiftRep_injective, shiftRep_presS, shiftRep_presT, presE_apply_X_pow,
    mem_presDefectIdeal_iff_isFiniteMatrix⟩

/-- **Printed (tex 1133--1134).**  The kernel of `EL_n(J) → EL_n(F_2[z,z^{-1}])` lies in
`GL_fs(V^n)`:
`EL_n(J)` acts faithfully on `V^n` by the shift in each entry, the kernel acts with finite
matrix support, and for `n ≥ 2` the kernel is `EL_n(J, J(1-st)J)`, which the action carries
onto `GL_fs(V^n)`. -/
def PrintedToeplitzJacobsonKernelFinitary : Prop :=
  ∀ n : ℕ,
    (∀ (g : elementaryGroup (Fin n) ToeplitzJacobson) (x : BinaryPower n) (i : Fin n),
      presBlockAct n g x i =
        ∑ j, shiftRep (((g : (Matrix (Fin n) (Fin n) ToeplitzJacobson)ˣ) :
          Matrix (Fin n) (Fin n) ToeplitzJacobson) i j) (x j)) ∧
    Function.Injective (presBlockAct n) ∧
    (∀ g ∈ (presSymbolMap n).ker, presBlockAct n g ∈ binaryGLfs n) ∧
    (2 ≤ n →
      (presSymbolMap n).ker = relativeElementary (Fin n)
          (TwoSidedIdeal.span {(1 : ToeplitzJacobson) - presS * presT}) ∧
        (relativeElementary (Fin n)
            (TwoSidedIdeal.span {(1 : ToeplitzJacobson) - presS * presT})).map
          (presBlockAct n) = binaryGLfs n)

theorem manuscriptSentence_toeplitzJacobsonKernelFinitary :
    PrintedToeplitzJacobsonKernelFinitary := fun n ↦
  ⟨presBlockAct_apply n, presBlockAct_injective n, fun _ hg ↦ presBlockAct_mem_binaryGLfs hg,
    fun hn ↦ ⟨presKer_eq n hn, presMap_relativeElementary_eq n hn⟩⟩

/-- **Printed (tex 1126--1127).**  For `J` the inclusion of Proposition
`prop:torsion-defect-ring` is an equality: `Rad_MF(EL_n(J)) = EL_n(J, J(1-st)J)` for
`n ≥ 4`. -/
def PrintedToeplitzJacobsonRadicalEquality : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    MFQuotientUnits.mfHomKernel (elementaryGroup (Fin n) ToeplitzJacobson) =
      relativeElementary (Fin n) (TwoSidedIdeal.span {(1 : ToeplitzJacobson) - presS * presT})

theorem manuscriptSentence_toeplitzJacobsonRadicalEquality :
    PrintedToeplitzJacobsonRadicalEquality :=
  presMfHomKernel_eq

end

end JacobsonPresented
end OneSidedMFRadical
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonPresented.manuscriptSentence_toeplitzJacobsonAlgebra
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonPresented.manuscriptSentence_toeplitzJacobsonShiftAction
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonPresented.manuscriptSentence_toeplitzJacobsonKernelFinitary
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonPresented.manuscriptSentence_toeplitzJacobsonRadicalEquality
