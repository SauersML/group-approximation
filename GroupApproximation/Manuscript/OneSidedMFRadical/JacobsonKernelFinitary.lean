import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonBlockAction
import GroupApproximation.Algebra.LaurentBinaryLinearMF
import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotentsJacobson

/-!
# `Rad_MF(EL_n(J)) = EL_n(J, JeJ) ≅ ⋃_N SL_N(F_2)`

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`
(tex lines 1126--1145):

> For `J` the inclusion of Proposition `prop:torsion-defect-ring` is an equality. …
> The kernel of `EL_n(J) → EL_n(F_2[z,z^{-1}])` lies in `GL_fs(V^n)`.  Over `F_2` every
> element of `GL_fs(V^n)` is a product of transvections, and each transvection is a
> relative root `e_{ij}(f_{uv})` or, inside one coordinate, the commutator
> `[e_{ik}(f_{uw}), e_{ki}(f_{wv})]` of two.  So `EL_n(J,JeJ)` is this kernel; the
> quotient `EL_n(F_2[z,z^{-1}])` is residually finite, so MF, and
> `Rad_MF(EL_n(J)) = EL_n(J,JeJ) ≅ ⋃_N SL_N(F_2)  (n ≥ 4)`,
> an infinite simple locally finite group.

* An element of the kernel of the symbol map has entries congruent to the identity
  modulo finite matrices, so its action on `V^n` has finite matrix support
  (`blockAct_mem_binaryGLfs_of_mem_ker`).
* Every basis transvection is the image of an element of `EL_n(J,JeJ)`
  (`binaryGLfs_le_map`), and they generate `GL_fs(V^n)`; faithfulness then gives
  `ker = EL_n(J,JeJ)` (`ker_symbolMap_eq`) and `blockAct(EL_n(J,JeJ)) = GL_fs(V^n)`.
* The reduction to the MF group `EL_n(F_2[z,z^{-1}])` contains `Rad_MF` in its kernel;
  the proposition gives the other inclusion (`mfHomKernel_eq`), and the action identifies
  the radical with `⋃_N SL_N(F_2)` (`radicalEquivSLUnion`).
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace JacobsonSymbol

open TorsionComplementaryIdempotents FinitaryLinear JacobsonLaurent

/-- The reduction `EL_n(J) → EL_n(F_2[z,z^{-1}])`. -/
noncomputable abbrev symbolMap (n : ℕ) :
    elementaryGroup (Fin n) ↥jacobsonAlgebra →* elementaryGroup (Fin n) BinaryLaurent :=
  elementaryGroupMap symbol

theorem symbol_one_apply {n : ℕ} (i j : Fin n) :
    symbol ((1 : Matrix (Fin n) (Fin n) ↥jacobsonAlgebra) i j) =
      (1 : Matrix (Fin n) (Fin n) BinaryLaurent) i j := by
  rw [Matrix.one_apply, Matrix.one_apply, apply_ite symbol, map_one, map_zero]

theorem mem_ker_symbolMap_iff {n : ℕ} {g : elementaryGroup (Fin n) ↥jacobsonAlgebra} :
    g ∈ (symbolMap n).ker ↔ ∀ i j : Fin n,
      symbol (((g : (Matrix (Fin n) (Fin n) ↥jacobsonAlgebra)ˣ) :
        Matrix (Fin n) (Fin n) ↥jacobsonAlgebra) i j) =
        (1 : Matrix (Fin n) (Fin n) BinaryLaurent) i j := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun y : elementaryGroup (Fin n) BinaryLaurent ↦
      ((y : (Matrix (Fin n) (Fin n) BinaryLaurent)ˣ) : Matrix (Fin n) (Fin n) BinaryLaurent) i j) h
    exact this
  · intro h
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact h i j

/-- `EL_n(J, JeJ)` lies in the kernel of the symbol map. -/
theorem relativeElementary_le_ker (n : ℕ) :
    relativeElementary (Fin n) defectIdeal ≤ (symbolMap n).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨i, j, hij, a, ha, rfl⟩
  have ha' : a ∈ TwoSidedIdeal.ker symbol := by
    rw [ker_symbol]
    exact ha
  have ha0 : symbol a = 0 := (TwoSidedIdeal.mem_ker symbol).mp ha'
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  apply Subtype.ext
  apply Units.ext
  show ((elementaryMatrixUnitMap symbol (elementaryUnit i j hij a) : (Matrix (Fin n) (Fin n) BinaryLaurent)ˣ) :
    Matrix (Fin n) (Fin n) BinaryLaurent) = 1
  rw [elementaryMatrixUnitMap_elementaryUnit, ha0, elementaryUnit_zero, Units.val_one]

/-- A vector whose coordinates have no coefficient at or above `Mx` lies in the block
span of the basis vectors `b_{(k,u)}`, `u < Mx`. -/
theorem mem_blockSpan_of_coeff {n : ℕ} {Mx : ℕ} {y : BinaryPower n}
    (hy : ∀ (k : Fin n) (m : ℕ), Mx ≤ m → (y k).coeff m = 0) :
    y ∈ blockSpan (binaryPowerBasis n) (Finset.univ.sigma fun _ ↦ Finset.range Mx) := by
  classical
  refine (Module.Basis.mem_span_image (binaryPowerBasis n)).mpr ?_
  intro b hb
  obtain ⟨k, m⟩ := b
  have hne : ((binaryPowerBasis n).repr y) ⟨k, m⟩ ≠ 0 := Finsupp.mem_support_iff.mp hb
  have hcoeff : (y k).coeff m ≠ 0 := by
    have := coord_binaryPowerBasis y k m
    rw [Module.Basis.coord_apply] at this
    rwa [this] at hne
  have hm : m < Mx := by
    by_contra h
    exact hcoeff (hy k m (by omega))
  simp [Finset.mem_sigma, hm]

/-- **The kernel of `EL_n(J) → EL_n(F_2[z,z^{-1}])` lies in `GL_fs(V^n)`.** -/
theorem blockAct_mem_binaryGLfs_of_mem_ker {n : ℕ} {g : elementaryGroup (Fin n) ↥jacobsonAlgebra}
    (hg : g ∈ (symbolMap n).ker) : blockAct n g ∈ binaryGLfs n := by
  classical
  rw [mem_ker_symbolMap_iff] at hg
  set G : Matrix (Fin n) (Fin n) ↥jacobsonAlgebra :=
    ((g : (Matrix (Fin n) (Fin n) ↥jacobsonAlgebra)ˣ) : Matrix (Fin n) (Fin n) ↥jacobsonAlgebra) with hG
  have hfin : ∀ i j : Fin n,
      IsFiniteMatrix ((G i j - (1 : Matrix (Fin n) (Fin n) ↥jacobsonAlgebra) i j : ↥jacobsonAlgebra) :
        Module.End (ZMod 2) JacobsonSpace) := by
    intro i j
    apply isFiniteMatrix_of_symbol_eq_zero
    rw [map_sub, hg i j, symbol_one_apply, sub_self]
  choose M hM0 hMc using hfin
  set Mx : ℕ := ∑ i, ∑ j, M i j with hMx
  have hbound : ∀ i j, M i j ≤ Mx := by
    intro i j
    calc M i j ≤ ∑ j', M i j' := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
      _ ≤ Mx := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  have hsplit : ∀ (k l : Fin n) (p : JacobsonSpace),
      ((G k l : ↥jacobsonAlgebra) : Module.End (ZMod 2) JacobsonSpace) p =
        ((G k l - (1 : Matrix (Fin n) (Fin n) ↥jacobsonAlgebra) k l : ↥jacobsonAlgebra) :
          Module.End (ZMod 2) JacobsonSpace) p +
        (((1 : Matrix (Fin n) (Fin n) ↥jacobsonAlgebra) k l : ↥jacobsonAlgebra) :
          Module.End (ZMod 2) JacobsonSpace) p := by
    intro k l p
    rw [← LinearMap.add_apply, ← Subring.coe_add, sub_add_cancel]
  have hbasis : ∀ (l : Fin n) (w : ℕ) (k : Fin n),
      blockAct n g (binaryPowerBasis n ⟨l, w⟩) k =
        ((G k l : ↥jacobsonAlgebra) : Module.End (ZMod 2) JacobsonSpace) (Polynomial.X ^ w) := by
    intro l w k
    rw [blockAct_apply, matrixAct_apply, binaryPowerBasis_apply,
      Finset.sum_eq_single l (fun m _ hm ↦ by rw [Pi.single_eq_of_ne hm, map_zero]) (by simp),
      Pi.single_eq_same]
  have hone : ∀ (k l : Fin n) (w : ℕ),
      (((1 : Matrix (Fin n) (Fin n) ↥jacobsonAlgebra) k l : ↥jacobsonAlgebra) :
        Module.End (ZMod 2) JacobsonSpace) (Polynomial.X ^ w) =
        if k = l then Polynomial.X ^ w else 0 := by
    intro k l w
    rw [Matrix.one_apply]
    by_cases h : k = l
    · rw [if_pos h, if_pos h, Subring.coe_one, Module.End.one_apply]
    · rw [if_neg h, if_neg h, Subring.coe_zero, LinearMap.zero_apply]
  refine (mem_finitary (binaryPowerBasis n)).mpr
    ⟨Finset.univ.sigma fun _ ↦ Finset.range Mx, IsSupportedOn.of_basis (fun b hb ↦ ?_) fun b hb ↦ ?_⟩
  · obtain ⟨l, w⟩ := b
    have hw : Mx ≤ w := by
      by_contra h
      exact hb (by simp [Finset.mem_sigma]; omega)
    funext k
    rw [hbasis, hsplit, hM0 k l w ((hbound k l).trans hw), zero_add, hone, binaryPowerBasis_apply]
    by_cases h : k = l
    · subst h
      rw [if_pos rfl, Pi.single_eq_same]
    · rw [if_neg h, Pi.single_eq_of_ne h]
  · obtain ⟨l, w⟩ := b
    have hw : w < Mx := by simpa [Finset.mem_sigma] using hb
    refine mem_blockSpan_of_coeff fun k m hm ↦ ?_
    rw [hbasis, hsplit, Polynomial.coeff_add, hMc k l w m ((hbound k l).trans hm), zero_add, hone]
    by_cases h : k = l
    · rw [if_pos h, Polynomial.coeff_X_pow, if_neg (by omega)]
    · rw [if_neg h, Polynomial.coeff_zero]

/-- **Every basis transvection of `V^n` is the action of an element of `EL_n(J,JeJ)`.** -/
theorem binaryGLfs_le_map (n : ℕ) (hn : 2 ≤ n) :
    binaryGLfs n ≤ (relativeElementary (Fin n) defectIdeal).map (blockAct n) := by
  rw [binaryGLfs, finitary_eq_closure_basisTransvections, Subgroup.closure_le]
  rintro _ ⟨⟨i, u⟩, ⟨j, v⟩, h, rfl⟩
  by_cases hij : i = j
  · subst hij
    have huv : u ≠ v := fun e ↦ h (by rw [e])
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    obtain ⟨k, hk⟩ := exists_ne i
    have g1 := elGen_mem_relativeElementary (I := defectIdeal) i k hk.symm (matUnitJ_mem_defectIdeal u v)
    have g2 := elGen_mem_relativeElementary (I := defectIdeal) k i hk (matUnitJ_mem_defectIdeal v v)
    refine ⟨_, ?_, blockAct_commutator_matUnit n hk.symm huv⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ g1 g2) (Subgroup.inv_mem _ g1))
      (Subgroup.inv_mem _ g2)
  · exact ⟨elGen i j hij (matUnitJ u v),
      elGen_mem_relativeElementary (I := defectIdeal) i j hij (matUnitJ_mem_defectIdeal u v),
      blockAct_elGen_matUnit n hij u v⟩

/-- **`EL_n(J,JeJ)` is the kernel of `EL_n(J) → EL_n(F_2[z,z^{-1}])`** (`n ≥ 2`). -/
theorem ker_symbolMap_eq (n : ℕ) (hn : 2 ≤ n) :
    (symbolMap n).ker = relativeElementary (Fin n) defectIdeal := by
  refine le_antisymm (fun g hg ↦ ?_) (relativeElementary_le_ker n)
  obtain ⟨h, hh, e⟩ := binaryGLfs_le_map n hn (blockAct_mem_binaryGLfs_of_mem_ker hg)
  rwa [blockAct_injective n e] at hh

theorem map_relativeElementary_eq (n : ℕ) (hn : 2 ≤ n) :
    (relativeElementary (Fin n) defectIdeal).map (blockAct n) = binaryGLfs n := by
  refine le_antisymm ?_ (binaryGLfs_le_map n hn)
  rintro _ ⟨g, hg, rfl⟩
  rw [← ker_symbolMap_eq n hn] at hg
  exact blockAct_mem_binaryGLfs_of_mem_ker hg

/-- **`Rad_MF(EL_n(J)) = EL_n(J, JeJ)`** for `n ≥ 4`. -/
theorem mfHomKernel_eq (n : ℕ) (hn : 4 ≤ n) :
    MFQuotientUnits.mfHomKernel (elementaryGroup (Fin n) ↥jacobsonAlgebra) =
      relativeElementary (Fin n) defectIdeal := by
  refine le_antisymm (fun g hg ↦ ?_) (manuscriptJacobsonRelativeElementaryInRadical n hn)
  rw [← ker_symbolMap_eq n (by omega)]
  exact MonoidHom.mem_ker.mpr ((MFQuotientUnits.mem_mfHomKernel_iff g).mp hg _
    (manuscriptSentence_laurentElementaryResiduallyFiniteMF n).2 (symbolMap n))

/-- **`Rad_MF(EL_n(J)) ≅ ⋃_N SL_N(F_2)`** for `n ≥ 4`. -/
noncomputable def radicalEquivSLUnion (n : ℕ) (hn : 4 ≤ n) :
    MFQuotientUnits.mfHomKernel (elementaryGroup (Fin n) ↥jacobsonAlgebra) ≃* binarySLUnion :=
  haveI : NeZero n := ⟨by omega⟩
  (MulEquiv.subgroupCongr (mfHomKernel_eq n hn)).trans
    (((relativeElementary (Fin n) defectIdeal).equivMapOfInjective (blockAct n)
        (blockAct_injective n)).trans
      ((MulEquiv.subgroupCongr (map_relativeElementary_eq n (by omega))).trans
        (binaryGLfsEquivSLUnion n)))

/-- **Printed (tex 1133--1139).**  The kernel of `EL_n(J) → EL_n(F_2[z,z^{-1}])` lies in
`GL_fs(V^n)`, and `EL_n(J,JeJ)` is this kernel, acting on `V^n` as all of `GL_fs(V^n)`. -/
def PrintedJacobsonKernelFinitary : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ g ∈ (symbolMap n).ker, blockAct n g ∈ binaryGLfs n) ∧
      (symbolMap n).ker = relativeElementary (Fin n) defectIdeal ∧
      (relativeElementary (Fin n) defectIdeal).map (blockAct n) = binaryGLfs n

theorem manuscriptSentence_jacobsonKernelFinitary : PrintedJacobsonKernelFinitary := by
  intro n hn
  exact ⟨fun _ hg ↦ blockAct_mem_binaryGLfs_of_mem_ker hg, ker_symbolMap_eq n hn,
    map_relativeElementary_eq n hn⟩

/-- **Printed (tex 1126--1127 and 1141--1145).**  For `J` the inclusion of the
proposition is an equality, `Rad_MF(EL_n(J)) = EL_n(J,JeJ) ≅ ⋃_N SL_N(F_2)`, an infinite
simple locally finite group (`n ≥ 4`). -/
def PrintedJacobsonRadical : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    MFQuotientUnits.mfHomKernel (elementaryGroup (Fin n) ↥jacobsonAlgebra) =
        relativeElementary (Fin n) defectIdeal ∧
      Nonempty (MFQuotientUnits.mfHomKernel (elementaryGroup (Fin n) ↥jacobsonAlgebra) ≃*
        binarySLUnion) ∧
      Infinite binarySLUnion ∧ IsSimpleGroup binarySLUnion ∧ IsLocallyFiniteGroup binarySLUnion

theorem manuscriptSentence_jacobsonRadical : PrintedJacobsonRadical := by
  intro n hn
  obtain ⟨_, hinf, hsimple, hlf⟩ := manuscriptSentence_binarySLUnionInfiniteSimpleLocallyFinite
  exact ⟨mfHomKernel_eq n hn, ⟨radicalEquivSLUnion n hn⟩, hinf, hsimple, hlf⟩

end JacobsonSymbol
end OneSidedMFRadical
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.ker_symbolMap_eq
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.mfHomKernel_eq
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.manuscriptSentence_jacobsonKernelFinitary
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.manuscriptSentence_jacobsonRadical
