import GroupApproximation.Sofic.ManuscriptExactWrappers
import GroupApproximation.Sofic.CentralInvolutionSubgroup
import GroupApproximation.Meta.AxiomGuard

/-!
# The remarks after `cor:marked-obstruction`

Manuscript `non_mf_group_notes.tex`, prose after `cor:marked-obstruction`
(tex 733--742):

> The same conclusion holds for every finite normal subgroup `F` contained in a
> subgroup `D ≤ H` whose elements lie in `K₂^ω(U)` for every operator-norm
> asymptotic representation `U` of `H` and every `ω`. [...]
>
> For `F = {1, w}`, the projection is `p_n = ½(1 + V_{w,n})`; in the corona
> corner the image of `w` is `−1` exactly [...]

The first sentence is the finite-normal obstruction with the Kazhdan datum
replaced by an arbitrary tracially killed subgroup `D`.  The engine is the rooted
`KazhdanCompressionCore.finiteNormal_le_normMFResidual_of_hyperlinear_killed`,
which already takes the kill as a hypothesis; this file carries it to the
genuine C-star corona (`finiteNormalRemark_type0`) and then to an ambient group
in any universe at literal natural matrix dimensions (`finiteNormal_remark`),
along the `Type 0` descent used by
`ManuscriptExactWrappers.manuscriptAbstractNormalKazhdanObstruction`.  The
hypothesis `hDkill` is literally the quantified form of
`ManuscriptExactWrappers.ManuscriptHSInvisible` over `D`.

For the second sentence the file proves the algebra of `p = ½(1 + v)` for an
involution `v` in any complex algebra: `v p = p`, `p² = p`, and
`v (1 − p) = −(1 − p)` (on the complementary corner `v` is `−1` exactly), and
`p = 1` when `v = 1`.  Together with `centralInvolution_remark`
(every corona representation sends a central involution of `D` to `1`) this is
the vanishing of the corner.

Scope note.  The finite-stage clause `‖W_{w,n} + 1‖ → 0` of the second remark
belongs to the inner proof of `thm:criterion` and is not restated here.
-/

namespace GroupApproximation.Full.NN12

universe u

/-! ## The finite-normal remark -/

/-- **The finite-normal remark, `Type 0` form.**  If every element of `D` is
killed in the tracial ultraproduct attached to every operator-norm almost
representation, then every genuine norm-matrix C-star-corona representation is
trivial on every finite normal subgroup contained in `D`. -/
theorem finiteNormalRemark_type0 {E : Type} [Group E] [Countable E]
    (D : Subgroup E)
    (hDkill : ∀ (B : OpAlmostRepresentation E) (U : Ultrafilter ℕ)
      (hcof : (U : Filter ℕ) ≤ Filter.cofinite) (x : E), x ∈ D →
      (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof x = 1)
    (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ D)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : E →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      F ≤ rho.ker := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  let sigma : E →* NormMatrixCoronaUnitary X :=
    (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp rho
  intro f hf
  have hres : f ∈ normMFResidual E :=
    KazhdanCompressionCore.finiteNormal_le_normMFResidual_of_hyperlinear_killed
      D hDkill F hF hf
  have hkernel : f ∈ sigma.ker :=
    NormMFInvisible.toCoronaMFInvisible
      (mem_normMFResidual_iff.mp hres) X hX sigma
  apply MonoidHom.mem_ker.mpr
  apply (normMatrixCoronaUnitaryEquiv X).symm.injective
  simpa [sigma] using MonoidHom.mem_ker.mp hkernel

/-- **The finite-normal remark** (tex 733--737), for a countable ambient group
in any universe and literal positive natural matrix dimensions: a finite normal
subgroup of a Hilbert--Schmidt invisible subgroup `D` dies in every genuine
norm-matrix C-star-corona representation. -/
theorem finiteNormal_remark :
    ∀ {H : Type u} [Group H] [Countable H]
      (D : Subgroup H)
      (hDkill : ∀ (B : OpAlmostRepresentation H) (U : Ultrafilter ℕ)
        (hcof : (U : Filter ℕ) ≤ Filter.cofinite) (x : H), x ∈ D →
        (ManuscriptExactWrappers.asymptoticUnitaryOfOpAlmost B).toUltraproductHom
          hcof x = 1)
      (F : Subgroup H) [Finite F] [F.Normal]
      (hF : F ≤ D)
      (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
    let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (by
        simpa [X] using hd n)
    ∀ Theta : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      F ≤ Theta.ker := by
  intro H _ _ D hDkill F _ _ hF d hd
  obtain ⟨H₀, _groupH₀, ⟨e⟩⟩ := Type0Transfer.exists_type0_model H
  haveI : Countable H₀ := Type0Transfer.countable_type0_model H e
  haveI : Finite (F.map e.toMonoidHom) :=
    CompressionUniverseTransfer.map_finite e F
  haveI : (F.map e.toMonoidHom).Normal :=
    CompressionUniverseTransfer.map_normal e F
  -- an almost representation of the `Type 0` model pulls back along `e`, and
  -- the two tracial ultraproduct homomorphisms agree definitionally (see the
  -- warning in `manuscriptAbstractNormalKazhdanObstruction`)
  have hDkill₀ : ∀ (B : OpAlmostRepresentation H₀) (U : Ultrafilter ℕ)
      (hcof : (U : Filter ℕ) ≤ Filter.cofinite) (y : H₀),
      y ∈ D.map e.toMonoidHom →
      (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof y = 1 := by
    rintro B U hcof _ ⟨x, hx, rfl⟩
    exact hDkill (B.comap e.toMonoidHom) U hcof x hx
  have h₀ :=
    finiteNormalRemark_type0 (D.map e.toMonoidHom) hDkill₀
      (F.map e.toMonoidHom) (Subgroup.map_mono hF)
      (fun n ↦ naturalFiniteModel (d n)) (fun n ↦ by simpa using hd n)
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  intro _X Theta x hx
  have hx₀ := MonoidHom.mem_ker.mp
    (h₀ (Theta.comp e.symm.toMonoidHom)
      (CompressionUniverseTransfer.mem_map_of_mem e hx))
  exact MonoidHom.mem_ker.mpr (by simpa using hx₀)

/-- **The case `F = {1, w}`.**  A central involution lying in a Hilbert--Schmidt
invisible subgroup is sent to `1` by every genuine corona representation. -/
theorem centralInvolution_remark :
    ∀ {H : Type u} [Group H] [Countable H]
      (D : Subgroup H)
      (hDkill : ∀ (B : OpAlmostRepresentation H) (U : Ultrafilter ℕ)
        (hcof : (U : Filter ℕ) ≤ Filter.cofinite) (x : H), x ∈ D →
        (ManuscriptExactWrappers.asymptoticUnitaryOfOpAlmost B).toUltraproductHom
          hcof x = 1)
      (w : H) (hw_sq : w ^ 2 = 1) (_hw_central : ∀ g : H, Commute w g)
      (_hw : w ∈ D)
      (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
    let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (by
        simpa [X] using hd n)
    ∀ Theta : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      Theta w = 1 := by
  intro H _ _ D hDkill w hw_sq hw_central hw d hd
  letI : (centralInvolutionSubgroup w hw_sq).Normal :=
    centralInvolutionSubgroup_normal w hw_sq hw_central
  have hle : centralInvolutionSubgroup w hw_sq ≤ D :=
    (centralInvolutionSubgroup_le_iff_mem w hw_sq D).mpr hw
  have hrem := finiteNormal_remark D hDkill (centralInvolutionSubgroup w hw_sq)
    hle d hd
  intro _X Theta
  exact MonoidHom.mem_ker.mp
    (hrem Theta (involution_mem_centralInvolutionSubgroup w hw_sq))

/-! ## The projection `p = ½(1 + v)` -/

section HalfProjection

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- `½(1 + v) + ½(1 + v) = 1 + v`. -/
theorem halfSum_add_self (v : A) :
    (2⁻¹ : ℂ) • (1 + v) + (2⁻¹ : ℂ) • (1 + v) = 1 + v := by
  have hc : (2⁻¹ : ℂ) + 2⁻¹ = 1 := by norm_num
  rw [← add_smul, hc, one_smul]

/-- An involution fixes its projection: `v · ½(1 + v) = ½(1 + v)`. -/
theorem involution_mul_halfSum (v : A) (hv : v * v = 1) :
    v * ((2⁻¹ : ℂ) • (1 + v)) = (2⁻¹ : ℂ) • (1 + v) := by
  rw [mul_smul_comm, mul_add, mul_one, hv, add_comm v 1]

/-- **`p_n = ½(1 + V_{w,n})` is idempotent** for an involution. -/
theorem halfSum_isIdempotentElem (v : A) (hv : v * v = 1) :
    IsIdempotentElem ((2⁻¹ : ℂ) • (1 + v)) := by
  show (2⁻¹ : ℂ) • (1 + v) * ((2⁻¹ : ℂ) • (1 + v)) = (2⁻¹ : ℂ) • (1 + v)
  rw [smul_mul_assoc, add_mul, one_mul, involution_mul_halfSum v hv,
    halfSum_add_self]

/-- The complementary corner `1 − p` is idempotent too. -/
theorem one_sub_halfSum_isIdempotentElem (v : A) (hv : v * v = 1) :
    IsIdempotentElem (1 - (2⁻¹ : ℂ) • (1 + v)) :=
  (halfSum_isIdempotentElem v hv).one_sub

/-- **In the complementary corner the involution is `−1` exactly**:
`v (1 − p) = −(1 − p)`. -/
theorem involution_mul_one_sub_halfSum (v : A) (hv : v * v = 1) :
    v * (1 - (2⁻¹ : ℂ) • (1 + v)) = -(1 - (2⁻¹ : ℂ) • (1 + v)) := by
  rw [mul_sub, mul_one, involution_mul_halfSum v hv, neg_sub,
    sub_eq_sub_iff_add_eq_add, halfSum_add_self, add_comm v 1]

/-- If the involution is `1`, its projection is `1`, so the corner where it is
`−1` vanishes. -/
theorem halfSum_eq_one_of_eq_one {v : A} (hv : v = 1) :
    (2⁻¹ : ℂ) • (1 + v) = 1 := by
  have hc : (2⁻¹ : ℂ) + 2⁻¹ = 1 := by norm_num
  rw [hv, smul_add, ← add_smul, hc, one_smul]

end HalfProjection

#audit_axioms finiteNormalRemark_type0
#audit_axioms finiteNormal_remark
#audit_axioms centralInvolution_remark
#audit_axioms halfSum_add_self
#audit_axioms involution_mul_halfSum
#audit_axioms halfSum_isIdempotentElem
#audit_axioms one_sub_halfSum_isIdempotentElem
#audit_axioms involution_mul_one_sub_halfSum
#audit_axioms halfSum_eq_one_of_eq_one

end GroupApproximation.Full.NN12
