import GroupApproximation.Sofic.UltraproductKazhdanTransport
import GroupApproximation.Sofic.UltraproductModelConstruction

/-!
# The constructor for the manuscript's ultraproduct ambient (KT.01--KT.09)

`Sofic/UltraproductKazhdanTransport.lean` states the printed proof of
the Kazhdan transport result in `non_mf_groups_exist.tex` relative to a
bundled ambient `UltraproductAdjointModel`, one field per sentence of manuscript
steps KT.01--KT.09, and proves KT.10 and KT.11 against it.  Until this file
nothing constructed such an ambient, so the printed proof was formalized only
conditionally: `ultraproductKazhdanTransport` had a hypothesis that no term
discharged.

This file discharges it.  It assembles

* `Sofic/UltraproductModelConstruction.lean` -- the vector ultraproduct `K_ω`,
  the algebra `B_ω` and its `ℂ`-linear action on `K_ω`, and the adjoint
  representation `π g = [Ad U_n g]_ω` (KT.01--KT.05);
* `Sofic/UltraproductDedekindFinite.lean` -- finiteness of `B_ω` (KT.06), as an
  instance rather than a hypothesis;
* `Sofic/UltraproductKazhdanProjection.lean` -- the Kazhdan spectral gap, the
  projection `P` with `ran P = Fix`, and the one-sided compression `P ≤ Q`
  (KT.07--KT.09)

into `ultraproductAdjointModel`, which takes exactly the hypotheses of
the Kazhdan transport result itself -- property `(T)` for `Γ`, the compression
`s ι(Γ) s⁻¹ ⊆ ι(Γ)`, positivity of the dimensions, and operator-norm asymptotic
multiplicativity of `U` -- plus the free ultrafilter the printed proof fixes.
Nothing else is assumed.

## The weight

The construction of `K_ω` is written at an arbitrary nonnegative weight `w`,
because the weighted transport theorem of the superseded manuscript revision (the section it lived in, and its label, are no longer printed) needs it at a rank weight.  The
unweighted interface is the **dimension weight** `w n = d_n`, at which the
renormalized coordinate norm `matMass x / w n` is literally the manuscript's
normalized Hilbert--Schmidt norm `hsNormSq`.  `weightBounded_dimWeight_iff` and
`weightNull_dimWeight_iff_tendsto` are that dictionary; the second is
`UltraproductScaledTransport.weightNull_dimension_iff_tendsto` along a general
filter, which is what the ultraproduct proof needs, since its defect condition
is read along `ω` and not along `atTop`.

## One deliberate deviation, stated plainly

The manuscript writes `B_ω = ∏_ω B(K_n)`, the norm ultraproduct along the same
ultrafilter `ω` that indexes `K_ω`.  The algebra used here is instead the
cofinite norm corona `∏_∞ B(K_n)` of `Analysis/NormMatrixCorona.lean`, i.e. the
bounded operator sequences modulo those whose norms tend to `0` along the
cofinite filter.  This is not a weakening:

* the corona surjects onto `∏_ω B(K_n)` for every `ω`, because a cofinite-null
  sequence is `ω`-null whenever `ω ≤ cofinite`;
* every object the printed proof builds inside `B_ω` already lives in the
  corona -- `π` does, because the multiplicative defects of `U_n` vanish along
  `atTop` and not merely along `ω`, and `P` does, because it is a continuous
  functional calculus of `π`;
* the corona acts on `K_ω` (`applyFam_mem_massNull_of_isC0`), which is the only
  thing steps KT.03, KT.08 and KT.11 ask of the algebra;
* finiteness, KT.06, is proved for the corona in
  `Sofic/UltraproductDedekindFinite.lean`.

Faithfulness of the action, which the manuscript's KT.04 asserts, is never used:
the interface reads `Fix ⊆ V·Fix` back as `P ≤ Q` through the *algebraic*
identities `kt_09_conjugate_mul_proj` and `kt_09_proj_mul_conjugate`, not
through an inclusion of ranges, so no separation property of the action is
required anywhere in the chain.

TeX references are by `\label` and sectioning command, never by line number.
-/

namespace GroupApproximation
namespace UltraproductModelConstruction

open Filter Matrix
open ScaledKazhdanTransport UltraproductScaledTransport
open UltraproductKazhdanProjection
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## The dimension weight

At the weight `w n = card (Y n)` the renormalized coordinate norm of
`Sofic/UltraproductScaledTransport.lean` is the manuscript's normalized
Hilbert--Schmidt norm, so the weighted predicates `WeightBounded` and
`WeightNull` become the unweighted hypotheses of `UltraproductAdjointModel`. -/

/-- The dimension weight `w n = d_n` of the manuscript's coordinate spaces
`K_n = L²(M_{d n}, tr_{d n})`. -/
def dimWeight (Y : ℕ → FiniteModel) : ℕ → ℝ :=
  fun n ↦ (Fintype.card (Y n) : ℝ)

/-- The dimension weight, unfolded.  It is definitional, and is recorded so that
statements about `WeightBounded` and `WeightNull` at this weight can be read
against `matMass_le_iff_hsNormSq_le` without unfolding a `def` by hand. -/
@[simp] theorem dimWeight_apply (Y : ℕ → FiniteModel) (n : ℕ) :
    dimWeight Y n = (Fintype.card (Y n) : ℝ) := rfl

/-- The dimension weight is nonnegative, which is the standing hypothesis under
which the construction of `K_ω` has a submodule of null families. -/
theorem dimWeight_nonneg (Y : ℕ → FiniteModel) (n : ℕ) : 0 ≤ dimWeight Y n :=
  Nat.cast_nonneg _

/-- At the dimension weight the printed mass bound `Tr(x_n* x_n) ≤ C w_n` is the
normalized Hilbert--Schmidt bound `hsNormSq x_n ≤ C`, coordinate by
coordinate. -/
theorem weightBounded_dimWeight_iff {Y : ℕ → FiniteModel}
    (hY : ∀ n, 0 < Fintype.card (Y n)) (C : ℝ)
    (ξ : ∀ n, Matrix (Y n) (Y n) ℂ) :
    WeightBounded Y (dimWeight Y) C ξ ↔ ∀ n, hsNormSq (Y n) (ξ n) ≤ C := by
  constructor
  · intro h n
    have hn : matMass (ξ n) ≤ C * (Fintype.card (Y n) : ℝ) := h n
    exact (matMass_le_iff_hsNormSq_le (Y n) (hY n) (ξ n) C).mp hn
  · intro h n
    show matMass (ξ n) ≤ C * dimWeight Y n
    exact (matMass_le_iff_hsNormSq_le (Y n) (hY n) (ξ n) C).mpr (h n)

/-- At the dimension weight the printed defect condition along a filter `l` is
exactly normalized Hilbert--Schmidt convergence to zero along `l`.

`UltraproductScaledTransport.weightNull_dimension_iff_tendsto` is this statement
at `atTop`; the printed ultraproduct proof reads its defect hypothesis along the
ultrafilter `ω`, so the general filter is what the ambient needs. -/
theorem weightNull_dimWeight_iff_tendsto {Y : ℕ → FiniteModel}
    (hY : ∀ n, 0 < Fintype.card (Y n)) (l : Filter ℕ)
    (y : ∀ n, Matrix (Y n) (Y n) ℂ) :
    WeightNull Y (dimWeight Y) l y ↔
      Filter.Tendsto (fun n ↦ hsNormSq (Y n) (y n)) l (nhds 0) := by
  have hdist : ∀ n : ℕ,
      dist (hsNormSq (Y n) (y n)) 0 = hsNormSq (Y n) (y n) := by
    intro n
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNormSq_nonneg _ _)]
  constructor
  · intro h
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have hhalf : (0 : ℝ) < δ / 2 := by linarith
    filter_upwards [h (δ / 2) hhalf] with n hn
    have hn' : matMass (y n) ≤ δ / 2 * (Fintype.card (Y n) : ℝ) := hn
    have h1 : hsNormSq (Y n) (y n) ≤ δ / 2 :=
      (matMass_le_iff_hsNormSq_le (Y n) (hY n) (y n) (δ / 2)).mp hn'
    show dist (hsNormSq (Y n) (y n)) 0 < δ
    rw [hdist n]
    linarith
  · intro h ε hε
    filter_upwards [(Metric.tendsto_nhds.mp h) ε hε] with n hn
    have h1 : dist (hsNormSq (Y n) (y n)) 0 < ε := hn
    rw [hdist n] at h1
    exact (matMass_le_iff_hsNormSq_le (Y n) (hY n) (y n) ε).mpr h1.le

/-! ## The manuscript's coordinate models -/

/-- The manuscript's coordinate models `M_{d_n}(ℂ)`, as a family of finite
models: this is the family `Y` at which the construction of
`Sofic/UltraproductModelConstruction.lean` is instantiated to meet the
unweighted interface `UltraproductAdjointModel`. -/
abbrev natModels (d : ℕ → ℕ) : ℕ → FiniteModel :=
  fun n ↦ naturalFiniteModel (d n)

/-- Positive dimensions make the coordinate models nonempty; this is the only
place the hypothesis `0 < d n` of the Kazhdan transport result is consumed by the
construction. -/
theorem nonempty_natModels {d : ℕ → ℕ} (hd : ∀ n, 0 < d n) (n : ℕ) :
    Nonempty (natModels d n) :=
  Fintype.card_pos_iff.mp (by simpa using hd n)

/-- Positive dimensions in the form the weight dictionary consumes. -/
theorem card_natModels_pos {d : ℕ → ℕ} (hd : ∀ n, 0 < d n) (n : ℕ) :
    0 < Fintype.card (natModels d n) := by
  simpa using hd n

/-- `π g`, read inside the algebra, is the coercion of the unitary `π g`.  The
two are the same term: `piHom` is `piUnitary` composed with the inclusion of the
unitary group, so this identity is definitional.  It is recorded because the
KT.07--KT.09 bundle states its conclusions with the coercion and the interface
states its fields with `piHom`. -/
@[simp] theorem piHom_eq_coe_piUnitary (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    {H : Type*} [Group H] (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)
    (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (Y n) (Y n) ℂ) -
        (U n g : Matrix (Y n) (Y n) ℂ) * (U n h : Matrix (Y n) (Y n) ℂ)‖ ≤ ε)
    (g : H) :
    piHom Y U hU g =
      ((piUnitary Y U hU g : unitary (AdjointCorona Y)) : AdjointCorona Y) :=
  rfl

/-! ## KT.07--KT.09 on the constructed ambient -/

/-- **The Kazhdan compression bundle on the manuscript's own ambient.**

`Sofic/UltraproductKazhdanProjection.lean` proves KT.07 (the spectral gap at the
printed rate `κ²/(2|S|)`), KT.08 (the projection `P`, with `ran P = Fix`) and
KT.09 (`Fix ⊆ V·Fix`, read as `P ≤ Q`) in an abstract unital C-star algebra
carrying a unitary representation of the ambient group.  Here that abstract
algebra is instantiated at `B_ω` and that representation at
`π g = [Ad U_n g]_ω`.

The Kazhdan data `S`, `kappa` is not a hypothesis about the transport theorem:
it is what property `(T)` supplies through
`KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair`, which
is exactly the manuscript's sentence "Property (T) provides a finite symmetric
generating set `S ⊆ Γ` with `1 ∈ S` and a Kazhdan constant `κ`".  It is passed
in rather than chosen here so that the ambient constructor below can obtain it
once and reuse it. -/
def compressionRep {Γ : Type} {H : Type*} [Group Γ] [Group H]
    (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)
    (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (Y n) (Y n) ℂ) -
        (U n g : Matrix (Y n) (Y n) ℂ) * (U n h : Matrix (Y n) (Y n) ℂ)‖ ≤ ε)
    (S : Finset Γ) (kappa : ℝ) (hpair : IsKazhdanPair.{0, 0} Γ S kappa)
    (hone : (1 : Γ) ∈ S) (hsymm : ∀ γ ∈ S, γ⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤) :
    KazhdanCompressionRep Γ H (AdjointCorona Y) where
  pi := piUnitary Y U hU
  iota := iota
  s := s
  Q := S
  kappa := kappa
  kazhdan := hpair
  S := S
  QS := Finset.Subset.refl S
  one_mem := hone
  symm := hsymm
  generates := hgen
  compresses := hs

/-! ## The ambient of KT.01--KT.09, constructed -/

/-- **The manuscript's ultraproduct ambient exists.**

Every field of `UltraproductAdjointModel` is discharged by a construction, not
by a hypothesis:

* `Alg`, `ring`, `starRing` are the norm corona `B_ω` of
  `Analysis/NormMatrixCorona.lean` on the doubled index (KT.03);
* `dedekindFinite` is `normMatrixCStarCorona_isDedekindFiniteMonoid` (KT.06);
* `Vec`, `act`, `act_mul` are the vector ultraproduct `K_ω` and the `ℂ`-linear
  action of `B_ω` on it (KT.02, KT.03);
* `cls`, `cls_eq_iff` are the class map and the class-equality criterion, moved
  from the weighted predicates to `hsNormSq` by the dimension-weight dictionary
  (KT.02, KT.04);
* `pi`, `pi_star`, `act_pi_cls` are `π g = [Ad U_n g]_ω`, whose multiplicativity
  is exactness in the quotient of the asymptotic multiplicativity of `U_n`
  (KT.01, KT.05);
* `P`, `P_star`, `P_mul_P`, `rep_mul_P`, `act_P_cls_of_fixed` are the Kazhdan
  projection and both halves of `ran P = Fix` (KT.07, KT.08), the second half
  through the resolvent factorisation `1 - P = cfc (gapResolvent c) h · (1 - h)`,
  which is where the spectral gap `sp(h) ⊆ [-1, 1 - κ²/(2|S|)] ∪ {1}` is
  consumed;
* `P_mul_conjugate`, `conjugate_mul_P` are `Fix ⊆ V·Fix` read as `P ≤ Q`
  (KT.09).

The hypotheses are exactly those of the Kazhdan transport result -- property `(T)`,
the compression, positive dimensions, operator-norm asymptotic multiplicativity
-- together with the free ultrafilter the printed proof fixes.  `hω` is the
freeness the printed proof asks for; it is what lets the cofinite corona act on
the `ω`-ultraproduct. -/
theorem nonempty_ultraproductAdjointModel
    {Γ : Type} {H : Type*} [Group Γ] [Group H]
    (hT : HasKazhdanPropertyT.{0, 0} Γ)
    (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ) -
        (U n g : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ) * U n h‖ ≤ ε)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    Nonempty (UltraproductAdjointModel iota s d U ω) := by
  classical
  haveI : ∀ n, Nonempty (natModels d n) := nonempty_natModels hd
  have hcard : ∀ n, 0 < Fintype.card (natModels d n) := card_natModels_pos hd
  have hwnn : ∀ n, 0 ≤ dimWeight (natModels d) n := dimWeight_nonneg (natModels d)
  -- the Kazhdan data the manuscript's paragraph *The Kazhdan projection* fixes
  obtain ⟨S, kappa, hone, hsymm, hgen, _hkpos, _hkone, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  let D : KazhdanCompressionRep Γ H (AdjointCorona (natModels d)) :=
    compressionRep (natModels d) iota s hs U hU S kappa hpair hone hsymm hgen
  -- the action laws of `B_ω` on `K_ω`, in the unbundled form KT.08 consumes
  have hact_mul : ∀ (a b : AdjointCorona (natModels d))
      (ζ : Vec (natModels d) (dimWeight (natModels d)) ω),
      act (natModels d) (dimWeight (natModels d)) ω (a * b) ζ =
        act (natModels d) (dimWeight (natModels d)) ω a
          (act (natModels d) (dimWeight (natModels d)) ω b ζ) := by
    intro a b ζ
    simp only [act_mul (natModels d) (dimWeight (natModels d)) ω hwnn hω,
      LinearMap.comp_apply]
  have hact_one : ∀ ζ : Vec (natModels d) (dimWeight (natModels d)) ω,
      act (natModels d) (dimWeight (natModels d)) ω 1 ζ = ζ := by
    intro ζ
    simp only [act_one (natModels d) (dimWeight (natModels d)) ω hwnn hω,
      LinearMap.id_apply]
  have hact_sub : ∀ (a b : AdjointCorona (natModels d))
      (ζ : Vec (natModels d) (dimWeight (natModels d)) ω),
      act (natModels d) (dimWeight (natModels d)) ω (a - b) ζ =
        act (natModels d) (dimWeight (natModels d)) ω a ζ -
          act (natModels d) (dimWeight (natModels d)) ω b ζ := by
    intro a b ζ
    simp only [act_sub (natModels d) (dimWeight (natModels d)) ω hwnn hω,
      LinearMap.sub_apply]
  have hact_zero : ∀ a : AdjointCorona (natModels d),
      act (natModels d) (dimWeight (natModels d)) ω a
        (0 : Vec (natModels d) (dimWeight (natModels d)) ω) = 0 := fun a ↦
    map_zero (act (natModels d) (dimWeight (natModels d)) ω a)
  have hact_smul : ∀ (c : ℂ) (a : AdjointCorona (natModels d))
      (ζ : Vec (natModels d) (dimWeight (natModels d)) ω),
      act (natModels d) (dimWeight (natModels d)) ω (c • a) ζ =
        c • act (natModels d) (dimWeight (natModels d)) ω a ζ := by
    intro c a ζ
    simp only [act_smul (natModels d) (dimWeight (natModels d)) ω hwnn hω,
      LinearMap.smul_apply]
  have hact_sum : ∀ (t : Finset Γ) (f : Γ → AdjointCorona (natModels d))
      (ζ : Vec (natModels d) (dimWeight (natModels d)) ω),
      act (natModels d) (dimWeight (natModels d)) ω (∑ γ ∈ t, f γ) ζ =
        ∑ γ ∈ t, act (natModels d) (dimWeight (natModels d)) ω (f γ) ζ :=
    fun t f ζ ↦
      act_finset_sum (natModels d) (dimWeight (natModels d)) ω hwnn hω t f ζ
  refine ⟨{
    Alg := AdjointCorona (natModels d)
    ring := inferInstance
    starRing := inferInstance
    dedekindFinite := inferInstance
    Vec := Vec (natModels d) (dimWeight (natModels d)) ω
    act := fun a ζ ↦ act (natModels d) (dimWeight (natModels d)) ω a ζ
    act_mul := hact_mul
    cls := cls (natModels d) (dimWeight (natModels d)) ω
    cls_eq_iff := ?_
    pi := piHom (natModels d) U hU
    pi_star := piHom_star (natModels d) U hU
    act_pi_cls := ?_
    P := D.proj
    P_star := D.kt_08_isSelfAdjoint_proj.star_eq
    P_mul_P := D.kt_08_proj_mul_proj
    rep_mul_P := ?_
    act_P_cls_of_fixed := ?_
    P_mul_conjugate := D.kt_09_proj_mul_conjugate
    conjugate_mul_P := D.kt_09_conjugate_mul_proj }⟩
  -- KT.02 and KT.04: the class-equality criterion, at the dimension weight
  · intro C ξ η hξ hη
    rw [cls_eq_iff_weightNull (natModels d) (dimWeight (natModels d)) ω hwnn C
      ξ η ((weightBounded_dimWeight_iff hcard C ξ).mpr hξ)
      ((weightBounded_dimWeight_iff hcard C η).mpr hη)]
    exact weightNull_dimWeight_iff_tendsto hcard (ω : Filter ℕ)
      (fun n ↦ ξ n - η n)
  -- KT.01 and KT.03: `π g` acts by the ultraproduct of the adjoint actions
  · intro g _C ξ _hξ
    exact act_pi_cls (natModels d) (dimWeight (natModels d)) ω U hU hwnn hω g ξ
  -- KT.08, `ran P ⊆ Fix`, algebraically
  · intro γ
    exact D.kt_08_rep_mul_proj γ
  -- KT.07 and KT.08, `Fix ⊆ ran P`, on classes of bounded families
  · intro _C ξ _hξ hfix
    exact D.kt_08_act_proj_of_fixed
      (fun a ζ ↦ act (natModels d) (dimWeight (natModels d)) ω a ζ)
      hact_mul hact_one hact_sub hact_zero hact_smul hact_sum
      (fun γ ↦ hfix γ)

/-- **The ambient of manuscript steps KT.01--KT.09, as a term.**

This is the constructor whose absence made the printed proof of
the Kazhdan transport result conditional.  With it,
`ultraproductKazhdanTransport` and `manuscriptKazhdanTransport_ultraproduct`
become unconditional, and the manuscript's printed proof -- the adjoint model,
the ultraproduct, the Kazhdan projection, one-sided compression and finiteness
-- is the proof the theorem's `\leanverified` badge certifies. -/
def ultraproductAdjointModel
    {Γ : Type} {H : Type*} [Group Γ] [Group H]
    (hT : HasKazhdanPropertyT.{0, 0} Γ)
    (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ) -
        (U n g : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ) * U n h‖ ≤ ε)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    UltraproductAdjointModel iota s d U ω :=
  Classical.choice
    (nonempty_ultraproductAdjointModel hT iota s hs d hd U hU ω hω)

end

end UltraproductModelConstruction
end GroupApproximation
