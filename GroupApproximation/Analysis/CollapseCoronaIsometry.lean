import GroupApproximation.Analysis.OmegaConjugationOperators
import GroupApproximation.Analysis.VectorOmegaAction
import GroupApproximation.Sofic.KOmegaHilbert

/-!
# A unitary of `B_ω` acts on `K_ω` by an isometry

Proof-ledger row `CO.21b`.  `Analysis/CollapseTransportEndpoint` discharged
`htransport` for the coboundary form of the collapse endpoint, and recorded
what the Delorme form still needs: that form proves the coboundary from
property (T) instead of taking it, and Delorme–Guichardet consumes `π` as a
homomorphism into the **isometries** of `K_ω`, not merely into its linear
automorphisms.  The multiplicativity was already available — `omegaRep` is
`D.pi` read inside `B_ω` — so the single missing fact was

  `‖omegaAct u ζ‖ = ‖ζ‖`  for `u` unitary in `B_ω`.

This file proves it.

## Why no lifting lemma is needed

The obvious route is to lift `u` to a coordinatewise unitary sequence and
compute, which is `lem:unitarycorona` and is available only at the cofinite
filter.  It is not needed.  `OmegaOperatorUltraproduct.norm_omegaMk` gives the
norm of `B_ω` as the **ultralimit** `lim_ω ‖A_n‖` of the coordinate norms of
any representative, not as an infimum over representatives, so the coordinate
estimate `‖A_n ξ_n‖_F ≤ ‖A_n‖ ‖ξ_n‖_F` passes to the quotient with the sharp
constant — no truncation and no `ε` of room:

* `norm_actKOmega_le` is that estimate, with the bound the corona norm itself;
* `norm_actKOmega_of_unitary` is then a two-sided squeeze: `‖u‖ = 1` bounds
  one way, and applying the bound to `u*` at the vector `π(u) ζ` bounds the
  other, because `u* u = 1`.

`‖u‖ = 1` itself is the C*-identity together with `‖1‖ = 1` in `B_ω`, and that
last fact is proved here rather than assumed: the constant sequence `1`
represents `1`, its coordinate norms are all `1` because the doubled index is
nonempty, and the ultralimit of a constant is that constant.  So no
`Nontrivial` instance has to be supplied by a consumer.

`ulim_mul` is the one ultralimit fact `Sofic/UltrafilterLimit` lacks — it has
the sum, the negation and the constant multiple, and
`Analysis/VectorOmegaAction` added monotonicity for the same reason.

The action is retyped as `actKOmega`, an endomorphism of `KOmega` rather than
of its underlying quotient, for the reason `OmegaIsometryRepresentation.actK`
is: the norm is carried by the opaque synonym, so a statement about `‖·‖` has
to be made there.
-/

namespace GroupApproximation
namespace CollapseCoronaIsometry

open Filter Matrix Topology
open UltrafilterLimit UltraproductModelConstruction ScaledKazhdanTransport
open OmegaOperatorUltraproduct OmegaConjugationOperators
open HilbertUltraproductInner KOmegaHilbert
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (w : ℕ → ℝ)
  (ω : Ultrafilter ℕ)

/-! ## Ultralimits are multiplicative -/

/-- Ultralimits multiply on convergent sequences.  `Sofic/UltrafilterLimit`
has the sum, the negation and the constant multiple, but not this. -/
theorem ulim_mul {f g : ℕ → ℝ}
    (hf : ∃ L : ℝ, Tendsto f (ω : Filter ℕ) (𝓝 L))
    (hg : ∃ L : ℝ, Tendsto g (ω : Filter ℕ) (𝓝 L)) :
    ulim ω (fun n ↦ f n * g n) = ulim ω f * ulim ω g := by
  obtain ⟨Lf, hLf⟩ := hf
  obtain ⟨Lg, hLg⟩ := hg
  rw [ulim_eq hLf, ulim_eq hLg]
  exact ulim_eq (hLf.mul hLg)

omit [∀ n, Nonempty (Y n)] in
/-- The coordinate norms of a bounded sequence converge along `ω`. -/
theorem exists_tendsto_coord_norm (a : BoundedMatrixSequence (DblIdx Y)) :
    ∃ L : ℝ, Tendsto
      (fun n ↦ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖)
      (ω : Filter ℕ) (𝓝 L) :=
  exists_tendsto_of_bounded (C := ‖a‖) ω fun n ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact boundedMatrixSequence_coord_norm_le (DblIdx Y) a n

/-! ## The action, typed on `K_ω` -/

/-- The action of `B_ω` on `K_ω`, typed as an endomorphism of `KOmega` rather
than of its underlying quotient, so that its norm can be spoken of. -/
def actKOmega (hw : ∀ n, 0 ≤ w n) (u : OmegaAdjointCorona Y ω) :
    KOmega Y w ω hw →ₗ[ℂ] KOmega Y w ω hw :=
  omegaAct Y w ω hw u

/-! ## The action is bounded by the corona norm -/

/-- **The action of a class of `B_ω` is bounded by its norm.**

The constant is the corona norm on the nose, not the `ℓ∞` norm of a
representative: along an ultrafilter the corona norm *is* the ultralimit of
the coordinate norms, so the coordinate estimate pushes through the ultralimit
with no loss. -/
theorem norm_actKOmega_le (hw : ∀ n, 0 ≤ w n) (u : OmegaAdjointCorona Y ω)
    (x : KOmega Y w ω hw) :
    ‖actKOmega Y w ω hw u x‖ ≤ ‖u‖ * ‖x‖ := by
  obtain ⟨a, rfl⟩ := omegaMk_surjective Y ω u
  obtain ⟨ξ, hξ⟩ : ∃ ξ : massBounded Y w, mkK Y w ω hw ξ = x :=
    Submodule.Quotient.mk_surjective (nullIn Y w ω) (show Vec Y w ω from x)
  subst hξ
  have hval : actKOmega Y w ω hw (omegaMk Y ω a) (mkK Y w ω hw ξ)
      = mkK Y w ω hw (actSub Y w a ξ) := rfl
  rw [hval, norm_mkK, norm_mkK, norm_omegaMk]
  have hexn := exists_tendsto_coord_norm Y ω a
  have hex1 := exists_tendsto_mass (Y := Y) (w := w) (ω := ω) hw
    (actSub Y w a ξ)
  have hex2 := exists_tendsto_mass (Y := Y) (w := w) (ω := ω) hw ξ
  have hexN : ∃ L : ℝ, Tendsto
      (fun n ↦ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ *
        ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖)
      (ω : Filter ℕ) (𝓝 L) := by
    obtain ⟨L, hL⟩ := hexn
    exact ⟨L * L, hL.mul hL⟩
  have hexprod : ∃ L : ℝ, Tendsto
      (fun n ↦ (‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ *
          ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖) *
        (matMass ((ξ : MatFam Y) n) / w n)) (ω : Filter ℕ) (𝓝 L) := by
    obtain ⟨LN, hLN⟩ := hexN
    obtain ⟨L2, hL2⟩ := hex2
    exact ⟨LN * L2, hLN.mul hL2⟩
  have hpt : ∀ n, matMass (((actSub Y w a ξ : massBounded Y w) : MatFam Y) n)
        / w n
      ≤ (‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ *
          ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖) *
        (matMass ((ξ : MatFam Y) n) / w n) := by
    intro n
    have hbase : matMass (applyFam Y a (ξ : MatFam Y) n)
        ≤ (‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ *
            ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖) *
          matMass ((ξ : MatFam Y) n) := by
      have h := matMass_applyFam_le Y a (ξ : MatFam Y) n
      rwa [sq] at h
    show matMass (applyFam Y a (ξ : MatFam Y) n) / w n ≤ _
    rcases (hw n).lt_or_eq with hpos | hzero
    · rw [mul_div_assoc']
      gcongr
    · rw [← hzero]
      simp
  have hmono := VectorOmegaAction.ulim_mono ω hex1 hexprod hpt
  rw [ulim_mul ω hexN hex2, ulim_mul ω hexn hexn] at hmono
  have hnn : 0 ≤ ulim ω
      (fun n ↦ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖) :=
    ulim_nonneg hexn fun n ↦ norm_nonneg _
  calc Real.sqrt (ulim ω (fun n ↦
        matMass (((actSub Y w a ξ : massBounded Y w) : MatFam Y) n) / w n))
      ≤ Real.sqrt ((ulim ω
          (fun n ↦ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖) *
          ulim ω
          (fun n ↦ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖)) *
          ulim ω (fun n ↦ matMass ((ξ : MatFam Y) n) / w n)) :=
        Real.sqrt_le_sqrt hmono
    _ = ulim ω (fun n ↦ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖) *
          Real.sqrt (ulim ω
            (fun n ↦ matMass ((ξ : MatFam Y) n) / w n)) := by
        rw [Real.sqrt_mul (by positivity), ← sq, Real.sqrt_sq hnn]

/-! ## `‖1‖ = 1`, and the isometry -/

/-- `B_ω` is unital with `‖1‖ = 1`: the constant sequence `1` represents `1`,
its coordinate norms are all `1` because the doubled index is nonempty, and
the ultralimit of a constant is that constant.  Proving it here means no
consumer has to supply a `Nontrivial` instance for the corona. -/
theorem norm_one_omegaAdjointCorona :
    ‖(1 : OmegaAdjointCorona Y ω)‖ = 1 := by
  have h1 : (1 : OmegaAdjointCorona Y ω) = omegaMk Y ω 1 :=
    (map_one (omegaMk Y ω)).symm
  rw [h1, norm_omegaMk]
  have hfun : (fun n ↦ ‖((1 : BoundedMatrixSequence (DblIdx Y)) :
        ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖)
      = fun _ : ℕ ↦ (1 : ℝ) := by
    funext n
    show ‖(1 : Matrix (DblIdx Y n) (DblIdx Y n) ℂ)‖ = 1
    exact norm_one
  rw [hfun, ulim_const]

/-- A unitary of `B_ω` has norm one, by the C*-identity and `‖1‖ = 1`. -/
theorem norm_of_mem_unitary {u : OmegaAdjointCorona Y ω}
    (hu : u ∈ unitary (OmegaAdjointCorona Y ω)) : ‖u‖ = 1 := by
  have hsq : ‖u‖ * ‖u‖ = 1 := by
    have hcstar : ‖star u * u‖ = ‖u‖ * ‖u‖ := CStarRing.norm_star_mul_self
    rw [hu.1, norm_one_omegaAdjointCorona] at hcstar
    exact hcstar.symm
  have hfac : (‖u‖ - 1) * (‖u‖ + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith [norm_nonneg u]

/-- **A unitary of `B_ω` acts on `K_ω` by an isometry.**

This is what the Delorme form of the collapse endpoint needs of `π`, and it
was the last analytic gap in the printed route of `CO.21b`.  The squeeze is
two-sided: `‖u‖ = 1` gives one inequality, and applying the same bound to `u*`
at the vector `π(u) ζ` gives the other, because `u* u = 1`. -/
theorem norm_actKOmega_of_unitary (hw : ∀ n, 0 ≤ w n)
    {u : OmegaAdjointCorona Y ω}
    (hu : u ∈ unitary (OmegaAdjointCorona Y ω)) (x : KOmega Y w ω hw) :
    ‖actKOmega Y w ω hw u x‖ = ‖x‖ := by
  have hnorm : ‖u‖ = 1 := norm_of_mem_unitary Y ω hu
  have hstar : ‖star u‖ = 1 := by
    rw [norm_star]
    exact hnorm
  have hle : ‖actKOmega Y w ω hw u x‖ ≤ ‖x‖ := by
    have h := norm_actKOmega_le Y w ω hw u x
    rwa [hnorm, one_mul] at h
  have hid : actKOmega Y w ω hw (star u) (actKOmega Y w ω hw u x) = x := by
    show omegaAct Y w ω hw (star u) (omegaAct Y w ω hw u x) = x
    rw [← omegaAct_mul, hu.1, omegaAct_one]
  have hge : ‖x‖ ≤ ‖actKOmega Y w ω hw u x‖ := by
    have h := norm_actKOmega_le Y w ω hw (star u) (actKOmega Y w ω hw u x)
    rwa [hid, hstar, one_mul] at h
  exact le_antisymm hle hge

end

end CollapseCoronaIsometry
end GroupApproximation
