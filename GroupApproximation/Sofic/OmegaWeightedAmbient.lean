import GroupApproximation.Sofic.OmegaKazhdanCompression
import GroupApproximation.Sofic.WeightedUltraproductModelConstruction

/-!
# The weighted ultraproduct ambient over `B_ω`

`Sofic/WeightedUltraproductModelConstruction.lean` constructs the manuscript's
KT.01--KT.09 ambient, `WeightedUltraproductAdjointModel`, with its algebra field
`Alg` realized as the **cofinite** corona, and its own docstring records that as
the deviation: the printed algebra is `B_ω = ∏_ω B(K_n)`.

The interface is abstract in `Alg` --- it asks for a ring with star, Dedekind
finiteness, an action on `K_ω`, a unitary representation, and a Kazhdan
projection --- so this file supplies it with `Alg := B_ω` instead.  Everything
that made that hard is now present: `B_ω` itself, its Dedekind finiteness, the
representation `[Ad U_n(·)]_ω`, and the Kazhdan bundle over it.

## What this closes

`transport_variants_one`, `scaled_transport_both_of_ambient` and
`dimension_weight_recovers_kazhdan_transport` all take the ambient as a
hypothesis, for every free ultrafilter.  With `omegaWeightedAmbient` they can be
instantiated along the printed algebra, so the printed proof of
`thm:kazhdan-transport` is walkable and not merely assembled.

## What is genuinely reused

The action on `K_ω` is the *same* `actQ` in both routes: the cofinite corona and
`B_ω` differ in which sequences they identify, not in how a sequence acts.  So
every coordinate computation --- `applyFam_piSeq`, `applyFam_star_piSeq`,
`kt_01_matMass_adjoint` --- is shared verbatim, and the only new content is the
quotient bookkeeping and the fact that `omegaAct` needs `0 ≤ w` but *not*
`ω ≤ cofinite`, the cofinite route having needed the latter precisely to see
that a `c₀`-null sequence is `ω`-null.
-/

namespace GroupApproximation
namespace OmegaWeightedAmbient

open Filter Matrix Topology
open ScaledKazhdanTransport UltraproductScaledTransport
open UltraproductModelConstruction OmegaOperatorUltraproduct
open UltraproductKazhdanProjection KazhdanProjection
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

variable {H : Type u} [Group H]
  (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (hY : ∀ n, 0 < Fintype.card (Y n))
  (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)

/-! ## Repackaging the printed data as an almost representation -/

/-- The printed data `(Y, U)` viewed as an almost representation, so that the
`B_ω` constructions apply to it. -/
def rep (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (Y n) (Y n) ℂ) -
        (U n g : Matrix (Y n) (Y n) ℂ) * (U n h : Matrix (Y n) (Y n) ℂ)‖ ≤ ε) :
    OpAlmostRepresentation H where
  model := Y
  modelNonempty := hY
  map := U
  asymptoticallyMultiplicative := hU

variable (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
  ‖(U n (g * h) : Matrix (Y n) (Y n) ℂ) -
    (U n g : Matrix (Y n) (Y n) ℂ) * (U n h : Matrix (Y n) (Y n) ℂ)‖ ≤ ε)

/-- The adjoint sequence of the repackaged data is the representation sequence
the cofinite route already uses.  This is what makes every coordinate
computation shared rather than repeated. -/
theorem adSeq_eq_piSeq (g : H) :
    OmegaAlmostRepresentation.adSeq (rep Y hY U hU) g = piSeq Y U g :=
  Subtype.ext rfl

variable (w : ℕ → ℝ) (ω : Ultrafilter ℕ)

/-! ## `π` at `ω`, in the algebra -/

/-- `π(g) = [Ad U_n(g)]_ω`, read inside `B_ω` rather than in its unitary
group. -/
def piOmegaAlg (hω : (ω : Filter ℕ) ≤ cofinite) : H →* OmegaAdjointCorona Y ω :=
  (unitary (OmegaAdjointCorona Y ω)).subtype.comp
    (OmegaAlmostRepresentation.piHom (rep Y hY U hU) ω hω)

theorem piOmegaAlg_eq_mk (hω : (ω : Filter ℕ) ≤ cofinite) (g : H) :
    piOmegaAlg Y hY U hU ω hω g = omegaMk Y ω (piSeq Y U g) := by
  show OmegaAlmostRepresentation.piOmega (rep Y hY U hU) ω g = _
  rw [OmegaAlmostRepresentation.piOmega_def]
  exact congrArg (omegaMk Y ω) (adSeq_eq_piSeq Y hY U hU g)

theorem piOmegaAlg_star (hω : (ω : Filter ℕ) ≤ cofinite) (g : H) :
    star (piOmegaAlg Y hY U hU ω hω g) = piOmegaAlg Y hY U hU ω hω g⁻¹ :=
  AbstractSpectralGap.star_unitary_coe
    (OmegaAlmostRepresentation.piHom (rep Y hY U hU) ω hω) g

theorem star_piOmegaAlg_eq_mk (hω : (ω : Filter ℕ) ≤ cofinite) (g : H) :
    star (piOmegaAlg Y hY U hU ω hω g)
      = omegaMk Y ω (star (piSeq Y U g)) := by
  rw [piOmegaAlg_eq_mk, OmegaAlmostRepresentation.omegaMk_star]

/-! ## The action laws, unbundled -/

variable (hw : ∀ n, 0 ≤ w n)

theorem omegaMk_algebraMap (c : ℂ) :
    omegaMk Y ω (algebraMap ℂ (BoundedMatrixSequence (DblIdx Y)) c)
      = algebraMap ℂ (OmegaAdjointCorona Y ω) c := by
  unfold omegaMk OmegaAdjointCorona
  exact Ideal.Quotient.mk_algebraMap ℂ
    (nullMatrixSequenceIdeal (DblIdx Y) (ω : Filter ℕ)) c

theorem omegaMk_smul (c : ℂ) (a : BoundedMatrixSequence (DblIdx Y)) :
    omegaMk Y ω (c • a) = c • omegaMk Y ω a := by
  rw [Algebra.smul_def, map_mul, omegaMk_algebraMap, Algebra.smul_def]

theorem omegaAct_mul (a b : OmegaAdjointCorona Y ω) (ζ : Vec Y w ω) :
    omegaAct Y w ω hw (a * b) ζ = omegaAct Y w ω hw a (omegaAct Y w ω hw b ζ) := by
  rw [map_mul]
  rfl

theorem omegaAct_one_apply (ζ : Vec Y w ω) : omegaAct Y w ω hw 1 ζ = ζ := by
  rw [map_one]
  rfl

theorem omegaAct_sub (a b : OmegaAdjointCorona Y ω) (ζ : Vec Y w ω) :
    omegaAct Y w ω hw (a - b) ζ
      = omegaAct Y w ω hw a ζ - omegaAct Y w ω hw b ζ := by
  rw [map_sub]
  rfl

theorem omegaAct_zero (a : OmegaAdjointCorona Y ω) :
    omegaAct Y w ω hw a (0 : Vec Y w ω) = 0 :=
  map_zero (omegaAct Y w ω hw a)

theorem omegaAct_smul (c : ℂ) (a : OmegaAdjointCorona Y ω) (ζ : Vec Y w ω) :
    omegaAct Y w ω hw (c • a) ζ = c • omegaAct Y w ω hw a ζ := by
  obtain ⟨a', rfl⟩ := omegaMk_surjective Y ω a
  rw [← omegaMk_smul Y ω c a', omegaAct_omegaMk, omegaAct_omegaMk,
    actQ_smul Y w ω c a']
  rfl

theorem omegaAct_finset_sum {ι : Type*} (t : Finset ι)
    (f : ι → OmegaAdjointCorona Y ω) (ζ : Vec Y w ω) :
    omegaAct Y w ω hw (∑ i ∈ t, f i) ζ = ∑ i ∈ t, omegaAct Y w ω hw (f i) ζ := by
  rw [map_sum]
  exact LinearMap.sum_apply t (fun i ↦ omegaAct Y w ω hw (f i)) ζ

/-! ## The representation on classes -/

theorem omegaAct_pi_cls (hω : (ω : Filter ℕ) ≤ cofinite) (g : H) (ξ : MatFam Y) :
    omegaAct Y w ω hw (piOmegaAlg Y hY U hU ω hω g) (cls Y w ω ξ) =
      cls Y w ω (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)ᴴ) := by
  have hmass : ∀ n, matMass ((U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
      (U n g : Matrix (Y n) (Y n) ℂ)ᴴ) = matMass (ξ n) :=
    fun n ↦ kt_01_matMass_adjoint (U n g).2 (ξ n)
  rw [piOmegaAlg_eq_mk, omegaAct_omegaMk]
  by_cases hb : ξ ∈ massBounded Y w
  · obtain ⟨C, hC⟩ := hb
    have hb' : ξ ∈ massBounded Y w := ⟨C, hC⟩
    have hcb : (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)ᴴ) ∈ massBounded Y w :=
      ⟨C, fun n ↦ by rw [hmass n]; exact hC n⟩
    rw [cls_of_mem Y w ω hb', actQ_mk, cls_of_mem Y w ω hcb]
    exact congrArg Submodule.Quotient.mk
      (Subtype.ext (applyFam_piSeq Y U g ξ))
  · have hcb : (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)ᴴ) ∉ massBounded Y w := by
      rintro ⟨C, hC⟩
      exact hb ⟨C, fun n ↦ by rw [← hmass n]; exact hC n⟩
    rw [cls_of_not_mem Y w ω hb, cls_of_not_mem Y w ω hcb, map_zero]

theorem omegaAct_star_pi_cls (hω : (ω : Filter ℕ) ≤ cofinite) (g : H)
    (ξ : MatFam Y) :
    omegaAct Y w ω hw (star (piOmegaAlg Y hY U hU ω hω g)) (cls Y w ω ξ) =
      cls Y w ω (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ)ᴴ * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)) := by
  have hmass : ∀ n, matMass ((U n g : Matrix (Y n) (Y n) ℂ)ᴴ * ξ n *
      (U n g : Matrix (Y n) (Y n) ℂ)) = matMass (ξ n) :=
    fun n ↦ kt_01_matMass_coadjoint (U n g).2 (ξ n)
  rw [star_piOmegaAlg_eq_mk, omegaAct_omegaMk]
  by_cases hb : ξ ∈ massBounded Y w
  · obtain ⟨C, hC⟩ := hb
    have hb' : ξ ∈ massBounded Y w := ⟨C, hC⟩
    have hcb : (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ)ᴴ * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)) ∈ massBounded Y w :=
      ⟨C, fun n ↦ by rw [hmass n]; exact hC n⟩
    rw [cls_of_mem Y w ω hb', actQ_mk, cls_of_mem Y w ω hcb]
    exact congrArg Submodule.Quotient.mk
      (Subtype.ext (applyFam_star_piSeq Y U g ξ))
  · have hcb : (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ)ᴴ * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)) ∉ massBounded Y w := by
      rintro ⟨C, hC⟩
      exact hb ⟨C, fun n ↦ by rw [← hmass n]; exact hC n⟩
    rw [cls_of_not_mem Y w ω hb, cls_of_not_mem Y w ω hcb, map_zero]

/-! ## The ambient, assembled over `B_ω` -/

variable (hw : ∀ n, 0 ≤ w n)

include hY hU hw in
/-- **The manuscript's KT.01--KT.09 ambient, over the manuscript's algebra.**

Every field is discharged exactly as in the cofinite construction, with three
differences and no new hypotheses:

* `Alg` is `B_ω`, and `dedekindFinite` is
  `OmegaCoronaFinite.omegaAdjointCorona_isDedekindFiniteMonoid` rather than the
  cofinite instance;
* the action is `omegaAct`, which needs `0 ≤ w` but not `ω ≤ cofinite` -- the
  cofinite route needed the latter only to see that a `c₀`-null sequence is
  `ω`-null, which is vacuous once the corona is indexed by `ω`;
* `pi` is `[Ad U_n(·)]_ω` in `B_ω`.

`ω ≤ cofinite` is still a hypothesis, because it is what makes `π`
multiplicative: the almost representation's defect vanishes along `atTop`. -/
theorem nonempty_omegaWeightedAmbient {Γ : Type} [Group Γ]
    (hT : HasKazhdanPropertyT.{0, 0} Γ)
    (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (hω : (ω : Filter ℕ) ≤ cofinite) :
    Nonempty (WeightedUltraproductAdjointModel iota s Y U w ω) := by
  classical
  obtain ⟨S, kappa, hone, hsymm, hgen, _hkpos, _hkone, hpair⟩ :=
    HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  let D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω) :=
    OmegaKazhdanCompression.omegaCompressionRep ω (rep Y hY U hU) hω iota s
      S kappa hpair S (Finset.Subset.refl S) hone hsymm hgen hs
  have hrep : ∀ γ : Γ,
      piOmegaAlg Y hY U hU ω hω (iota γ) * D.proj = D.proj :=
    fun γ ↦ D.kt_08_rep_mul_proj γ
  refine ⟨{
    Alg := OmegaAdjointCorona Y ω
    ring := inferInstance
    starRing := inferInstance
    dedekindFinite := inferInstance
    Vec := Vec Y w ω
    act := fun a ζ ↦ omegaAct Y w ω hw a ζ
    act_mul := omegaAct_mul Y w ω hw
    cls := cls Y w ω
    cls_eq_iff := fun C ξ η hξ hη ↦ cls_eq_iff_weightNull Y w ω hw C ξ η hξ hη
    pi := piOmegaAlg Y hY U hU ω hω
    pi_star := piOmegaAlg_star Y hY U hU ω hω
    act_pi_cls := fun g ξ ↦ omegaAct_pi_cls Y hY U hU w ω hw hω g ξ
    act_star_pi_cls := fun _C g ξ _hξ ↦
      omegaAct_star_pi_cls Y hY U hU w ω hw hω g ξ
    P := D.proj
    P_star := D.kt_08_isSelfAdjoint_proj.star_eq
    P_mul_P := D.kt_08_proj_mul_proj
    act_P_iff := ?_
    P_mul_conjugate := D.kt_09_proj_mul_conjugate
    conjugate_mul_P := D.kt_09_conjugate_mul_proj }⟩
  intro ζ
  constructor
  · intro hζ γ
    have hζ' : omegaAct Y w ω hw D.proj ζ = ζ := hζ
    show omegaAct Y w ω hw (piOmegaAlg Y hY U hU ω hω (iota γ)) ζ = ζ
    calc omegaAct Y w ω hw (piOmegaAlg Y hY U hU ω hω (iota γ)) ζ
        = omegaAct Y w ω hw (piOmegaAlg Y hY U hU ω hω (iota γ))
            (omegaAct Y w ω hw D.proj ζ) := by rw [hζ']
      _ = omegaAct Y w ω hw
            (piOmegaAlg Y hY U hU ω hω (iota γ) * D.proj) ζ :=
          (omegaAct_mul Y w ω hw _ _ _).symm
      _ = omegaAct Y w ω hw D.proj ζ := by rw [hrep γ]
      _ = ζ := hζ'
  · intro hfix
    exact D.kt_08_act_proj_of_fixed (fun a ζ ↦ omegaAct Y w ω hw a ζ)
      (omegaAct_mul Y w ω hw) (omegaAct_one_apply Y w ω hw)
      (omegaAct_sub Y w ω hw) (omegaAct_zero Y w ω hw)
      (omegaAct_smul Y w ω hw) (omegaAct_finset_sum Y w ω hw)
      (fun γ ↦ hfix γ)

include hY hU hw in
/-- The ambient over `B_ω` as a term. -/
def omegaWeightedAmbient {Γ : Type} [Group Γ]
    (hT : HasKazhdanPropertyT.{0, 0} Γ)
    (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (hω : (ω : Filter ℕ) ≤ cofinite) :
    WeightedUltraproductAdjointModel iota s Y U w ω :=
  Classical.choice
    (nonempty_omegaWeightedAmbient Y hY U hU w ω hw hT iota s hs hω)

end

/-! ## KT.00 along the printed route -/

section Endpoint

variable {H : Type u} [Group H]
  (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (hY : ∀ n, 0 < Fintype.card (Y n))
  (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)
  (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    ‖(U n (g * h) : Matrix (Y n) (Y n) ℂ) -
      (U n g : Matrix (Y n) (Y n) ℂ) * (U n h : Matrix (Y n) (Y n) ℂ)‖ ≤ ε)

include hY hU in
/-- **Theorem 3.1 along the printed route.**  The conclusion of
`thm:kazhdan-transport` -- normalized Hilbert--Schmidt vanishing of the
conjugated commutators -- obtained through the free-ultrafilter ambient, i.e.
through `B_ω = ∏_ω B(K_n)` acting on `K_ω`, rather than through the cofinite
corona.

Every hypothesis is the manuscript's: property `(T)` for the source, the
one-sided compression `s ι(Γ) s⁻¹ ⊆ ι(Γ)`, nonempty coordinate models,
asymptotic multiplicativity, a Hilbert--Schmidt bound on `x`, and asymptotic
commutation with `ι(Γ)`.  The ambient is not assumed: it is
`omegaWeightedAmbient`. -/
theorem omega_route_kazhdan_transport {Γ : Type} [Group Γ]
    (hT : HasKazhdanPropertyT.{0, 0} Γ)
    (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (C : ℝ) (x : ∀ n, Matrix (Y n) (Y n) ℂ)
    (hmass : ∀ n, hsNormSq (Y n) (x n) ≤ C)
    (hcomm : ∀ γ : Γ, Tendsto
      (fun n ↦ hsNormSq (Y n)
        (x n * (U n (iota γ) : Matrix (Y n) (Y n) ℂ) -
          (U n (iota γ) : Matrix (Y n) (Y n) ℂ) * x n))
      atTop (𝓝 0))
    (γ : Γ) :
    Tendsto
      (fun n ↦ hsNormSq (Y n)
        ((U n s : Matrix (Y n) (Y n) ℂ) * x n *
              (U n s : Matrix (Y n) (Y n) ℂ)ᴴ *
            (U n (iota γ) : Matrix (Y n) (Y n) ℂ) -
          (U n (iota γ) : Matrix (Y n) (Y n) ℂ) *
            ((U n s : Matrix (Y n) (Y n) ℂ) * x n *
              (U n s : Matrix (Y n) (Y n) ℂ)ᴴ)))
      atTop (𝓝 0) :=
  dimension_weight_recovers_kazhdan_transport iota s Y hY U C x hmass hcomm
    (fun ω hω ↦ omegaWeightedAmbient Y hY U hU
      (fun n ↦ (Fintype.card (Y n) : ℝ)) ω
      (fun n ↦ Nat.cast_nonneg (Fintype.card (Y n))) hT iota s hs hω)
    γ

end Endpoint

end OmegaWeightedAmbient
end GroupApproximation
