import GroupApproximation.Sofic.UltraproductModelConstructionAssembly

/-!
# The constructor for the weighted ultraproduct ambient

`Sofic/UltraproductScaledTransport.lean` states the printed proof of
the weighted transport theorem of the superseded manuscript revision (the section it lived in, and its label, are no longer printed) in `non_mf_groups_exist.tex` relative to
`WeightedUltraproductAdjointModel`, the ambient of manuscript steps
KT.01--KT.09 written at an arbitrary nonnegative weight `w` rather than at the
dimension weight, and says of that signature that "**no instance exists yet**".

This file constructs one, at every weight and every free ultrafilter at once,
out of exactly the same pieces the unweighted constructor of
`Sofic/UltraproductModelConstructionAssembly.lean` uses.  That the same pieces
suffice is the manuscript's own observation: "the ambient algebra `B_ω`, the
homomorphism `π`, the projection `P` and the absorption identities are literally
weight-independent, because rescaling the inner product of a Hilbert space by a
positive constant leaves the operator norm, hence the algebra `B(K_n)` and its
norm ultraproduct, unchanged".  Only `cls_eq_iff` sees the weight, and
`cls_eq_iff_weightNull` is proved at an arbitrary weight already.

Two fields of the weighted interface have no unweighted counterpart, and both
are discharged here rather than assumed:

* `act_star_pi_cls`, the assertion that `(π g)*` acts by the reverse
  conjugation `ξ ↦ U_n(g)* ξ U_n(g)`, is
  `UltraproductModelConstruction.act_star_pi_cls`, which holds coordinatewise
  and needs no mass bound at all;
* `act_P_iff`, the *equivalence* `ran P = Fix` for an arbitrary vector of
  `K_ω` rather than only for classes of bounded families.  Its two halves are
  `kt_08_rep_mul_proj` moved across the action (which needs nothing analytic)
  and `kt_08_act_proj_of_fixed` (which is where the spectral gap enters,
  through the resolvent factorisation).  Neither half restricts to classes, so
  the equivalence holds for every vector.

The deviation recorded in the module docstring of the unweighted assembly --
`B_ω` realized as the cofinite norm corona rather than the literal `ω`-corona
-- applies verbatim here, for the same reasons and with the same consequences.
-/

namespace GroupApproximation
namespace UltraproductModelConstruction

open Filter Matrix
open ScaledKazhdanTransport UltraproductScaledTransport
open UltraproductKazhdanProjection
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **The weighted ultraproduct ambient exists**, at every nonnegative weight
and every free ultrafilter.

The hypotheses are those of the weighted transport theorem of the superseded manuscript revision (the section it lived in, and its label, are no longer printed) itself: property
`(T)` for `Γ`, the compression `s ι(Γ) s⁻¹ ⊆ ι(Γ)`, nonempty coordinate models,
operator-norm asymptotic multiplicativity of `U`, nonnegativity of the weight,
and freeness of the ultrafilter.  No field of the interface is left as an
assumption. -/
theorem nonempty_weightedUltraproductAdjointModel
    {Γ H : Type} [Group Γ] [Group H]
    (hT : HasKazhdanPropertyT.{0, 0} Γ)
    (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (Y : ℕ → FiniteModel) (hY : ∀ n, 0 < Fintype.card (Y n))
    (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)
    (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (Y n) (Y n) ℂ) -
        (U n g : Matrix (Y n) (Y n) ℂ) * (U n h : Matrix (Y n) (Y n) ℂ)‖ ≤ ε)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    Nonempty (WeightedUltraproductAdjointModel iota s Y U w ω) := by
  classical
  haveI : ∀ n, Nonempty (Y n) := fun n ↦ Fintype.card_pos_iff.mp (hY n)
  obtain ⟨S, kappa, hone, hsymm, hgen, _hkpos, _hkone, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  let D : KazhdanCompressionRep Γ H (AdjointCorona Y) :=
    compressionRep Y iota s hs U hU S kappa hpair hone hsymm hgen
  -- the action laws, in the unbundled form KT.08 consumes
  have hact_mul : ∀ (a b : AdjointCorona Y) (ζ : Vec Y w ω),
      act Y w ω (a * b) ζ = act Y w ω a (act Y w ω b ζ) := by
    intro a b ζ
    simp only [act_mul Y w ω hw hω, LinearMap.comp_apply]
  have hact_one : ∀ ζ : Vec Y w ω, act Y w ω 1 ζ = ζ := by
    intro ζ
    simp only [act_one Y w ω hw hω, LinearMap.id_apply]
  have hact_sub : ∀ (a b : AdjointCorona Y) (ζ : Vec Y w ω),
      act Y w ω (a - b) ζ = act Y w ω a ζ - act Y w ω b ζ := by
    intro a b ζ
    simp only [act_sub Y w ω hw hω, LinearMap.sub_apply]
  have hact_zero : ∀ a : AdjointCorona Y,
      act Y w ω a (0 : Vec Y w ω) = 0 := fun a ↦ map_zero (act Y w ω a)
  have hact_smul : ∀ (c : ℂ) (a : AdjointCorona Y) (ζ : Vec Y w ω),
      act Y w ω (c • a) ζ = c • act Y w ω a ζ := by
    intro c a ζ
    simp only [act_smul Y w ω hw hω, LinearMap.smul_apply]
  have hact_sum : ∀ (t : Finset Γ) (f : Γ → AdjointCorona Y) (ζ : Vec Y w ω),
      act Y w ω (∑ γ ∈ t, f γ) ζ = ∑ γ ∈ t, act Y w ω (f γ) ζ :=
    fun t f ζ ↦ act_finset_sum Y w ω hw hω t f ζ
  -- KT.08 `ran P ⊆ Fix`, with `π` named as the interface names it
  have hrep : ∀ γ : Γ, piHom Y U hU (iota γ) * D.proj = D.proj :=
    fun γ ↦ D.kt_08_rep_mul_proj γ
  refine ⟨{
    Alg := AdjointCorona Y
    ring := inferInstance
    starRing := inferInstance
    dedekindFinite := inferInstance
    Vec := Vec Y w ω
    act := fun a ζ ↦ act Y w ω a ζ
    act_mul := hact_mul
    cls := cls Y w ω
    cls_eq_iff := fun C ξ η hξ hη ↦ cls_eq_iff_weightNull Y w ω hw C ξ η hξ hη
    pi := piHom Y U hU
    pi_star := piHom_star Y U hU
    act_pi_cls := fun g ξ ↦ act_pi_cls Y w ω U hU hw hω g ξ
    act_star_pi_cls := fun _C g ξ _hξ ↦ act_star_pi_cls Y w ω U hU hw hω g ξ
    P := D.proj
    P_star := D.kt_08_isSelfAdjoint_proj.star_eq
    P_mul_P := D.kt_08_proj_mul_proj
    act_P_iff := ?_
    P_mul_conjugate := D.kt_09_proj_mul_conjugate
    conjugate_mul_P := D.kt_09_conjugate_mul_proj }⟩
  intro ζ
  constructor
  · intro hζ γ
    have hζ' : act Y w ω D.proj ζ = ζ := hζ
    show act Y w ω (piHom Y U hU (iota γ)) ζ = ζ
    calc act Y w ω (piHom Y U hU (iota γ)) ζ
        = act Y w ω (piHom Y U hU (iota γ)) (act Y w ω D.proj ζ) := by
          rw [hζ']
      _ = act Y w ω (piHom Y U hU (iota γ) * D.proj) ζ :=
          (hact_mul _ _ _).symm
      _ = act Y w ω D.proj ζ := by rw [hrep γ]
      _ = ζ := hζ'
  · intro hfix
    exact D.kt_08_act_proj_of_fixed (fun a ζ ↦ act Y w ω a ζ)
      hact_mul hact_one hact_sub hact_zero hact_smul hact_sum
      (fun γ ↦ hfix γ)

/-- **The weighted ambient of manuscript steps KT.01--KT.09, as a term.**

This is the constructor whose absence made every conclusion of
`Sofic/UltraproductScaledTransport.lean` conditional: `transport_variants_one`,
`scaled_transport_both_of_ambient` and
`dimension_weight_recovers_kazhdan_transport` all take a
`WeightedUltraproductAdjointModel` for every free ultrafilter, and this supplies
it. -/
def weightedUltraproductAdjointModel
    {Γ H : Type} [Group Γ] [Group H]
    (hT : HasKazhdanPropertyT.{0, 0} Γ)
    (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (Y : ℕ → FiniteModel) (hY : ∀ n, 0 < Fintype.card (Y n))
    (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)
    (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (Y n) (Y n) ℂ) -
        (U n g : Matrix (Y n) (Y n) ℂ) * (U n h : Matrix (Y n) (Y n) ℂ)‖ ≤ ε)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    WeightedUltraproductAdjointModel iota s Y U w ω :=
  Classical.choice
    (nonempty_weightedUltraproductAdjointModel hT iota s hs Y hY U hU w hw ω hω)

end

end UltraproductModelConstruction
end GroupApproximation
