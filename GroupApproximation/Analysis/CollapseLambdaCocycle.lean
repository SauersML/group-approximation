import GroupApproximation.Analysis.CollapseUltraproductRepresentation
import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Analysis.OmegaConjQCompatibility
import GroupApproximation.Analysis.RankNormalizedLambda

/-!
# `β(g) = Λ(d_g)` is a cocycle in `K_ω`, and it does not vanish

Proof-ledger row `CO.21`, the paragraph *An exact cocycle* and the
nonvanishing paragraph in the proof of `thm:projection-collapse` in
`non_mf_groups_exist.tex` (navigate by the label; that file is under
concurrent edit).

The row was split on 2026-08-17.  Its algebraic half —
`eq:collapse-cocycle`, `d_{gh} = d_g + Θ(g) d_h Θ(g)*`, and the two
identities `q_a q = q_a`, `d_a = d_a q_a` that put `d_a` in the ideal — is
`Analysis/ProjectionOrbitCollapse`, proved in an arbitrary ring with
involution.  Its analytic half was recorded as *the whole difficulty*: `Λ`,
the space it lands in, and the nonvanishing.  `Analysis/CollapseCocycleAnalytic`
then supplied the conjugation action on `K_ω` and transported a *coordinate*
cocycle identity to the classes, and `Analysis/RankNormalizedLambda` supplied
`Λ`.  What was still missing is the join between them: the cocycle identity
stated for `β(g) = Λ(d_g)`, with `d_g` an element of the corona ideal rather
than a coordinate family, and the nonvanishing.

Both are here.

## Equivariance

`conjIsometryEquiv_lambda` is the printed
*"`π(h) Λ(z) = Λ(Θ(h) z Θ(h)*)` on the closed invariant subspace
`K_q = closure Λ(𝓘_q)`"*.  It is proved where the print proves it — on
representatives: a rank-controlled representative of `z` conjugates to a
rank-controlled representative of `Θ(h) z Θ(h)*`, because sandwiching does not
raise the rank, and `conjBounded` is conjugation of representatives.  No
closure is taken, because none is needed: the identity holds on the ideal
itself, and every use of it in the proof is at an element of the ideal.

## The cocycle

`lambda_cocycle` reads `eq:collapse-cocycle` through `Λ`.  The displacements
enter as a family `d : H → 𝓘_q` satisfying the printed identity *in the
corona*; the conclusion is `β(gh) = β(g) + π(g) β(h)` in `K_ω` for the
representation `conjRep` that `collapse_contradiction_kOmega` consumes.  That
is the shape `Kazhdan/DelormeFixedPoint` needs, so this closes the gap between
the algebraic identity and the hypothesis `hβ` of the endpoint.

## The nonvanishing

`lambda_sum_eq_zero` is the printed telescoping read through `Λ`, and it is
one line once `Λ` is a linear map: `∑_i e_i = q` in the ideal, `Λ(e_i) = 0`,
so `Λ(q) = 0`.  `not_all_lambda_eq_zero` is the contradiction with
`‖Λ(q)‖ = 1`, which is the printed *"so `β` is not identically zero"*.

Compare `CollapseDelormeEndpoint.massNull_join`, which proves the same
telescoping directly on coordinate families and needed the one-sided kernel
stability to do it.  With `Λ` in hand the argument is linearity, which is what
the printed sentence actually says.

## The printed lift is only asymptotically multiplicative

`conjRep` requires an exactly multiplicative coordinate lift, while the lift of
`lem:unitarycorona` is only asymptotically multiplicative.  That gap does not
need closing: `Analysis/OmegaIsometryRepresentation.rep` already builds an
honest homomorphism `H →* (K_ω ≃ₗᵢ[ℂ] K_ω)` from an operator-norm *almost*
representation — freeness of `ω` is what turns the asymptotic identity into an
exact one on classes — and
`OmegaConjQCompatibility.repEquiv_eq_conjIsometryEquiv` identifies its values
with conjugation of representatives.  `lambda_cocycle_almost` is therefore the
cocycle at the printed generality, and `lambda_cocycle` is the special case
that `collapse_contradiction_kOmega` consumes as stated.
-/

namespace GroupApproximation
namespace CollapseLambdaCocycle

open Filter Matrix Topology
open KazhdanCornerMatrices ScaledKazhdanTransport
open UltraproductModelConstruction RankNormalizedHilbertization
open KOmegaHilbert CollapseCocycleAnalytic CollapseUltraproductRepresentation
open RankNormalizedLambda
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]

/-! ## Conjugation of a representative -/

/-- The adjoint of the bounded sequence of a unitary family is its
coordinatewise conjugate transpose. -/
theorem star_unitarySequenceBounded_apply
    (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) (n : ℕ) :
    ((star (unitarySequenceBounded Y U)) n : Matrix (Y n) (Y n) ℂ)
      = (U n : Matrix (Y n) (Y n) ℂ)ᴴ := by
  rw [lp.star_apply]
  exact Matrix.star_eq_conjTranspose _

/-- **Conjugation acts on representatives.**  `Ad U_n` applied to the
coordinate family of a rank-controlled sequence is the coordinate family of its
conjugate.  This is what makes the printed
`π(h) Λ(z) = Λ(Θ(h) z Θ(h)*)` a computation and not an extension by
continuity. -/
theorem conjBounded_coordRC (P : MatFam Y)
    (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) (a : rankControlled Y P) :
    conjBounded Y (rankWeight Y P) U (coordRC Y P a)
      = coordRC Y P
          ⟨unitarySequenceBounded Y U *
              (a : BoundedMatrixSequence (fun n ↦ Y n)) *
              star (unitarySequenceBounded Y U),
            mul_mul_mem_rankControlled Y P _ _ a.2⟩ := by
  refine Subtype.ext (funext fun n ↦ ?_)
  show (U n : Matrix (Y n) (Y n) ℂ) *
      ((a : BoundedMatrixSequence (fun m ↦ Y m)) n) *
      (U n : Matrix (Y n) (Y n) ℂ)ᴴ
    = (U n : Matrix (Y n) (Y n) ℂ) *
      ((a : BoundedMatrixSequence (fun m ↦ Y m)) n) *
      ((star (unitarySequenceBounded Y U)) n)
  rw [star_unitarySequenceBounded_apply]

/-- Equivariance of `Λ` on representatives. -/
theorem conjIsometryEquiv_lambdaBounded (P : MatFam Y) (ω : Ultrafilter ℕ)
    (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) (a : rankControlled Y P) :
    conjIsometryEquiv Y (rankWeight Y P) ω (rankWeight_nonneg Y P) U
        (lambdaBounded Y P ω a)
      = lambdaBounded Y P ω
          ⟨unitarySequenceBounded Y U *
              (a : BoundedMatrixSequence (fun n ↦ Y n)) *
              star (unitarySequenceBounded Y U),
            mul_mul_mem_rankControlled Y P _ _ a.2⟩ :=
  congrArg (mkK Y (rankWeight Y P) ω (rankWeight_nonneg Y P))
    (conjBounded_coordRC Y P U a)

/-! ## Equivariance of `Λ` -/

/-- **The printed `π(h) Λ(z) = Λ(Θ(h) z Θ(h)*)`.**  The conjugation
representation of `K_ω` carries the value of `Λ` at an ideal element to its
value at the conjugate. -/
theorem conjIsometryEquiv_lambda (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite)
    (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) (z w : rankIdeal Y P)
    (hw : (w : NormMatrixCStarCorona (fun n ↦ Y n))
      = coronaLinear Y (unitarySequenceBounded Y U) *
          (z : NormMatrixCStarCorona (fun n ↦ Y n)) *
          star (coronaLinear Y (unitarySequenceBounded Y U))) :
    conjIsometryEquiv Y (rankWeight Y P) ω (rankWeight_nonneg Y P) U
        (lambda Y P ω hω z)
      = lambda Y P ω hω w := by
  have hstar : normMatrixCStarCoronaMk (fun m ↦ Y m)
      (star (unitarySequenceBounded Y U))
      = star (normMatrixCStarCoronaMk (fun m ↦ Y m)
        (unitarySequenceBounded Y U)) :=
    (normMatrixCStarCorona_star_mk (fun m ↦ Y m) _).symm
  have hl : normMatrixCStarCoronaMk (fun m ↦ Y m)
      ((lift Y P z : rankControlled Y P) :
        BoundedMatrixSequence (fun n ↦ Y n))
      = (z : NormMatrixCStarCorona (fun n ↦ Y n)) :=
    coronaLinear_lift Y P z
  have hw' : (w : NormMatrixCStarCorona (fun n ↦ Y n))
      = normMatrixCStarCoronaMk (fun m ↦ Y m) (unitarySequenceBounded Y U) *
          (z : NormMatrixCStarCorona (fun n ↦ Y n)) *
          star (normMatrixCStarCoronaMk (fun m ↦ Y m)
            (unitarySequenceBounded Y U)) := hw
  have ha : coronaLinear Y
      (unitarySequenceBounded Y U *
        ((lift Y P z : rankControlled Y P) :
          BoundedMatrixSequence (fun n ↦ Y n)) *
        star (unitarySequenceBounded Y U))
      = (w : NormMatrixCStarCorona (fun n ↦ Y n)) := by
    show normMatrixCStarCoronaMk (fun m ↦ Y m)
        (unitarySequenceBounded Y U *
          ((lift Y P z : rankControlled Y P) :
            BoundedMatrixSequence (fun n ↦ Y n)) *
          star (unitarySequenceBounded Y U)) = _
    rw [hw', map_mul, map_mul, hl, hstar]
  have hz : lambda Y P ω hω z = lambdaBounded Y P ω (lift Y P z) := rfl
  rw [hz, conjIsometryEquiv_lambdaBounded,
    lambda_apply Y P ω hω w
      ⟨unitarySequenceBounded Y U *
          ((lift Y P z : rankControlled Y P) :
            BoundedMatrixSequence (fun n ↦ Y n)) *
          star (unitarySequenceBounded Y U),
        mul_mul_mem_rankControlled Y P _ _ (lift Y P z).2⟩ ha]

/-! ## The cocycle -/

/-- **`CO.21`, the analytic half.**  For a coordinatewise unitary lift `Θ` and
a family `d` of ideal elements satisfying `eq:collapse-cocycle` in the corona,
`β(g) = Λ(d_g)` is a `1`-cocycle for the conjugation representation `π` on the
rank-normalized ultraproduct:

  `β(gh) = β(g) + π(g) β(h)`.

This is the hypothesis `hβ` of
`CollapseUltraproductRepresentation.collapse_contradiction_kOmega`, so the two
halves of the printed proof now meet: the algebraic identity
`ProjectionOrbitCollapse.sub_conj_mul` supplies `hd`, and this theorem turns it
into the cocycle the Delorme–Guichardet endpoint consumes. -/
theorem lambda_cocycle {H : Type u} [Group H] (P : MatFam Y)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) (d : H → rankIdeal Y P)
    (hd : ∀ g h : H, (d (g * h) : NormMatrixCStarCorona (fun n ↦ Y n))
      = (d g : NormMatrixCStarCorona (fun n ↦ Y n))
        + coronaLinear Y (unitarySequenceBounded Y (Θ g)) *
            (d h : NormMatrixCStarCorona (fun n ↦ Y n)) *
            star (coronaLinear Y (unitarySequenceBounded Y (Θ g))))
    (g h : H) :
    lambda Y P ω hω (d (g * h))
      = lambda Y P ω hω (d g)
        + conjRep Y (rankWeight Y P) ω (rankWeight_nonneg Y P) Θ g
            (lambda Y P ω hω (d h)) := by
  have hmem : coronaLinear Y (unitarySequenceBounded Y (Θ g)) *
      (d h : NormMatrixCStarCorona (fun n ↦ Y n)) *
      star (coronaLinear Y (unitarySequenceBounded Y (Θ g)))
      ∈ rankIdeal Y P :=
    mul_mem_rankIdeal Y P _ _ (d h).2
  have heq : conjRep Y (rankWeight Y P) ω (rankWeight_nonneg Y P) Θ g
      (lambda Y P ω hω (d h)) = lambda Y P ω hω ⟨_, hmem⟩ := by
    show conjIsometryEquiv Y (rankWeight Y P) ω (rankWeight_nonneg Y P)
        (fun n ↦ Θ g n) (lambda Y P ω hω (d h)) = _
    exact conjIsometryEquiv_lambda Y P ω hω (fun n ↦ Θ g n) (d h) ⟨_, hmem⟩ rfl
  have hsum : d (g * h) = d g + ⟨_, hmem⟩ := by
    refine Subtype.ext ?_
    show (d (g * h) : NormMatrixCStarCorona (fun n ↦ Y n))
      = (d g : NormMatrixCStarCorona (fun n ↦ Y n))
        + coronaLinear Y (unitarySequenceBounded Y (Θ g)) *
            (d h : NormMatrixCStarCorona (fun n ↦ Y n)) *
            star (coronaLinear Y (unitarySequenceBounded Y (Θ g)))
    exact hd g h
  rw [heq, hsum, map_add]

/-! ## The nonvanishing of `β` -/

/-- **The printed telescoping, through `Λ`.**  If the join `q` is the sum of
ideal elements each killed by `Λ`, then `Λ(q) = 0`.  This is the printed
*"the products `e_i = r_i q_{a_i}` … satisfy `∑_i e_i = q` … and
`Λ(e_i) = 0`, whence `Λ(q) = 0`"*, and with `Λ` a linear map it is exactly
linearity. -/
theorem lambda_sum_eq_zero (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (m : ℕ) (e : ℕ → rankIdeal Y P)
    (qz : rankIdeal Y P)
    (hq : (qz : NormMatrixCStarCorona (fun n ↦ Y n))
      = ∑ i ∈ Finset.range m,
          (e i : NormMatrixCStarCorona (fun n ↦ Y n)))
    (he : ∀ i, lambda Y P ω hω (e i) = 0) :
    lambda Y P ω hω qz = 0 := by
  have hsum : qz = ∑ i ∈ Finset.range m, e i := by
    refine Subtype.ext ?_
    rw [hq, Submodule.coe_sum]
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ ↦ he i

/-- **The printed *"so `β` is not identically zero"*.**  The join of the
displacement supports is the class of a projection lift of positive rank, so
`‖Λ(q)‖ = 1`; if every `Λ(e_i)` vanished, `Λ(q)` would vanish. -/
theorem not_all_lambda_eq_zero (Q : BoundedMatrixSequence (fun n ↦ Y n))
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (hproj : ∀ n, IsOrthogonalProjectionMatrix (Q n))
    (hrk : ∀ n, 0 < (Q n).rank) (m : ℕ)
    (e : ℕ → rankIdeal Y (coord Y Q)) (qz : rankIdeal Y (coord Y Q))
    (hqz : (qz : NormMatrixCStarCorona (fun n ↦ Y n)) = coronaLinear Y Q)
    (hq : (qz : NormMatrixCStarCorona (fun n ↦ Y n))
      = ∑ i ∈ Finset.range m,
          (e i : NormMatrixCStarCorona (fun n ↦ Y n)))
    (he : ∀ i, lambda Y (coord Y Q) ω hω (e i) = 0) : False := by
  have h1 : ‖lambda Y (coord Y Q) ω hω qz‖ = 1 :=
    norm_lambda_projection Y Q ω hω hproj hrk qz hqz
  rw [lambda_sum_eq_zero Y (coord Y Q) ω hω m e qz hq he, norm_zero] at h1
  exact zero_ne_one h1

/-! ## The cocycle at the printed generality -/

section Almost

variable {H : Type u} [Group H] (A : OpAlmostRepresentation H)

/-- The coordinate models of an almost representation are nonempty, so the
instance the corona construction needs is never a restriction. -/
theorem nonempty_model (n : ℕ) : Nonempty (A.model n) :=
  Fintype.card_pos_iff.mp (A.modelNonempty n)

variable [∀ n, Nonempty (A.model n)]

/-- **`CO.21` at the printed generality.**  The same cocycle identity for the
representation built from an operator-norm *almost* representation, which is
what `lem:unitarycorona` supplies: the printed unitary coordinate lifts
`U_n(h)` of `Θ(h)` are only asymptotically multiplicative, and freeness of `ω`
makes `π(h) = [Ad U_n(h)]_ω` a homomorphism all the same.

The bridge is `OmegaConjQCompatibility.repEquiv_eq_conjIsometryEquiv`: the
bundled corona representation acts on a class by conjugating a representative,
which is exactly the map `conjIsometryEquiv_lambda` is stated for. -/
theorem lambda_cocycle_almost (P : MatFam A.model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (d : H → rankIdeal A.model P)
    (hd : ∀ g h : H,
      (d (g * h) : NormMatrixCStarCorona (fun n ↦ A.model n))
        = (d g : NormMatrixCStarCorona (fun n ↦ A.model n))
          + coronaLinear A.model
              (unitarySequenceBounded A.model (fun n ↦ A.map n g)) *
            (d h : NormMatrixCStarCorona (fun n ↦ A.model n)) *
            star (coronaLinear A.model
              (unitarySequenceBounded A.model (fun n ↦ A.map n g))))
    (g h : H) :
    lambda A.model P ω hω (d (g * h))
      = lambda A.model P ω hω (d g)
        + OmegaIsometryRepresentation.rep A (rankWeight A.model P) ω hω
            (rankWeight_nonneg A.model P) g (lambda A.model P ω hω (d h)) := by
  have hmem : coronaLinear A.model
      (unitarySequenceBounded A.model (fun n ↦ A.map n g)) *
      (d h : NormMatrixCStarCorona (fun n ↦ A.model n)) *
      star (coronaLinear A.model
        (unitarySequenceBounded A.model (fun n ↦ A.map n g)))
      ∈ rankIdeal A.model P :=
    mul_mem_rankIdeal A.model P _ _ (d h).2
  have heq : OmegaIsometryRepresentation.rep A (rankWeight A.model P) ω hω
      (rankWeight_nonneg A.model P) g (lambda A.model P ω hω (d h))
      = lambda A.model P ω hω ⟨_, hmem⟩ := by
    show OmegaIsometryRepresentation.repEquiv A (rankWeight A.model P) ω hω
        (rankWeight_nonneg A.model P) g (lambda A.model P ω hω (d h)) = _
    rw [OmegaConjQCompatibility.repEquiv_eq_conjIsometryEquiv A
      (rankWeight A.model P) ω hω (rankWeight_nonneg A.model P) g]
    exact conjIsometryEquiv_lambda A.model P ω hω (fun n ↦ A.map n g) (d h)
      ⟨_, hmem⟩ rfl
  have hsum : d (g * h) = d g + ⟨_, hmem⟩ := Subtype.ext (hd g h)
  rw [heq, hsum, map_add]

end Almost

end

end CollapseLambdaCocycle
end GroupApproximation
