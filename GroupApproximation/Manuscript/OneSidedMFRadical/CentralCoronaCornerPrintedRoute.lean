import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaEmbedding
import GroupApproximation.Analysis.CollapseProjectionLift
import GroupApproximation.Analysis.CollapseUnitaryLift
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.Nat.Nth

/-!
# `lem:central-corona-corner` along the rewritten printed route

`non_mf_groups_exist.tex`, Lemma `lem:central-corona-corner`.  The printed
proof was rewritten to avoid ultrafilters, and it now reads:

> Lift `q` to projections `q_n ∈ M_{d_n}(ℂ)` by functional calculus.  Since
> `q ≠ 0`, infinitely many `q_n` are nonzero; retain those coordinates and put
> `r_n = rank(q_n)`.  Unitary identifications `J_n : ℂ^{r_n} → q_n ℂ^{d_n}`
> identify each corner `q_n M_{d_n}(ℂ) q_n` with `M_{r_n}(ℂ)`, and then the
> corner `q 𝒬_d q` with the corona `𝒬_r`: a bounded sequence `(z_n)`
> representing `z ∈ 𝒬_d` gives the representative `(q_n z_n q_n)` of `q z q`.
> Since `q` commutes with `ρ(G)`, the map `g ↦ q ρ(g)` is a homomorphism from
> `G` to the unitary group of the corner, with unit `q`.  Each value is a
> unitary of `𝒬_r`, so, as in the proof of Lemma `lem:stable-finite`, it lifts
> to unitaries `W_n(g) ∈ U(r_n)`, with `W_n(1) = I_{r_n}`.  Multiplicativity
> in the corona makes `(W_n)` an operator norm asymptotic representation, and
> the class of `(J_n W_n(g) J_n*)` is the coordinate restriction of `q ρ(g)`.

The existing carrier `Manuscript/OneSidedMFRadical/CentralCoronaCorner.lean`
proves the printed *statement*, but by the *previous* argument: a free
ultrafilter through
`CollapseNormalizedSetup.exists_projection_lift_and_ultrafilter`, a
polar-decomposition unitary lift `U_n(g)` of `ρ(g)`, and BDL Proposition 2.4 to
correct the compressions `q_n U_n(g) q_n`.  None of those three sentences
occurs in the printed proof any more.  This module proves the printed
statement along the printed sentences instead, and it uses no ultrafilter, no
polar decomposition of `ρ(g)` and no compression correction: the corner
unitaries are lifted *directly* out of the corner corona, which is what
"as in the proof of Lemma `lem:stable-finite`" refers to.

## What is claimed, and what is not

`PrintedCentralCoronaCorner` is the printed sentence with every clause named:
the retained subsequence `φ`, the projection lift `Q` of `q`, the corner
models `r`, the identifications `J` (additive, multiplicative,
adjoint-preserving, isometric, with `J 1 = q_n` and image exactly the corner),
the corner unitaries `W` with `W(1) = I` and vanishing multiplicative defect,
and the final corona equation.

`r_n = rank(q_n)` is **not** claimed.  The printed lemma names the integer
`r_n` as the rank of `q_n`; here `r_n` is the number of retained corner
coordinates, and only `0 < r_n` is proved.  The existing carrier
`manuscriptCentralCoronaCorner` omits the rank identification in exactly the
same way (`0 < Fintype.card (D.cornerModel k)`), so nothing that used to be
proved is dropped, but neither statement pins the printed integer.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace CentralCoronaCornerPrintedRoute

open Filter Matrix Topology
open CornerCoronaEmbedding
open PrintedCornerCompression
open KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Sentence: infinitely many `q_n` are nonzero -/

/-- **`lem:central-corona-corner`, printed sentence.**

> Since `q ≠ 0`, infinitely many `q_n` are nonzero; retain those coordinates.

No ultrafilter is used: if only finitely many coordinates of the lift were
nonzero, the lift would be null along `cofinite` and `q` would be `0`. -/
theorem manuscriptSentence_retainedCoordinatesInfinite
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (Q : BoundedMatrixSequence (fun n ↦ X n))
    {q : NormMatrixCStarCorona (fun n ↦ X n)}
    (hQmk : normMatrixCStarCoronaMk (fun n ↦ X n) Q = q) (hqne : q ≠ 0) :
    {n : ℕ | (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0}.Infinite := by
  intro hfin
  refine hqne ?_
  rw [← hQmk]
  refine (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) Q).mpr ?_
  have hev : ∀ᶠ n in Filter.cofinite,
      (0 : ℝ) = ‖(Q : ∀ n, Matrix (X n) (X n) ℂ) n‖ := by
    filter_upwards [hfin.compl_mem_cofinite] with n hn
    have hz : (Q : ∀ n, Matrix (X n) (X n) ℂ) n = 0 := not_not.mp hn
    rw [hz, norm_zero]
  exact Filter.Tendsto.congr' hev tendsto_const_nhds

/-! ## The construction on a family of nonzero corners -/

section Construction

variable {G : Type} [Group G]
  (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
  (P : ∀ n, Matrix (Y n) (Y n) ℂ) (hP : ∀ n, (P n).IsHermitian)
  [∀ n, Nonempty (cornerModel Y P hP n)]
  (Qs : BoundedMatrixSequence (fun n ↦ Y n))
  (qY : NormMatrixCStarCorona (fun n ↦ Y n))
  (u : G → NormMatrixCStarCorona (fun n ↦ Y n))
  (A : G → BoundedMatrixSequence (fun n ↦ Y n))

/-- **`lem:central-corona-corner`, printed sentence.**

> Since `q` commutes with `ρ(G)`, the map `g ↦ q ρ(g)` is a homomorphism from
> `G` to the unitary group of the corner, with unit `q`.  Each value is a
> unitary of `𝒬_r`, so, as in the proof of Lemma `lem:stable-finite`, it
> lifts to unitaries `W_n(g) ∈ U(r_n)`, with `W_n(1) = I_{r_n}`.
> Multiplicativity in the corona makes `(W_n)` an operator norm asymptotic
> representation, and the class of `(J_n W_n(g) J_n*)` is the coordinate
> restriction of `q ρ(g)`.

The corner-valued homomorphism `g ↦ q u(g)` is transported to the corner
corona along the identification of
`Manuscript/OneSidedMFRadical/CornerCoronaEmbedding.lean`, which is injective;
`Analysis/CollapseUnitaryLift.lean` then performs the lifting, which is the
same argument `lem:stable-finite` runs and which the corpus already carries. -/
theorem exists_cornerUnitaries
    (hPi : ∀ n, P n * P n = P n)
    (hQs : ∀ n, (Qs : ∀ n, Matrix (Y n) (Y n) ℂ) n = P n)
    (hQsmk : normMatrixCStarCoronaMk (fun n ↦ Y n) Qs = qY)
    (hqYstar : star qY = qY) (hqYidem : qY * qY = qY)
    (hu1 : u (1 : G) = 1) (humul : ∀ g h : G, u (g * h) = u g * u h)
    (hustar : ∀ g : G, u g * star (u g) = 1)
    (hstaru : ∀ g : G, star (u g) * u g = 1)
    (hcomm : ∀ g : G, u g * qY = qY * u g)
    (hAmk : ∀ g : G, normMatrixCStarCoronaMk (fun n ↦ Y n) (A g) = u g) :
    ∃ W : ∀ n, G → Matrix.unitaryGroup (cornerModel Y P hP n) ℂ,
      (∀ n, W n (1 : G) = 1) ∧
      (∀ g h : G, Filter.Tendsto (fun n ↦
        ‖((W n (g * h) : Matrix (cornerModel Y P hP n)
            (cornerModel Y P hP n) ℂ))
          - (W n g : Matrix (cornerModel Y P hP n) (cornerModel Y P hP n) ℂ)
            * (W n h : Matrix (cornerModel Y P hP n)
              (cornerModel Y P hP n) ℂ)‖) Filter.atTop (nhds 0)) ∧
      (∀ g : G, normMatrixCStarCoronaMk (fun n ↦ Y n)
          (cornerEmbedSeq Y P hP
            (unitarySequenceBounded (fun n ↦ cornerModel Y P hP n)
              (fun n ↦ W n g)))
        = qY * u g) := by
  classical
  -- the printed representative `(q_n z_n q_n)` of `q u(g)`
  have hEmbC : ∀ g : G, normMatrixCStarCoronaMk (fun n ↦ Y n)
      (cornerEmbedSeq Y P hP (cornerCompressSeq Y P hP (A g))) = qY * u g := by
    intro g
    have hseq : cornerEmbedSeq Y P hP (cornerCompressSeq Y P hP (A g))
        = Qs * A g * Qs := by
      refine lp.ext (funext fun n ↦ ?_)
      rw [cornerEmbedSeq_cornerCompressSeq_apply Y P hP hPi (A g) n]
      simp only [lp.infty_coeFn_mul, Pi.mul_apply, hQs n]
    rw [hseq, map_mul, map_mul, hQsmk, hAmk g]
    calc qY * u g * qY = qY * (u g * qY) := by rw [mul_assoc]
      _ = qY * (qY * u g) := by rw [hcomm g]
      _ = qY * qY * u g := by rw [mul_assoc]
      _ = qY * u g := by rw [hqYidem]
  -- the corner unit
  have hOneSeq : cornerEmbedSeq Y P hP 1 = Qs := by
    refine lp.ext (funext fun n ↦ ?_)
    rw [cornerEmbedSeq_one_apply Y P hP hPi n, hQs n]
  have hOneEmb : normMatrixCStarCoronaMk (fun n ↦ Y n)
      (cornerEmbedSeq Y P hP 1) = qY := by rw [hOneSeq, hQsmk]
  have hinj := mk_eq_of_mk_cornerEmbedSeq_eq Y P hP
  have hone : (1 : NormMatrixCStarCorona (fun n ↦ cornerModel Y P hP n))
      = normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n) 1 :=
    (map_one _).symm
  -- the corner-valued homomorphism is unitary
  have hmulstar : ∀ g : G,
      normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n)
          (cornerCompressSeq Y P hP (A g)) *
        star (normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n)
          (cornerCompressSeq Y P hP (A g))) = 1 := by
    intro g
    rw [normMatrixCStarCorona_star_mk, ← map_mul, hone]
    refine hinj _ _ ?_
    rw [cornerEmbedSeq_mul, cornerEmbedSeq_star, map_mul,
      ← normMatrixCStarCorona_star_mk, hEmbC g, hOneEmb, star_mul, hqYstar]
    calc qY * u g * (star (u g) * qY)
        = qY * (u g * star (u g)) * qY := by noncomm_ring
      _ = qY * qY := by rw [hustar g, mul_one]
      _ = qY := hqYidem
  have hstarmul : ∀ g : G,
      star (normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n)
          (cornerCompressSeq Y P hP (A g))) *
        normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n)
          (cornerCompressSeq Y P hP (A g)) = 1 := by
    intro g
    rw [normMatrixCStarCorona_star_mk, ← map_mul, hone]
    refine hinj _ _ ?_
    rw [cornerEmbedSeq_mul, cornerEmbedSeq_star, map_mul,
      ← normMatrixCStarCorona_star_mk, hEmbC g, hOneEmb, star_mul, hqYstar]
    calc star (u g) * qY * (qY * u g)
        = star (u g) * (qY * qY) * u g := by noncomm_ring
      _ = star (u g) * qY * u g := by rw [hqYidem]
      _ = star (u g) * (u g * qY) := by rw [mul_assoc, ← hcomm g]
      _ = star (u g) * u g * qY := by rw [mul_assoc]
      _ = qY := by rw [hstaru g, one_mul]
  -- and multiplicative
  have hs0mul : ∀ g h : G,
      normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n)
          (cornerCompressSeq Y P hP (A (g * h)))
        = normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n)
            (cornerCompressSeq Y P hP (A g)) *
          normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n)
            (cornerCompressSeq Y P hP (A h)) := by
    intro g h
    rw [← map_mul]
    refine hinj _ _ ?_
    rw [cornerEmbedSeq_mul, map_mul, hEmbC g, hEmbC h, hEmbC (g * h), humul g h]
    calc qY * (u g * u h) = qY * qY * (u g * u h) := by rw [hqYidem]
      _ = qY * (qY * u g) * u h := by noncomm_ring
      _ = qY * (u g * qY) * u h := by rw [hcomm g]
      _ = qY * u g * (qY * u h) := by noncomm_ring
  have hs0one : normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n)
      (cornerCompressSeq Y P hP (A (1 : G)))
      = (1 : NormMatrixCStarCorona (fun n ↦ cornerModel Y P hP n)) := by
    rw [hone]
    refine hinj _ _ ?_
    rw [hEmbC (1 : G), hOneEmb, hu1, mul_one]
  -- the printed lift, as in the proof of `lem:stable-finite`
  let tau : G →*
      unitary (NormMatrixCStarCorona (fun n ↦ cornerModel Y P hP n)) :=
    { toFun := fun g ↦ ⟨normMatrixCStarCoronaMk
          (fun n ↦ cornerModel Y P hP n) (cornerCompressSeq Y P hP (A g)),
        ⟨hstarmul g, hmulstar g⟩⟩
      map_one' := Subtype.ext hs0one
      map_mul' := fun g h ↦ Subtype.ext (hs0mul g h) }
  refine ⟨fun n g ↦ CollapseUnitaryLift.liftFam
      (fun n ↦ cornerModel Y P hP n) tau g n, ?_, ?_, ?_⟩
  · intro n
    exact CollapseUnitaryLift.liftFam_one_apply
      (fun n ↦ cornerModel Y P hP n) tau n
  · intro g h
    have h1 := CollapseUnitaryLift.tendsto_defect
      (fun n ↦ cornerModel Y P hP n) tau g h
    rwa [Nat.cofinite_eq_atTop] at h1
  · intro g
    have hclass : normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n)
        (unitarySequenceBounded (fun n ↦ cornerModel Y P hP n)
          (CollapseUnitaryLift.liftFam
            (fun n ↦ cornerModel Y P hP n) tau g))
        = normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n)
            (cornerCompressSeq Y P hP (A g)) :=
      congrArg Subtype.val
        (CollapseUnitaryLift.unitarySequenceToCorona_liftFam
          (fun n ↦ cornerModel Y P hP n) tau g)
    have h2 := mk_cornerEmbedSeq_congr Y P hP _ _ hclass
    rw [hEmbC g] at h2
    exact h2

end Construction

/-! ## The printed lemma -/

/-- **Lemma `lem:central-corona-corner`, exactly as printed, with the
identifications named.**

Every clause of the printed sentence is a conjunct: the retained subsequence
`φ`, the projection lift `Q` of `q`, the corner models `r`, the identifications
`J` (additive, multiplicative, adjoint-preserving, isometric, with `J 1 = q_n`
and image exactly the corner `q_n M q_n`), the corner unitaries `W` with
`W(1) = I` and vanishing multiplicative defect, and the closing equation:
in the corona over the retained coordinates the class of `(J_n W_n(g) J_n*)`
is the coordinate restriction of `q ρ(g)`.

The printed `r_n = rank(q_n)` is replaced by `0 < Fintype.card (r n)`, exactly
as in the existing carrier `manuscriptCentralCoronaCorner`. -/
def PrintedCentralCoronaCorner : Prop :=
  ∀ (G : Type) [Group G] [Countable G]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (q : NormMatrixCStarCorona (fun n ↦ X n)),
    star q = q → q * q = q → q ≠ 0 →
    (∀ g : G, ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) * q =
      q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n))) →
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (Q : BoundedMatrixSequence (fun n ↦ X n))
      (r : ℕ → FiniteModel)
      (J : ∀ k, Matrix (r k) (r k) ℂ → Matrix (X (φ k)) (X (φ k)) ℂ)
      (W : ∀ k, G → Matrix.unitaryGroup (r k) ℂ)
      (amb : G → BoundedMatrixSequence (fun k ↦ X (φ k))),
      (∀ n, IsOrthogonalProjectionMatrix
        ((Q : ∀ n, Matrix (X n) (X n) ℂ) n)) ∧
      normMatrixCStarCoronaMk (fun n ↦ X n) Q = q ∧
      (∀ k, (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k) ≠ 0) ∧
      (∀ k, 0 < Fintype.card (r k)) ∧
      (∀ (k : ℕ) (B C : Matrix (r k) (r k) ℂ),
        J k (B + C) = J k B + J k C) ∧
      (∀ (k : ℕ) (B C : Matrix (r k) (r k) ℂ),
        J k (B * C) = J k B * J k C) ∧
      (∀ (k : ℕ) (B : Matrix (r k) (r k) ℂ), (J k B)ᴴ = J k Bᴴ) ∧
      (∀ (k : ℕ) (B : Matrix (r k) (r k) ℂ), ‖J k B‖ = ‖B‖) ∧
      (∀ k : ℕ, J k 1 = (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k)) ∧
      (∀ (k : ℕ) (B : Matrix (r k) (r k) ℂ),
        (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k) * J k B *
            (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k) = J k B) ∧
      (∀ (k : ℕ) (Z : Matrix (X (φ k)) (X (φ k)) ℂ),
        ∃ B : Matrix (r k) (r k) ℂ,
          J k B = (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k) * Z *
            (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k)) ∧
      (∀ k : ℕ, W k (1 : G) = 1) ∧
      (∀ g h : G, Filter.Tendsto (fun k ↦
        ‖((W k (g * h) : Matrix (r k) (r k) ℂ))
          - (W k g : Matrix (r k) (r k) ℂ) *
            (W k h : Matrix (r k) (r k) ℂ)‖) Filter.atTop (nhds 0)) ∧
      (∀ (g : G) (k : ℕ),
        (amb g : ∀ k, Matrix (X (φ k)) (X (φ k)) ℂ) k
          = J k ((W k g : Matrix (r k) (r k) ℂ))) ∧
      (∀ g : G, normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (amb g)
        = coronaRestrict X φ hφ
            (q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
              NormMatrixCStarCorona (fun n ↦ X n))))

/-- Closed proof of `lem:central-corona-corner` along the rewritten printed
route: a projection lift, the retained coordinates, the corner-corona
identification, and a unitary lift out of the corner corona.  No ultrafilter,
no polar decomposition of `ρ(g)`, no compression correction. -/
theorem manuscriptPrintedCentralCoronaCorner : PrintedCentralCoronaCorner := by
  classical
  intro G _ _ X _ rho q hqstar hqidem hqne hcomm
  -- printed sentence: lift `q` to projections `q_n` by functional calculus
  obtain ⟨Q, hQproj, hQmk⟩ :=
    CollapseProjectionLift.exists_projection_lift X q hqstar hqidem
  have hQherm : ∀ n, ((Q : ∀ n, Matrix (X n) (X n) ℂ) n).IsHermitian :=
    fun n ↦ (hQproj n).1
  have hQi : ∀ n, (Q : ∀ n, Matrix (X n) (X n) ℂ) n *
      (Q : ∀ n, Matrix (X n) (X n) ℂ) n
      = (Q : ∀ n, Matrix (X n) (X n) ℂ) n := fun n ↦ (hQproj n).2
  -- printed sentence: infinitely many `q_n` are nonzero; retain those
  have hinf := manuscriptSentence_retainedCoordinatesInfinite X Q hQmk hqne
  set phi : ℕ → ℕ :=
    Nat.nth (fun n ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0) with hphi
  have hphimono : StrictMono phi := Nat.nth_strictMono hinf
  have hne : ∀ k, (Q : ∀ n, Matrix (X n) (X n) ℂ) (phi k) ≠ 0 :=
    fun k ↦ Nat.nth_mem_of_infinite hinf k
  letI : ∀ k, Nonempty (cornerModel (fun k ↦ X (phi k))
      (fun k ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) (phi k))
      (fun k ↦ hQherm (phi k)) k) :=
    cornerModel_nonempty _ _ _ (fun k ↦ hQi (phi k)) hne
  -- the restricted data
  have hQsmk : normMatrixCStarCoronaMk (fun k ↦ X (phi k))
      (restrictSeq X phi Q) = coronaRestrict X phi hphimono q := by
    rw [← hQmk, coronaRestrict_mk]
  have hAmk : ∀ g : G, normMatrixCStarCoronaMk (fun k ↦ X (phi k))
      (restrictSeq X phi (unitarySequenceBounded X
        (CollapseUnitaryLift.liftFam X rho g)))
      = coronaRestrict X phi hphimono
          ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) := by
    intro g
    have hlift : normMatrixCStarCoronaMk (fun n ↦ X n)
        (unitarySequenceBounded X (CollapseUnitaryLift.liftFam X rho g))
        = ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) :=
      congrArg Subtype.val
        (CollapseUnitaryLift.unitarySequenceToCorona_liftFam X rho g)
    rw [← hlift, coronaRestrict_mk]
  have hqYstar : star (coronaRestrict X phi hphimono q)
      = coronaRestrict X phi hphimono q := by
    rw [← coronaRestrict_star, hqstar]
  have hqYidem : coronaRestrict X phi hphimono q *
      coronaRestrict X phi hphimono q = coronaRestrict X phi hphimono q := by
    rw [← map_mul, hqidem]
  have hu1 : coronaRestrict X phi hphimono
      ((rho (1 : G) : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) = 1 := by
    have h1 : ((rho (1 : G) :
        unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) = 1 := by
      rw [map_one rho]; rfl
    rw [h1]
    exact map_one (coronaRestrict X phi hphimono)
  have humul : ∀ g h : G, coronaRestrict X phi hphimono
      ((rho (g * h) : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n))
      = coronaRestrict X phi hphimono
          ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) *
        coronaRestrict X phi hphimono
          ((rho h : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) := by
    intro g h
    have h1 : ((rho (g * h) :
        unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n))
        = ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) *
          ((rho h : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) := by
      rw [map_mul rho]; rfl
    rw [h1, map_mul]
  have hustar : ∀ g : G, coronaRestrict X phi hphimono
      ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) *
      star (coronaRestrict X phi hphimono
        ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n))) = 1 := by
    intro g
    rw [← coronaRestrict_star, ← map_mul,
      Unitary.mul_star_self_of_mem (rho g).2]
    exact map_one (coronaRestrict X phi hphimono)
  have hstaru : ∀ g : G, star (coronaRestrict X phi hphimono
        ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n))) *
      coronaRestrict X phi hphimono
        ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) = 1 := by
    intro g
    rw [← coronaRestrict_star, ← map_mul,
      Unitary.star_mul_self_of_mem (rho g).2]
    exact map_one (coronaRestrict X phi hphimono)
  have hucomm : ∀ g : G, coronaRestrict X phi hphimono
      ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) *
      coronaRestrict X phi hphimono q
      = coronaRestrict X phi hphimono q *
        coronaRestrict X phi hphimono
          ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) := by
    intro g
    rw [← map_mul, ← map_mul, hcomm g]
  -- the corner unitaries
  obtain ⟨W, hWone, hWdefect, hWclass⟩ :=
    exists_cornerUnitaries (G := G) (fun k ↦ X (phi k))
      (fun k ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) (phi k))
      (fun k ↦ hQherm (phi k))
      (restrictSeq X phi Q) (coronaRestrict X phi hphimono q)
      (fun g ↦ coronaRestrict X phi hphimono
        ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)))
      (fun g ↦ restrictSeq X phi (unitarySequenceBounded X
        (CollapseUnitaryLift.liftFam X rho g)))
      (fun k ↦ hQi (phi k)) (fun _ ↦ rfl) hQsmk hqYstar hqYidem hu1 humul
      hustar hstaru hucomm hAmk
  refine ⟨phi, hphimono, Q,
    (fun k ↦ cornerModel (fun k ↦ X (phi k))
      (fun k ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) (phi k))
      (fun k ↦ hQherm (phi k)) k),
    (fun k ↦ cornerEmbed (hQherm (phi k))), W,
    (fun g ↦ cornerEmbedSeq (fun k ↦ X (phi k))
      (fun k ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) (phi k))
      (fun k ↦ hQherm (phi k))
      (unitarySequenceBounded _ (fun k ↦ W k g))),
    hQproj, hQmk, hne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hWone, hWdefect,
    ?_, ?_⟩
  · exact fun k ↦ cornerModel_card_pos _ _ _ (fun k ↦ hQi (phi k)) hne k
  · exact fun k ↦ NormalKazhdanPrintedRoute.cornerEmbed_add (hQherm (phi k))
  · exact fun k ↦ cornerEmbed_mul (hQherm (phi k))
  · exact fun k ↦ cornerEmbed_conjTranspose (hQherm (phi k))
  · exact fun k ↦ norm_cornerEmbed (hQherm (phi k))
  · exact fun k ↦ cornerEmbed_one (hQherm (phi k)) (hQi (phi k))
  · exact fun k ↦ cornerEmbed_mem_corner (hQherm (phi k)) (hQi (phi k))
  · exact fun k Z ↦ ⟨cornerCompression (hQherm (phi k)) Z,
      cornerEmbed_cornerCompression (hQherm (phi k)) (hQi (phi k)) Z⟩
  · exact fun g k ↦ rfl
  · intro g
    rw [hWclass g, ← map_mul]

end

end CentralCoronaCornerPrintedRoute
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.CentralCoronaCornerPrintedRoute.manuscriptPrintedCentralCoronaCorner
