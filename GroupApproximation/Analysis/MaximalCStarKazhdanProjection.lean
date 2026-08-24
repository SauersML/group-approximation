import GroupApproximation.Analysis.MaximalCStarAllUniverses
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Kazhdan.KazhdanGenerators
import GroupApproximation.Kazhdan.KazhdanUniverse
import GroupApproximation.Sofic.UltraproductKazhdanProjection

/-!
# The Kazhdan projection of `Cmax(Λ)` and the one-sided order of its image

`non_mf_groups_exist.tex`, Lemma `lem:kazhdan-projection-order`:

> Let `L` have property (T), let `B` be a unital `C*`-algebra, and let
> `π : L → U(B)` be a homomorphism.  Denote by `P ∈ B` **the image of the
> Kazhdan projection under the extension `C*_max(L) → B`**.  If `U ∈ U(B)`
> satisfies `U π(L) U* ⊆ π(L)`, then `U* P U ≤ P`.

This file supplies the `Cmax` layer of that sentence: the Kazhdan projection is
built **once, inside `Cmax(Λ)`**, and `P` is literally its image under a
`⋆`-homomorphism `Cmax(Λ) → B` carrying the canonical unitaries to `π`.  The
target `B` is a unital `C*`-algebra in an arbitrary universe, and the order
relation is a genuine `C*`-order on `B`.

## What the repository already had, and what it did not

* `Cmax(Λ)` as a unital `C*`-algebra: `MaximalGroupCStar`
  (`Analysis/MaximalGroupCStar.lean`), with canonical unitaries
  `maximalGroupCStarUnitaryHom` / `maximalGroupCStarGenerator`.
* Its universal property with the universe of `B` unrestricted:
  `maximalGroupCStar_existsUnique_lift_allUniverses`
  (`Analysis/MaximalCStarAllUniverses.lean`).
* The Kazhdan projection **in an abstract algebra carrying the
  representation**: `CStarSpectralProjection.spectralProjection` applied to the
  orbit average, whose spectral gap is
  `UltraproductKazhdanProjection.unitaryAverage_spectrum_le_manuscript` (the
  printed rate `1 - κ²/(2|S|)`), with the absorption calculus of
  `Analysis/KazhdanProjectionAbsorption.lean`.  Two consumers instantiate this:
  `Analysis/MaximalCStarProperCompression.lean` at `Cmax(E)` for the *ambient*
  group, and `Manuscript/OneSidedMFRadical/KazhdanProjectionOrder.lean` at the
  *target* algebra `B` itself.

The last point is exactly the gap this file closes.  In both existing consumers
the projection is manufactured *in the algebra where the inequality is
asserted*; neither exhibits it as the image of a single element of `Cmax(Λ)`.
The manuscript's `P` is the image, and that is what is proved below.

## The route, and why no functional-calculus naturality is needed

Everything analytic happens in `Cmax(Λ)`:

* `KazhdanData.average` is the orbit average `|S|⁻¹ Σ_{s ∈ S} u_s` of the
  canonical unitaries;
* `KazhdanData.gap` is the uniform Kazhdan estimate of
  `Kazhdan/KazhdanProjection.lean`, transported to the `C*`-spectrum — this is
  the step that converts a representation-independent Hilbert-space contraction
  into a statement about `Cmax(Λ)`;
* `KazhdanData.projection` is the spectral projection at the isolated spectral
  point `1`, which is what the manuscript's paragraph *The Kazhdan projection*
  defines the Kazhdan projection to be.

The image `P = f p` under a `⋆`-homomorphism `f : Cmax(Λ) → B` then inherits,
by `map_mul` / `map_star` / `map_sub` alone:

* `P* = P`, `P² = P`, `M P = P` with `M = f(average) = |S|⁻¹ Σ π(s)`;
* `π(γ) P = P` for **every** `γ ∈ Λ` (the algebraic form of `ran P ⊆ Fix π(Λ)`);
* the resolvent factorisation `1 - P = R (1 - M)` with
  `R = f (cfc (gapResolvent rate) average)`.

The last item is the whole point: `conj_absorbs_of_factorisation` below is
`KazhdanProjectionAbsorption.conjugated_projection_absorbs` with the
`cfc`-factor turned into an abstract factor `r`, so the conjugated-average
absorption `(U M U*) P = P` — which is the printed line
`π(ℓ) U* ξ = U* (U π(ℓ) U*) ξ = U* ξ` read algebraically — upgrades to
`(U P U*) P = P` **without** any statement about `f` commuting with the
continuous functional calculus.  Conjugating back by `U*` gives the printed
`(U* P U) P = U* P U`, and for star projections that identity *is* the Loewner
inequality `U* P U ≤ P`.

`image_eq_spectralProjection` closes the loop with the existing consumers: as
soon as the same gap holds in `B` (it does whenever `B` carries a Kazhdan pair
at its own universe, which is the hypothesis those consumers already assume),
the image of the `Cmax` projection *is* the spectral projection built in `B`.
It is proved from the two resolvent factorisations, again with no naturality.

## What is not claimed

The order relation on `B` is taken as an instance argument
`[PartialOrder B] [StarOrderedRing B]`, the idiom of
`Analysis/ProperIsometryStrictOrder.lean`: the statement therefore holds for
every compatible order, the printed one — `CStarAlgebra.spectralOrder` — among
them.  Nothing here asserts that `B` has a faithful nondegenerate
representation; the printed proof's passage to `B(ℋ)` is replaced by the
algebra-internal absorption calculus, and the Hilbert-space form of the same
lemma is `Analysis/KazhdanProjectionOneSidedOrder.lean`.

The Kazhdan projection depends, as everywhere in this development, on a choice
of Kazhdan set: `KazhdanData` is that choice, and `exists_kazhdanData` produces
one from property (T).  No claim is made that different choices give the same
projection.
-/

namespace GroupApproximation
namespace MaximalCStarKazhdanProjection

open AbstractSpectralGap CStarSpectralProjection KazhdanProjectionAbsorption
open UltraproductKazhdanProjection

noncomputable section

universe u v

/-! ## The Kazhdan datum at the universe of `Cmax(Λ)` -/

/-- A Kazhdan set for `Λ` together with its constant, at the representation
universe where `Cmax(Λ)` lives.

`Cmax(Λ)` is a `Type (u + 1)` for `Λ : Type u`, so the Kazhdan pair has to hold
for representations on Hilbert spaces in `Type (u + 1)`.  That is free:
`HasKazhdanPropertyT.liftUniverse` raises property (T) from the universe of the
group, and `exists_kazhdanData` performs the lift. -/
structure KazhdanData (Λ : Type u) [Group Λ] where
  /-- The finite symmetric generating set averaged over. -/
  S : Finset Λ
  /-- The Kazhdan constant. -/
  kappa : ℝ
  /-- The Kazhdan pair, at the universe of the maximal algebra. -/
  kazhdan : IsKazhdanPair.{u, u + 1} Λ S kappa
  /-- The identity belongs to the averaging set. -/
  one_mem : (1 : Λ) ∈ S
  /-- The averaging set is symmetric. -/
  symm : ∀ γ ∈ S, γ⁻¹ ∈ S
  /-- The averaging set generates the group. -/
  generates : Subgroup.closure (S : Set Λ) = ⊤

/-- **Property (T) supplies a Kazhdan datum.**  The finite symmetric generating
set is `KazhdanFiniteGeneration.exists_symmetric_generating_finset`, the
constant on that set is `KazhdanGenerators.exists_pair_on_generators`, and the
universe of the maximal algebra is reached by `HasKazhdanPropertyT.liftUniverse`
— the direction of universe transfer that holds with no hypothesis. -/
theorem exists_kazhdanData (Λ : Type u) [Group Λ]
    (hT : HasKazhdanPropertyT.{u, u} Λ) : Nonempty (KazhdanData Λ) := by
  obtain ⟨S, hone, hsymm, hgen⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset Λ hT
  obtain ⟨delta, hdelta⟩ :=
    KazhdanGenerators.exists_pair_on_generators
      (hT.liftUniverse : HasKazhdanPropertyT.{u, u + 1} Λ) S hsymm hgen
  exact ⟨{ S := S
           kappa := delta
           kazhdan := hdelta
           one_mem := hone
           symm := hsymm
           generates := hgen }⟩

namespace KazhdanData

variable {Λ : Type u} [Group Λ] (K : KazhdanData Λ)

/-! ## The Kazhdan projection inside `Cmax(Λ)` -/

/-- The orbit average `|S|⁻¹ Σ_{s ∈ S} u_s` of the canonical unitaries, inside
the maximal group `C*`-algebra. -/
def average : MaximalGroupCStar Λ :=
  unitaryAverage (maximalGroupCStarUnitaryHom Λ) K.S

/-- The printed spectral rate `1 - κ²/(2|S|)`. -/
def rate : ℝ := 1 - K.kappa ^ 2 / (2 * K.S.card)

/-- **The Kazhdan projection of `Cmax(Λ)`**: the spectral projection of the
orbit average at the isolated spectral point `1`, which is the manuscript's
definition of the Kazhdan projection. -/
def projection : MaximalGroupCStar Λ :=
  spectralProjection K.average K.rate

theorem rate_lt_one : K.rate < 1 := by
  have hkappa : 0 < K.kappa := K.kazhdan.1
  have hcardNat : 0 < K.S.card := Finset.card_pos.mpr ⟨1, K.one_mem⟩
  have hcard : (0 : ℝ) < K.S.card := by exact_mod_cast hcardNat
  have hq : 0 < K.kappa ^ 2 / (2 * (K.S.card : ℝ)) :=
    div_pos (pow_pos hkappa 2) (by linarith)
  show (1 : ℝ) - K.kappa ^ 2 / (2 * (K.S.card : ℝ)) < 1
  linarith

theorem isSelfAdjoint_average : IsSelfAdjoint K.average :=
  isSelfAdjoint_unitaryAverage (maximalGroupCStarUnitaryHom Λ) K.symm

/-- **The Kazhdan spectral gap inside `Cmax(Λ)`.**  Every real spectral value of
the orbit average other than `1` is at most the printed rate.

This is the step that converts the representation-independent Hilbert-space
contraction of `Kazhdan/KazhdanProjection.lean` into a statement about the
maximal algebra: `unitaryAverage_spectrum_le_manuscript` extracts a genuine
eigenvector from a spectral value through a state and its GNS representation,
and the Kazhdan pair — which holds at the universe of `Cmax(Λ)` by
`KazhdanData.kazhdan` — forbids the eigenvalue. -/
theorem gap : ∀ mu ∈ spectrum ℝ K.average, mu ≤ K.rate ∨ mu = 1 := by
  letI : PartialOrder (MaximalGroupCStar Λ) :=
    CStarAlgebra.spectralOrder (MaximalGroupCStar Λ)
  letI : StarOrderedRing (MaximalGroupCStar Λ) :=
    CStarAlgebra.spectralOrderedRing (MaximalGroupCStar Λ)
  intro mu hmu
  by_cases hmu1 : mu = 1
  · exact Or.inr hmu1
  · left
    have hmuC : (mu : ℂ) ∈ spectrum ℂ K.average := by
      have h := spectrum.algebraMap_mem ℂ hmu
      rwa [show (algebraMap ℝ ℂ) mu = (mu : ℂ) by simp] at h
    exact unitaryAverage_spectrum_le_manuscript
      (maximalGroupCStarUnitaryHom Λ) K.kazhdan K.S Finset.Subset.rfl
      K.one_mem K.symm hmuC hmu1

theorem isSelfAdjoint_projection : IsSelfAdjoint K.projection :=
  isSelfAdjoint_spectralProjection K.average

theorem projection_mul_projection :
    K.projection * K.projection = K.projection :=
  isIdempotentElem_spectralProjection K.average K.isSelfAdjoint_average
    K.rate_lt_one K.gap

theorem average_mul_projection : K.average * K.projection = K.projection :=
  mul_spectralProjection K.average K.isSelfAdjoint_average K.rate_lt_one K.gap

theorem projection_mul_average : K.projection * K.average = K.projection :=
  spectralProjection_mul K.average K.isSelfAdjoint_average K.rate_lt_one K.gap

/-- **`ran p ⊆ Fix`, algebraically**: every canonical unitary of `Cmax(Λ)` fixes
the Kazhdan projection.  The second-moment argument turns two-sided absorption
by the average into `u_s p = p` for each generator, and the generating
hypothesis propagates that to the whole group. -/
theorem generator_mul_projection (gamma : Λ) :
    maximalGroupCStarGenerator Λ gamma * K.projection = K.projection := by
  letI : PartialOrder (MaximalGroupCStar Λ) :=
    CStarAlgebra.spectralOrder (MaximalGroupCStar Λ)
  letI : StarOrderedRing (MaximalGroupCStar Λ) :=
    CStarAlgebra.spectralOrderedRing (MaximalGroupCStar Λ)
  have hfix := unitary_mul_eq_of_average_absorbs
    (maximalGroupCStarUnitaryHom Λ) K.symm K.isSelfAdjoint_projection
    K.projection_mul_projection K.average_mul_projection
    K.projection_mul_average
  have hgamma : gamma ∈ Subgroup.closure (K.S : Set Λ) := by
    rw [K.generates]
    trivial
  exact unitary_mul_eq_of_closure (maximalGroupCStarUnitaryHom Λ) hfix hgamma

/-- The resolvent factorisation of the complement of the Kazhdan projection,
inside `Cmax(Λ)`.  This is the only place the spectral gap is spent after the
projection has been built, and it is what travels to `B` along a
`⋆`-homomorphism. -/
theorem one_sub_projection_eq :
    (1 : MaximalGroupCStar Λ) - K.projection
      = cfc (gapResolvent K.rate) K.average
        * ((1 : MaximalGroupCStar Λ) - K.average) :=
  one_sub_spectralProjection_eq K.average K.isSelfAdjoint_average
    K.rate_lt_one K.gap

end KazhdanData

/-! ## Conjugated absorption from an abstract resolvent factorisation

`KazhdanProjectionAbsorption.conjugated_projection_absorbs` states the same
implication for a projection that is *literally* `cfc (gapIndicator c) m`.  The
image of such a projection under a `⋆`-homomorphism need not be presented in
that form, but its complement still factors through `1 - m`; that factorisation
is all the argument uses, so it is what is assumed here. -/

section Absorption

variable {B : Type v} [CStarAlgebra B]

/-- **Conjugated absorption, from a factorisation of the complement.**  If
`1 - p = r (1 - m)` for some `r`, `u` is a unitary, and the conjugated element
`u m u*` absorbs `p`, then so does the conjugated projection `u p u*`.

The proof is that of
`KazhdanProjectionAbsorption.conjugated_projection_absorbs` with the
functional-calculus factor replaced by the abstract `r`: the hypothesis forces
`(1 - m) (u* p) = 0`, and the factorisation then annihilates `p` against
`1 - u p u*`. -/
theorem conj_absorbs_of_factorisation {m p r u : B}
    (hres : (1 : B) - p = r * ((1 : B) - m))
    (h1 : star u * u = 1) (h2 : u * star u = 1)
    (hmp : (u * m * star u) * p = p) :
    (u * p * star u) * p = p := by
  have hx : ((1 : B) - m) * (star u * p) = 0 := by
    have hb : u * (((1 : B) - m) * (star u * p))
        = ((1 : B) - u * m * star u) * p := by
      rw [sub_mul, sub_mul, one_mul, one_mul, mul_sub]
      congr 1
      · rw [← mul_assoc, h2, one_mul]
      · rw [← mul_assoc, ← mul_assoc]
    have ha : u * (((1 : B) - m) * (star u * p)) = 0 := by
      rw [hb, sub_mul, one_mul, hmp, sub_self]
    have hc := congrArg (fun z => star u * z) ha
    rw [← mul_assoc, h1, one_mul, mul_zero] at hc
    exact hc
  have hqp : ((1 : B) - u * p * star u) * p = 0 := by
    have hone : (1 : B) - u * p * star u = u * ((1 : B) - p) * star u := by
      rw [mul_sub, sub_mul, mul_one, h2]
    rw [hone, hres]
    have hassoc : u * (r * ((1 : B) - m)) * star u * p
        = u * r * (((1 : B) - m) * (star u * p)) := by
      noncomm_ring
    rw [hassoc, hx, mul_zero]
  rw [sub_mul, one_mul] at hqp
  exact (sub_eq_zero.mp hqp).symm

end Absorption

/-! ## The image of the Kazhdan projection in an arbitrary target -/

section Image

variable {Λ : Type u} [Group Λ] {B : Type v} [CStarAlgebra B]

/-- The image of the orbit average is the orbit average of the image
representation.  Only `map_smul` and `map_sum` are used. -/
theorem image_average (K : KazhdanData Λ) (pi : Λ →* unitary B)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B)
    (hf : ∀ gamma : Λ, f (maximalGroupCStarGenerator Λ gamma) = (pi gamma : B)) :
    f K.average = unitaryAverage pi K.S := by
  have hsum : ∑ gamma ∈ K.S, f (maximalGroupCStarGenerator Λ gamma)
      = ∑ gamma ∈ K.S, ((pi gamma : unitary B) : B) :=
    Finset.sum_congr rfl fun gamma _ => hf gamma
  show f (((K.S.card : ℂ))⁻¹ • ∑ gamma ∈ K.S,
      maximalGroupCStarGenerator Λ gamma)
    = ((K.S.card : ℂ))⁻¹ • ∑ gamma ∈ K.S, ((pi gamma : unitary B) : B)
  rw [map_smul, map_sum, hsum]

/-- `P* = P`. -/
theorem isSelfAdjoint_image (K : KazhdanData Λ)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B) : IsSelfAdjoint (f K.projection) := by
  show star (f K.projection) = f K.projection
  rw [← map_star, K.isSelfAdjoint_projection.star_eq]

/-- `P² = P`. -/
theorem image_mul_image (K : KazhdanData Λ)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B) :
    f K.projection * f K.projection = f K.projection := by
  rw [← map_mul, K.projection_mul_projection]

/-- `M P = P`, with `M` the image of the orbit average. -/
theorem image_average_mul_image (K : KazhdanData Λ)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B) :
    f K.average * f K.projection = f K.projection := by
  rw [← map_mul, K.average_mul_projection]

/-- **`ran P ⊆ Fix π(Λ)`, algebraically.**  Every `π(γ)` fixes `P`. -/
theorem rep_mul_image (K : KazhdanData Λ) (pi : Λ →* unitary B)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B)
    (hf : ∀ gamma : Λ, f (maximalGroupCStarGenerator Λ gamma) = (pi gamma : B))
    (gamma : Λ) :
    ((pi gamma : unitary B) : B) * f K.projection = f K.projection := by
  rw [← hf gamma, ← map_mul, K.generator_mul_projection gamma]

/-- The resolvent factorisation, transported to the target. -/
theorem one_sub_image_eq (K : KazhdanData Λ)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B) :
    (1 : B) - f K.projection
      = f (cfc (gapResolvent K.rate) K.average) * ((1 : B) - f K.average) := by
  have h := congrArg f K.one_sub_projection_eq
  rw [map_sub, map_one, map_mul, map_sub, map_one] at h
  exact h

/-- **The printed computation, algebraically.**  If `U π(γ) U*` always lies in
`π(Λ)`, then the conjugated orbit average absorbs `P`, because each
`U π(γ) U* = π(δ)` fixes `P`. -/
theorem conj_average_mul_image (K : KazhdanData Λ) (pi : Λ →* unitary B)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B)
    (hf : ∀ gamma : Λ, f (maximalGroupCStarGenerator Λ gamma) = (pi gamma : B))
    (U : B)
    (hcomp : ∀ gamma : Λ, ∃ delta : Λ,
      U * ((pi gamma : unitary B) : B) * star U
        = ((pi delta : unitary B) : B)) :
    (U * f K.average * star U) * f K.projection = f K.projection := by
  classical
  have hcard : ((K.S.card : ℂ)) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, K.one_mem⟩
  have havg : f K.average = unitaryAverage pi K.S := image_average K pi f hf
  have hconj : U * f K.average * star U
      = ((K.S.card : ℂ))⁻¹ • ∑ gamma ∈ K.S,
          (U * ((pi gamma : unitary B) : B) * star U) := by
    rw [havg]
    unfold unitaryAverage
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hconj, smul_mul_assoc, Finset.sum_mul]
  have hterm : ∀ gamma ∈ K.S,
      (U * ((pi gamma : unitary B) : B) * star U) * f K.projection
        = f K.projection := by
    intro gamma _
    obtain ⟨delta, hdelta⟩ := hcomp gamma
    rw [hdelta]
    exact rep_mul_image K pi f hf delta
  rw [Finset.sum_congr rfl hterm, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℂ K.S.card (f K.projection), smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/-- **`P ≤ U P U*`, in absorption form.**  The conjugated *projection* absorbs
`P` because the conjugated *average* does, by the transported resolvent
factorisation. -/
theorem conj_image_mul_image (K : KazhdanData Λ) (pi : Λ →* unitary B)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B)
    (hf : ∀ gamma : Λ, f (maximalGroupCStarGenerator Λ gamma) = (pi gamma : B))
    (U : B) (hU : star U * U = 1) (hU' : U * star U = 1)
    (hcomp : ∀ gamma : Λ, ∃ delta : Λ,
      U * ((pi gamma : unitary B) : B) * star U
        = ((pi delta : unitary B) : B)) :
    (U * f K.projection * star U) * f K.projection = f K.projection :=
  conj_absorbs_of_factorisation (one_sub_image_eq K f) hU hU'
    (conj_average_mul_image K pi f hf U hcomp)

/-- The conjugate `U P U*` is self-adjoint. -/
theorem isSelfAdjoint_conj_image (K : KazhdanData Λ)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B) (U : B) :
    IsSelfAdjoint (U * f K.projection * star U) := by
  show star (U * f K.projection * star U) = U * f K.projection * star U
  rw [star_mul, star_mul, star_star, (isSelfAdjoint_image K f).star_eq,
    mul_assoc]

/-- The adjoint form of `conj_image_mul_image`. -/
theorem image_mul_conj_image (K : KazhdanData Λ) (pi : Λ →* unitary B)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B)
    (hf : ∀ gamma : Λ, f (maximalGroupCStarGenerator Λ gamma) = (pi gamma : B))
    (U : B) (hU : star U * U = 1) (hU' : U * star U = 1)
    (hcomp : ∀ gamma : Λ, ∃ delta : Λ,
      U * ((pi gamma : unitary B) : B) * star U
        = ((pi delta : unitary B) : B)) :
    f K.projection * (U * f K.projection * star U) = f K.projection := by
  have h := congrArg star (conj_image_mul_image K pi f hf U hU hU' hcomp)
  rw [star_mul, (isSelfAdjoint_image K f).star_eq,
    (isSelfAdjoint_conj_image K f U).star_eq] at h
  exact h

/-! ### The printed side: `U* P U`

Conjugating the two identities above by `U*` and `U` turns `P ≤ U P U*` into
the printed `U* P U ≤ P`, again in absorption form. -/

/-- `(U* P U) P = U* P U`. -/
theorem star_conj_image_mul_image (K : KazhdanData Λ) (pi : Λ →* unitary B)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B)
    (hf : ∀ gamma : Λ, f (maximalGroupCStarGenerator Λ gamma) = (pi gamma : B))
    (U : B) (hU : star U * U = 1) (hU' : U * star U = 1)
    (hcomp : ∀ gamma : Λ, ∃ delta : Λ,
      U * ((pi gamma : unitary B) : B) * star U
        = ((pi delta : unitary B) : B)) :
    (star U * f K.projection * U) * f K.projection
      = star U * f K.projection * U := by
  have h : star U * (f K.projection * (U * f K.projection * star U)) * U
      = star U * f K.projection * U :=
    congrArg (fun x : B => star U * x * U)
      (image_mul_conj_image K pi f hf U hU hU' hcomp)
  have step : star U * (f K.projection * (U * f K.projection * star U)) * U
      = (star U * f K.projection * U) * f K.projection * (star U * U) := by
    noncomm_ring
  rw [hU, mul_one] at step
  exact step.symm.trans h

/-- `P (U* P U) = U* P U`. -/
theorem image_mul_star_conj_image (K : KazhdanData Λ) (pi : Λ →* unitary B)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B)
    (hf : ∀ gamma : Λ, f (maximalGroupCStarGenerator Λ gamma) = (pi gamma : B))
    (U : B) (hU : star U * U = 1) (hU' : U * star U = 1)
    (hcomp : ∀ gamma : Λ, ∃ delta : Λ,
      U * ((pi gamma : unitary B) : B) * star U
        = ((pi delta : unitary B) : B)) :
    f K.projection * (star U * f K.projection * U)
      = star U * f K.projection * U := by
  have h : star U * ((U * f K.projection * star U) * f K.projection) * U
      = star U * f K.projection * U :=
    congrArg (fun x : B => star U * x * U)
      (conj_image_mul_image K pi f hf U hU hU' hcomp)
  have step : star U * ((U * f K.projection * star U) * f K.projection) * U
      = (star U * U) * f K.projection * (star U * f K.projection * U) := by
    noncomm_ring
  rw [hU, one_mul] at step
  exact step.symm.trans h

/-! ### Star projections -/

theorem isStarProjection_image (K : KazhdanData Λ)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B) :
    IsStarProjection (f K.projection) := by
  constructor
  · show f K.projection * f K.projection = f K.projection
    exact image_mul_image K f
  · exact isSelfAdjoint_image K f

theorem isStarProjection_star_conj_image (K : KazhdanData Λ)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B) (U : B) (hU' : U * star U = 1) :
    IsStarProjection (star U * f K.projection * U) := by
  constructor
  · show (star U * f K.projection * U) * (star U * f K.projection * U)
        = star U * f K.projection * U
    have hrw : (star U * f K.projection * U) * (star U * f K.projection * U)
        = star U * (f K.projection * (U * star U) * f K.projection) * U := by
      noncomm_ring
    rw [hrw, hU', mul_one, image_mul_image K f]
  · show star (star U * f K.projection * U) = star U * f K.projection * U
    rw [star_mul, star_mul, star_star, (isSelfAdjoint_image K f).star_eq,
      mul_assoc]

/-! ### The genuine Loewner inequality -/

section Order

variable [PartialOrder B] [StarOrderedRing B]

/-- **`lem:kazhdan-projection-order`, with `P` the image of the Kazhdan
projection of `Cmax(Λ)`.**

`f` is any `⋆`-homomorphism `Cmax(Λ) → B` carrying the canonical unitaries to
`π` — by `maximalGroupCStar_existsUnique_lift_allUniverses` exactly one such
exists for every `π`, in every universe — and `P = f p` is the image of the
Kazhdan projection.  Under the printed inclusion `U π(Λ) U* ⊆ π(Λ)` the printed
inequality `U* P U ≤ P` holds in the Loewner order of `B`.

For star projections the Loewner order is the absorption identity
`Q P = Q` (`IsStarProjection.le_iff_mul_eq_left`), so the whole content is
`star_conj_image_mul_image`. -/
theorem star_conj_image_le (K : KazhdanData Λ) (pi : Λ →* unitary B)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B)
    (hf : ∀ gamma : Λ, f (maximalGroupCStarGenerator Λ gamma) = (pi gamma : B))
    (U : B) (hU : star U * U = 1) (hU' : U * star U = 1)
    (hcomp : ∀ gamma : Λ, ∃ delta : Λ,
      U * ((pi gamma : unitary B) : B) * star U
        = ((pi delta : unitary B) : B)) :
    star U * f K.projection * U ≤ f K.projection :=
  ((isStarProjection_star_conj_image K f U hU').le_iff_mul_eq_left
      (isStarProjection_image K f)).mpr
    (star_conj_image_mul_image K pi f hf U hU hU' hcomp)

end Order

/-! ### The compression hypothesis, in the unitary group of `B` -/

/-- The manuscript's `U π(Λ) U* ⊆ π(Λ)`, written with `U` a member of the
unitary group of `B`, read as an identity between elements of `B`. -/
theorem compresses_coe (pi : Λ →* unitary B) (U : unitary B)
    (hcomp : ∀ gamma : Λ, ∃ delta : Λ, U * pi gamma * U⁻¹ = pi delta)
    (gamma : Λ) :
    ∃ delta : Λ,
      ((U : unitary B) : B) * ((pi gamma : unitary B) : B)
          * star ((U : unitary B) : B)
        = ((pi delta : unitary B) : B) := by
  obtain ⟨delta, hdelta⟩ := hcomp gamma
  exact ⟨delta, congrArg (fun x : unitary B => (x : B)) hdelta⟩

/-! ### Agreement with the spectral projection built in the target

The two existing consumers of the Kazhdan projection construct it inside the
algebra where the inequality is asserted.  Whenever the same gap is available
there — which is exactly what those consumers assume — the image of the `Cmax`
projection is that element, so the results proved here and the results proved by
`Sofic/UltraproductKazhdanProjection.lean` are about the same `P`.

The proof needs no functional-calculus naturality: each of the two projections
has a complement that factors through `1 - M`, and each factorisation kills the
other projection. -/

/-- **The image of the `Cmax` Kazhdan projection is the spectral Kazhdan
projection of the target.** -/
theorem image_eq_spectralProjection (K : KazhdanData Λ) (pi : Λ →* unitary B)
    (f : MaximalGroupCStar Λ →⋆ₐ[ℂ] B)
    (hf : ∀ gamma : Λ, f (maximalGroupCStarGenerator Λ gamma) = (pi gamma : B))
    (hgap : ∀ mu ∈ spectrum ℝ (unitaryAverage pi K.S), mu ≤ K.rate ∨ mu = 1) :
    f K.projection = spectralProjection (unitaryAverage pi K.S) K.rate := by
  set M : B := unitaryAverage pi K.S
  have hMsa : IsSelfAdjoint M := isSelfAdjoint_unitaryAverage pi K.symm
  have hP2sa : IsSelfAdjoint (spectralProjection M K.rate) :=
    isSelfAdjoint_spectralProjection M
  have havg : f K.average = M := image_average K pi f hf
  have hzero1 : ((1 : B) - M) * f K.projection = 0 := by
    have hMP1 : M * f K.projection = f K.projection := by
      rw [← havg]
      exact image_average_mul_image K f
    rw [sub_mul, one_mul, hMP1, sub_self]
  have hzero2 : ((1 : B) - M) * spectralProjection M K.rate = 0 := by
    have hMP2 : M * spectralProjection M K.rate = spectralProjection M K.rate :=
      mul_spectralProjection M hMsa K.rate_lt_one hgap
    rw [sub_mul, one_mul, hMP2, sub_self]
  have h21 : spectralProjection M K.rate * f K.projection = f K.projection := by
    have h : ((1 : B) - spectralProjection M K.rate) * f K.projection = 0 := by
      rw [one_sub_spectralProjection_eq M hMsa K.rate_lt_one hgap, mul_assoc,
        hzero1, mul_zero]
    rw [sub_mul, one_mul] at h
    exact (sub_eq_zero.mp h).symm
  have h12 : f K.projection * spectralProjection M K.rate
      = spectralProjection M K.rate := by
    have h : ((1 : B) - f K.projection) * spectralProjection M K.rate = 0 := by
      rw [one_sub_image_eq K f, havg, mul_assoc, hzero2, mul_zero]
    rw [sub_mul, one_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hstar := congrArg star h21
  rw [star_mul, (isSelfAdjoint_image K f).star_eq, hP2sa.star_eq] at hstar
  exact hstar.symm.trans h12

end Image

end

end MaximalCStarKazhdanProjection

/-! ## The manuscript endpoint -/

namespace Manuscript
namespace OneSidedMFRadical

open MaximalCStarKazhdanProjection

universe u v

/-- **Lemma `lem:kazhdan-projection-order`, as one closed proposition, with `P`
the image of the Kazhdan projection under `C*_max(L) → B`.**

> Let `L` have property (T), let `B` be a unital `C*`-algebra, and let
> `π : L → U(B)` be a homomorphism.  Denote by `P ∈ B` the image of the Kazhdan
> projection under the extension `C*_max(L) → B`.  If `U ∈ U(B)` satisfies
> `U π(L) U* ⊆ π(L)`, then `U* P U ≤ P`.

The proposition names a single `p ∈ C*_max(L)` — self-adjoint, idempotent, and
fixed by every canonical unitary, so it is the Kazhdan projection and not merely
some projection — and then asserts, for every unital `C*`-algebra `B` in every
universe:

* the extension exists and is unique (`prop:maximal-cstar`, which is what makes
  "the image of the Kazhdan projection" a definite description);
* every extension `f` carries `p` to an element satisfying the printed
  inequality.

`Analysis/KazhdanProjectionOneSidedOrder.lean` proves the same lemma on a
Hilbert space, where `P` is the orthogonal projection onto `Fix π(L)` by
hypothesis; this endpoint is the abstract-algebra half, where `P` is the image
of a single element of `C*_max(L)` and no faithful representation of `B` is
used. -/
def MaximalCStarKazhdanProjectionOrder : Prop :=
  ∀ (L : Type u) [Group L], HasKazhdanPropertyT.{u, u} L →
    ∃ p : MaximalGroupCStar L,
      IsSelfAdjoint p ∧ p * p = p ∧
        (∀ l : L, maximalGroupCStarGenerator L l * p = p) ∧
        ∀ (B : Type v) [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
          (pi : L →* unitary B),
          (∃! f : MaximalGroupCStar L →⋆ₐ[ℂ] B,
            ∀ l : L, f (maximalGroupCStarGenerator L l) = (pi l : B)) ∧
          ∀ U : unitary B,
            (∀ l : L, ∃ l' : L, U * pi l * U⁻¹ = pi l') →
            ∀ f : MaximalGroupCStar L →⋆ₐ[ℂ] B,
              (∀ l : L, f (maximalGroupCStarGenerator L l) = (pi l : B)) →
              star ((U : unitary B) : B) * f p * ((U : unitary B) : B) ≤ f p

/-- Closed proof of `lem:kazhdan-projection-order` with `P` the image of the
Kazhdan projection of `C*_max(L)`. -/
theorem manuscriptMaximalCStarKazhdanProjectionOrder :
    MaximalCStarKazhdanProjectionOrder.{u, v} := by
  intro L _ hT
  obtain ⟨K⟩ := exists_kazhdanData L hT
  refine ⟨K.projection, K.isSelfAdjoint_projection,
    K.projection_mul_projection, K.generator_mul_projection, ?_⟩
  intro B _ _ _ pi
  refine ⟨maximalGroupCStar_existsUnique_lift_allUniverses L pi, ?_⟩
  intro U hcomp f hf
  exact star_conj_image_le K pi f hf ((U : unitary B) : B) U.property.1
    U.property.2 (compresses_coe pi U hcomp)

end OneSidedMFRadical
end Manuscript

end GroupApproximation
