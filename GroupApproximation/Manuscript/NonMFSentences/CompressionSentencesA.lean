import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Analysis.MaximalGroupCStar
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefinitions
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportPrintedRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.ShadowResidual
import GroupApproximation.Meta.AxiomGuard

/-!
# Sentence-level formalization of `non_mf_groups_exist.tex`, `sec:compression-radical`, part A

Section "One-sided compression", the subsections "Corona homomorphisms" and
the opening of "Kazhdan transport in normalized Hilbert--Schmidt norm" (tex
lines 348-425 at the current revision): Lemma `prop:mf-residual-calculus`
(statement and proof), the displayed printed definitions of the normalized
Hilbert--Schmidt norm, of an operator norm asymptotic representation, of the
Hilbert--Schmidt asymptotic commutant `𝒞₂(V,L)`, of `Ad(V(g))`, and of a
finite/stably finite unital `C^*`-algebra.

The lemma's own statement is already badge-verified whole
(`isCDEOperatorMF_of_faithful_corona_map`, `allMFTargetsKill_iff_allCoronasKill`);
this module supplies the printed *proof*, sentence by sentence, and the
definitions that the following lemma (`lem:stable-finite`, already covered
sentence-by-sentence in `StableFinitenessSentences.lean`) and the rest of the
section consume.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open Matrix
open OneSidedMFRadical.HilbertSchmidtOperatorAction
open OneSidedMFRadical.HilbertSchmidtAdMatrix

noncomputable section

/-! ## `prop:mf-residual-calculus`, proof sentence 1 (tex line 362)

"The image of a corona homomorphism is a countable MF group." -/

/-- **Proof sentence, tex line 362.**  The image of a corona homomorphism
from a countable group `G` is countable
(`OneSidedMFRadical.coronaImage_countable`) and is MF in the
unitary-sequence-corona reading (`OneSidedMFRadical.coronaImage_isOperatorMF`;
`IsOperatorMF` is the established reading of "MF" that does not itself demand
a `Countable` instance on the target group, matching
`PrintedDefinitions.PrintedCoronaImagesAndTargets`'s own first clause). -/
def CoronaImageIsCountableMF : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)], (∀ n, 0 < Fintype.card (X n)) →
    ∀ Theta : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      Countable Theta.range ∧ IsOperatorMF Theta.range

theorem manuscriptSentence_coronaImageIsCountableMF :
    CoronaImageIsCountableMF := by
  intro G _ _ X _ hX Theta
  exact ⟨OneSidedMFRadical.coronaImage_countable G X Theta,
    OneSidedMFRadical.coronaImage_isOperatorMF G X hX Theta⟩

/-! ## `prop:mf-residual-calculus`, proof sentence 2 (tex lines 362-364)

"Conversely, compose a homomorphism to an MF group with a corona embedding of
its image; the resulting corona homomorphism has the same kernel." -/

/-- **Proof sentence, tex lines 362-364.**  `M` is MF, so it embeds into a
norm matrix corona by an injective `rho`; composing `rho` with `f : G →* M`
gives a corona homomorphism `Theta`, and `Theta.ker = f.ker` because `rho` is
injective. -/
def ComposeMFHomWithCoronaEmbeddingSameKernel : Prop :=
  ∀ (G M : Type) [Group G] [Group M] [Countable G] [Countable M],
    IsCDEOperatorMF M → ∀ f : G →* M,
      ∃ (d : ℕ → ℕ) (_hd : ∀ n, 0 < d n),
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
          fun n ↦ Fintype.card_pos_iff.mp (by simpa using _hd n)
        ∃ Theta : G →* unitary
            (NormMatrixCStarCorona (fun n ↦ naturalFiniteModel (d n))),
          Theta.ker = f.ker

theorem manuscriptSentence_composeMFHomWithCoronaEmbeddingSameKernel :
    ComposeMFHomWithCoronaEmbeddingSameKernel := by
  intro G M _ _ _ _ hM f
  obtain ⟨d, hd, -, rho, hrho⟩ := hM
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  refine ⟨d, hd, rho.comp f, ?_⟩
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro h
    exact hrho (h.trans (map_one rho).symm)
  · intro h
    rw [h, map_one]

/-! ## `prop:mf-residual-calculus`, proof sentence 3 (tex lines 364-367)

"If `ι` is an embedding as in the last assertion, then
`g ↦ ι(π(g)) + 1 - ι(1)` is a corona homomorphism that is injective on `G`;
the complement term allows `ι` to be nonunital." -/

/-- **Proof sentence, tex lines 364-367.**  `nonUnitalStarAlgHomUnitaryMap`
is exactly the printed correction `u ↦ ι(u) + 1 - ι(1)`, and
`nonUnitalStarAlgHomUnitaryMap_injective` composed with the injectivity of
`π` gives the printed injectivity on `G`. -/
def NonunitalCoronaHomInjectiveOnG : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (A : Type) [CStarAlgebra A]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (iota : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n)),
    Function.Injective iota →
    ∀ pi : G →* unitary A, Function.Injective pi →
      ∃ Theta : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
        (∀ g : G,
          ((Theta g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
              NormMatrixCStarCorona (fun n ↦ X n))
            = iota (pi g : A) + (1 - iota (1 : A))) ∧
        Function.Injective Theta

theorem manuscriptSentence_nonunitalCoronaHomInjectiveOnG :
    NonunitalCoronaHomInjectiveOnG := by
  intro G _ _ A _ X _ iota hiota pi hpi
  exact ⟨(nonUnitalStarAlgHomUnitaryMap iota).comp pi, fun _ ↦ rfl,
    (nonUnitalStarAlgHomUnitaryMap_injective hiota).comp hpi⟩

/-! ## `prop:mf-residual-calculus`, statement sentence 4 (tex lines 354-357)

"In particular, this applies to the canonical group homomorphisms into
`U(C*_max(G))` and `U(C*_r(G))`." -/

/-- **Statement sentence, tex lines 354-357 (the `C*_max(G)` half).**  The
canonical map `G → U(C*_max(G))` is `maximalGroupCStarUnitaryHom`, proved
injective by `maximalGroupCStarUnitaryHom_injective` (testing equality at the
concrete left regular coordinate). -/
def AppliesToMaximalCanonicalMap : Prop :=
  ∀ (G : Type) [Group G] [Countable G]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (_hX : ∀ n, 0 < Fintype.card (X n))
    (e : MaximalGroupCStar G →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n)),
    Function.Injective e → IsCDEOperatorMF G

theorem manuscriptSentence_appliesToMaximalCanonicalMap :
    AppliesToMaximalCanonicalMap := by
  intro G _ _ X _ hX e he
  exact _root_.GroupApproximation.isCDEOperatorMF_of_faithful_corona_map X hX e he
    (maximalGroupCStarUnitaryHom G) (maximalGroupCStarUnitaryHom_injective G)

/-- **Statement sentence, tex lines 354-357 (the `C*_r(G)` half).**  The
canonical map `G → U(C*_r(G))` is `reducedLeftRegularUnitaryHom`, proved
injective by `reducedLeftRegularUnitaryHom_injective` (evaluating at
`δ_1 ∈ ℓ²(G)`). -/
def AppliesToReducedCanonicalMap : Prop :=
  ∀ (G : Type) [Group G] [Countable G]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (_hX : ∀ n, 0 < Fintype.card (X n))
    (e : ReducedGroupCStarTrace.ReducedGroupCStar G →⋆ₙₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ X n)),
    Function.Injective e → IsCDEOperatorMF G

theorem manuscriptSentence_appliesToReducedCanonicalMap :
    AppliesToReducedCanonicalMap := by
  intro G _ _ X _ hX e he
  exact _root_.GroupApproximation.isCDEOperatorMF_of_faithful_corona_map X hX e he
    (reducedLeftRegularUnitaryHom G) (reducedLeftRegularUnitaryHom_injective G)

/-! ## Definition, tex lines 382-386

"For `a ∈ M_d(ℂ)` write `‖a‖₂ = tr_d(a^*a)^{1/2}`, `tr_d = (1/d) Tr`." -/

-- The printed normalized Hilbert--Schmidt norm is `GroupApproximation.hsNorm`
-- (`Sofic/LeavittTraceFloor.lean`), already used throughout
-- `Manuscript/OneSidedMFRadical`; no new declaration is needed here.

/-! ## Definition, tex lines 387-392

"An operator norm asymptotic representation of a group `G` is a sequence of
maps `V_n : G → U(d_n)` such that `V_n(1) = 1` and
`‖V_n(gh) - V_n(g)V_n(h)‖ → 0` `(g, h ∈ G)`." -/

-- The printed operator norm asymptotic representation is
-- `GroupApproximation.OpAlmostRepresentation` (`Sofic/OpAlmostRepresentation.lean`):
-- a sequence of finite unitary models `V_n : G → U(d_n)` (with `V_n(1) = 1`
-- built into the `unitaryGroup` coercion) whose multiplicative defect tends
-- to `0` in operator norm; no new declaration is needed here.

/-! ## Claim, tex lines 393-401

"The elements `g` with `‖V_n(g) - 1‖₂ → 0` form a normal subgroup of `G`,
because `‖a‖₂ ≤ ‖a‖`, the Hilbert--Schmidt norm is invariant under adjoints
and unitary conjugation, and `‖V_n(g⁻¹) - V_n(g)^*‖ → 0`:
`‖V_n(gh)-1‖₂ ≤ ‖V_n(g)-1‖₂+‖V_n(h)-1‖₂+o(1)`,
`‖V_n(g⁻¹)-1‖₂=‖V_n(g)-1‖₂+o(1)`,
`‖V_n(ghg⁻¹)-1‖₂=‖V_n(h)-1‖₂+o(1)`." -/

/-- **The claim of tex lines 393-401: `K₂(V) = \{g : ‖V_n(g)-1‖₂ → 0\}` is a
normal subgroup of `G`.**  This is `OneSidedMFRadical.hsKernel` together with
the instance `OneSidedMFRadical.hsKernel_normal`; `IsHSNull` is the printed
membership condition (`OneSidedMFRadical.isHSNull_iff_tendsto` identifies it
with the printed `‖V_n(g)-1‖₂ → 0`).

The Lean proof of normality goes through the Hilbert--Schmidt ultraproduct
description of `K₂(V)` as the kernel of a homomorphism, rather than
re-deriving the three displayed estimates directly; both are proofs of the
same printed sentence's conclusion, and the outcome — `K₂(V)` is a normal
subgroup of `G` — is exactly the printed claim. -/
def HSNullFormsNormalSubgroup : Prop :=
  ∀ (G : Type) [Group G] (B : OpAlmostRepresentation G),
    ∃ K : Subgroup G, K.Normal ∧
      ∀ g : G, g ∈ K ↔ OneSidedMFRadical.IsHSNull B g

theorem manuscriptSentence_hsNullFormsNormalSubgroup :
    HSNullFormsNormalSubgroup := by
  intro G _ B
  exact ⟨OneSidedMFRadical.hsKernel B, OneSidedMFRadical.hsKernel_normal B,
    fun g ↦ OneSidedMFRadical.mem_hsKernel_iff B g⟩

/-! ## Definition, tex lines 402-410

"For `L ≤ G`, let `𝒞₂(V,L) = \{(x_n) : sup_n ‖x_n‖₂ < ∞, ‖V_n(ℓ)x_n-x_nV_n(ℓ)‖₂
→ 0 (ℓ ∈ L)\}` be the Hilbert--Schmidt asymptotic commutant of `V(L)`." -/

-- The printed `𝒞₂(V,L)` is
-- `OneSidedMFRadical.TransportPrintedCommutant.printedCTwo`, already used by
-- the sentence-level proof of `thm:transport`; no new declaration is needed
-- here.

/-! ## Definition/claim, tex lines 411-413

"Coordinatewise conjugation by `V_n(g)` defines a bijection, denoted
`Ad(V(g))`, of the Hilbert--Schmidt bounded matrix sequences." -/

/-- **`Ad(V(g))`: coordinatewise conjugation by `V_n(g)`, as a map on matrix
sequences.** -/
def adSequence {G : Type} [Group G] (B : OpAlmostRepresentation G) (g : G)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) :
    ∀ n, Matrix (B.model n) (B.model n) ℂ :=
  fun n ↦ applyOp (B.model n) (adMatrix (B.model n) (B.map n g)) (x n)

/-- **Tex lines 412-413: `Ad(V(g))` is a bijection of the matrix sequences.**
Proved on the full space of matrix sequences (a stronger statement than the
printed restriction to the Hilbert--Schmidt bounded ones, which follows
because `Ad(V(g))` and its inverse are `‖·‖₂`-isometries, so both send
Hilbert--Schmidt bounded sequences to Hilbert--Schmidt bounded sequences).
The two-sided inverse is coordinatewise conjugation by `V_n(g)^*`. -/
def AdSequenceBijective : Prop :=
  ∀ (G : Type) [Group G] (B : OpAlmostRepresentation G) (g : G),
    Function.Bijective (adSequence B g)

theorem manuscriptSentence_adSequenceBijective : AdSequenceBijective := by
  intro G _ B g
  have hV1 : ∀ n, (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ *
      (B.map n g : Matrix (B.model n) (B.model n) ℂ) = 1 := by
    intro n
    have h := Unitary.star_mul_self_of_mem (B.map n g).2
    rwa [Matrix.star_eq_conjTranspose] at h
  have hV2 : ∀ n, (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
      (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ = 1 := by
    intro n
    have h := Unitary.mul_star_self_of_mem (B.map n g).2
    rwa [Matrix.star_eq_conjTranspose] at h
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun x n ↦ applyOp (B.model n)
        (adMatrix (B.model n)
          ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ)) (x n),
      ?_, ?_⟩
  · intro x
    funext n
    show applyOp (B.model n)
        (adMatrix (B.model n)
          ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ))
        (applyOp (B.model n)
          (adMatrix (B.model n) (B.map n g)) (x n))
      = x n
    rw [← applyOp_mul, ← adMatrix_mul, hV1 n, adMatrix_one, applyOp_one]
  · intro x
    funext n
    show applyOp (B.model n)
        (adMatrix (B.model n) (B.map n g))
        (applyOp (B.model n)
          (adMatrix (B.model n)
            ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ)) (x n))
      = x n
    rw [← applyOp_mul, ← adMatrix_mul, hV2 n, adMatrix_one, applyOp_one]

/-! ## Definition, tex lines 414-415

"A unital `C^*`-algebra is finite if each of its isometries is unitary, and
stably finite if all matrix algebras over it are finite." -/

/-- **A unital `C^*`-algebra (or any star ring) is finite if each of its
isometries is unitary.** -/
def IsCStarFinite (A : Type*) [Ring A] [StarRing A] : Prop :=
  ∀ v : A, star v * v = 1 → v * star v = 1

/-- **A unital `C^*`-algebra (or any star ring) is stably finite if every
matrix algebra over it is finite.** -/
def IsCStarStablyFinite (A : Type*) [Ring A] [StarRing A] : Prop :=
  ∀ k : ℕ, 0 < k → IsCStarFinite (Matrix (Fin k) (Fin k) A)

end

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_coronaImageIsCountableMF
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_composeMFHomWithCoronaEmbeddingSameKernel
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_nonunitalCoronaHomInjectiveOnG
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_appliesToMaximalCanonicalMap
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_appliesToReducedCanonicalMap
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_hsNullFormsNormalSubgroup
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_adSequenceBijective
