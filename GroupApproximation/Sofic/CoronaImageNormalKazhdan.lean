import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Sofic.KazhdanCompressionFunctorial
import GroupApproximation.Sofic.NormalKazhdanCompressionObstruction
import GroupApproximation.Sofic.OperatorMFLocalNormalization
import GroupApproximation.Sofic.WeakMFUltraproduct

/-!
# The normal-Kazhdan obstruction along the printed corona-image route

`non_mf_groups_exist.tex`, Theorem~\ref{thm:normal-kazhdan}, in
`\subsection{The normal-Kazhdan form of the obstruction}` of
`\section{The compression defect and its obstruction theorems}`
(`\label{sec:conj}`).  The manuscript is under concurrent revision, so this
module is anchored on labels rather than line numbers.

The manuscript proves the normal-Kazhdan obstruction by contradiction, along
one specific chain:

1. a corona representation `Θ` **survives** on `K` — pass to its coordinate
   model in the unitary-sequence corona (the unitary-corona lifting result);
2. the **image** `H̄ = Θ(H)` is **countable, hence MF**;
3. the MF model-equivalence result, applied along an **exhaustion of `H̄`**, gives an
   operator-norm asymptotic representation `(V_{g,n})` with separation `1`
   for fixed nontrivial elements — *separated finite models*;
4. the **moving corner** built on those models contradicts the
   Hilbert--Schmidt invisibility of the image defect subgroup.

`KazhdanCompressionCore.normalKazhdan_le_normMFResidual` proves a *more
general* statement (membership in the universal norm-MF residual, quantified
over every operator-norm matrix ultraproduct) and reaches the corona
conclusion only afterwards, through the operator-MF/weak-MF abstraction
layer.  That theorem is correct and stays where it is.  This file supplies
the declaration whose *proof route* is the printed one: one lemma per link,
named `nk_01_…` through `nk_04_…`, assembled by `nk_05_assembly` and
presented in the manuscript's literal natural-dimension corona language by
`manuscriptNormalKazhdanObstructionViaCoronaImage`.

The moving-corner argument itself is **not** reproved here: step 4 is the
existing `InternalRadicalGap` corner machinery, driven directly by the
separated models produced in step 3 rather than by a re-derived weak-MF
predicate.

Countability of the ambient group `H` is exactly the manuscript hypothesis
("Let `H` be a countable group…"); it is what makes the image `H̄` countable
in step 2 and what supplies the exhaustion in step 3.  Countability of the
Kazhdan source `Λ` is part of Definition~\ref{def:pattern} and is carried by
the manuscript-facing statement even though the proof never uses it; the
internal steps below do not assume it.

The subgroup `N_comp` of Definition~\ref{def:pattern} — the normal closure in
`H` of the commutators `[d, ι(λ)]` with `d = t c t⁻¹` — is
`KazhdanCompressionCore.defectNormal`, so the printed containment
`K ⊆ N_comp` is `hK : K ≤ C.defectNormal` throughout.
-/

namespace GroupApproximation
namespace CoronaImageNormalKazhdan

open Filter
open scoped commutatorElement

section Route

variable {Gamma H : Type} [Group Gamma] [Group H]

/-! ## Step 1 — the surviving corona representation -/

/-- **Step 1 (surviving corona representation).**  "Suppose a corona
representation `Θ` is nontrivial on `K`."

A corona representation is a homomorphism into `U(𝒬)` for the genuine
norm-matrix C-star corona `𝒬`.  the unitary-corona lifting result — the polar
correction isomorphism `κ_{(d_n)}` of the manuscript, here
`normMatrixCoronaUnitaryEquiv` — canonically identifies it with its
*coordinate model*, a homomorphism into the unitary-sequence corona, and the
identification is faithful, so the coordinate model survives on the same
element. -/
theorem nk_01_surviving_corona_representation
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (Theta : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    {k : H} (hk : Theta k ≠ 1) :
    ∃ sigma : H →* NormMatrixCoronaUnitary X,
      (normMatrixCoronaUnitaryEquiv X).toMonoidHom.comp sigma = Theta ∧
        sigma k ≠ 1 := by
  refine ⟨(normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp Theta,
    MonoidHom.ext fun x ↦ ?_, ?_⟩
  · simp
  · intro hone
    apply hk
    apply (normMatrixCoronaUnitaryEquiv X).symm.injective
    simpa using hone

/-! ## Step 2 — the countable MF image -/

/-- **Step 2 (countable MF image).**  "Its image `H̄ = Θ(H)` is countable,
hence MF."

Countability is inherited from the ambient group because the range
restriction is surjective; MF-ness is immediate because `H̄` sits inside the
very corona that received the surviving representation, so its inclusion is
an injective corona representation on the same coordinate sequence. -/
theorem nk_02_countable_mf_image [Countable H]
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (sigma : H →* NormMatrixCoronaUnitary X) :
    Countable sigma.range ∧ IsOperatorMF sigma.range :=
  ⟨Function.Surjective.countable sigma.rangeRestrict_surjective,
    ⟨X, hX, sigma.range.subtype, Subtype.val_injective⟩⟩

/-! ## Step 3 — the separated finite models -/

/-- **Step 3 (separated finite models).**  "The MF model-equivalence result,
applied along an exhaustion of `H̄`, gives an operator-norm asymptotic
representation `(V_{g,n})` in which every fixed nontrivial element eventually
stays at operator-norm distance at least `1` from the identity."

The first component is the result's separation-normalization clause: local
operator-norm models with separation constant exactly `1`.  The second is the
sequence `(V_{g,n})` itself, obtained from
those local models by exhausting the countable group `H̄` — the finite test
sets `F n` of `exists_weakMFApproximation` are that exhaustion, and the
resulting `WeakMFApproximation` carries the separation constant `1` of the
first component together with the asymptotic multiplicativity. -/
theorem nk_03_separated_finite_models {Hbar : Type} [Group Hbar]
    [Countable Hbar] (hMF : IsOperatorMF Hbar) :
    IsNormApproximable Hbar 1 ∧ Nonempty (WeakMFApproximation Hbar) := by
  have hone : IsNormApproximable Hbar 1 :=
    OperatorMFLocalNormalization.isNormApproximable_one hMF
  exact ⟨hone, exists_weakMFApproximation (by norm_num : (0 : ℝ) < 1) hone⟩

/-! ## Step 4 — the moving corner -/

/-- **Step 4 (moving corner).**  The three closing paragraphs of the printed
proof — *the moving spectral subspace*, *the tracial deficit on the corner*,
*compression*, and *the contradiction* — run on the separated finite models
produced by step 3.

`InternalRadicalGap.exists_setup` fixes the finite symmetric generating
Kazhdan set `S ⊆ K̄` with constant `ε₀` and the spectral cut
`θ = 1 - ε₀²/(4|S|)`; `exists_ambientMovingCornerSchedule` schedules the
coordinates on which the moving subspace is nonzero and the ambient Gram
defects are controlled, which is where normality makes the cut asymptotically
central; `normalCornerOpAlmostRepresentation` is the compressed,
polar-corrected operator-norm asymptotic representation of all of `H̄` on the
moving corner.  On that corner every element of the image defect subgroup is
Hilbert--Schmidt invisible, in particular the surviving generator `s₀`
supplied by `exists_generator_hyperlinearHom_ne_one`, contradicting its
tracial deficit.

Nothing in the corner argument is reproved here; only its input has changed
from a weak-MF predicate to the models of step 3. -/
theorem nk_04_moving_corner {Hbar : Type} [Group Hbar] [Countable Hbar]
    (Cbar : KazhdanCompressionCore Gamma Hbar)
    (Kbar : Subgroup Hbar) [Kbar.Normal] [Nontrivial Kbar]
    (hT : HasKazhdanPropertyT.{0, 0} Kbar)
    (hK : Kbar ≤ Cbar.defectNormal)
    (A : WeakMFApproximation Hbar) :
    False := by
  classical
  obtain ⟨Dgap⟩ := InternalRadicalGap.exists_setup A Kbar hT
  obtain ⟨R⟩ := InternalRadicalGap.exists_ambientMovingCornerSchedule A Kbar Dgap
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hcof : ((U : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
    Ultrafilter.of_le Filter.cofinite
  let B : OpAlmostRepresentation Hbar :=
    KazhdanCompressionCore.normalCornerOpAlmostRepresentation R
  let S := KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B
  let rhoHS : Hbar →* UniversalHyperlinear U S.model S.modelNonempty :=
    S.toUltraproductHom hcof
  have hdefect : ∀ gamma : Gamma,
      rhoHS ⁅Cbar.transported, Cbar.iota gamma⁆ = 1 := by
    intro gamma
    exact Cbar.compressionDefects_eq_one_in_hyperlinearHom B hcof gamma
  have hkillK : ∀ x : Kbar, rhoHS (x : Hbar) = 1 := by
    intro x
    exact Cbar.map_eq_one_of_mem_of_defects_eq_one rhoHS hdefect Kbar hK x
  obtain ⟨s, _hsMem, hsurvive⟩ :=
    R.exists_generator_hyperlinearHom_ne_one hcof
  apply hsurvive
  rw [R.hyperlinearHom_apply]
  have hkill := hkillK s
  change QuotientGroup.mk (fun n ↦ S.map n (s : Hbar)) = 1 at hkill
  have hmap : (fun n ↦ S.map n (s : Hbar)) = (fun n ↦ R.map n (s : Hbar)) := by
    funext n
    rfl
  rw [hmap] at hkill
  exact hkill

/-! ## Assembly -/

/-- **Assembly of the printed chain.**  Every corona representation of a
countable group carrying a Kazhdan conjugation datum kills each normal
property-`(T)` subgroup of its compression defect, proved exactly along the
manuscript's route:

`nk_01` (surviving corona representation) → `nk_02` (countable MF image) →
`nk_03` (separated finite models) → `nk_04` (moving corner).

Between steps 3 and 4 the printed proof records that "the datum and the
subgroup pass to their `Θ`-images with normality and property-`(T)`
preserved, and `K̄ = Θ(K)` is nontrivial and lies in the defect subgroup of
the image datum"; that transport is the `Kbar` block below, supplied by
`KazhdanCompressionCore.map`, `map_subgroup_normal`,
`map_subgroup_hasKazhdanPropertyT` and `map_subgroup_le_defectNormal`.

This is the basis-free coordinate form; the manuscript's literal
natural-dimension statement is
`manuscriptNormalKazhdanObstructionViaCoronaImage`. -/
theorem nk_05_assembly [Countable H]
    (C : KazhdanCompressionCore Gamma H)
    (K : Subgroup H) [K.Normal]
    (hT : HasKazhdanPropertyT.{0, 0} K)
    (hK : K ≤ C.defectNormal)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ Theta : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      K ≤ Theta.ker := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro Theta k hk
  by_contra hker
  have hThetak : Theta k ≠ 1 := fun hone ↦ hker (MonoidHom.mem_ker.mpr hone)
  -- Step 1: the surviving corona representation, in its coordinate model.
  obtain ⟨sigma, _hcoordinate, hsigmak⟩ :=
    nk_01_surviving_corona_representation X Theta hThetak
  -- Step 2: the image is countable, hence MF.
  obtain ⟨hcountable, hMFimage⟩ := nk_02_countable_mf_image X hX sigma
  letI : Countable sigma.range := hcountable
  -- Step 3: separated finite models for the image, along an exhaustion.
  obtain ⟨_hseparation, ⟨A⟩⟩ := nk_03_separated_finite_models hMFimage
  -- The datum and the subgroup pass to their images.
  let f : H →* sigma.range := sigma.rangeRestrict
  let Kbar : Subgroup sigma.range := K.map f
  letI : Kbar.Normal :=
    KazhdanCompressionCore.map_subgroup_normal K f
      sigma.rangeRestrict_surjective
  have hTbar : HasKazhdanPropertyT.{0, 0} Kbar :=
    KazhdanCompressionCore.map_subgroup_hasKazhdanPropertyT K f hT
  have hfk : f k ∈ Kbar := ⟨k, hk, rfl⟩
  have hfk_ne : f k ≠ 1 := by
    intro heq
    apply hsigmak
    exact congrArg Subtype.val heq
  letI : Nontrivial Kbar :=
    ⟨⟨⟨f k, hfk⟩, 1, fun heq ↦ hfk_ne (congrArg Subtype.val heq)⟩⟩
  have hKbar : Kbar ≤ (C.map f).defectNormal :=
    C.map_subgroup_le_defectNormal f K hK
  -- Step 4: the moving corner on those models.
  exact nk_04_moving_corner (C.map f) Kbar hTbar hKbar A

end Route

/-- **Manuscript Theorem~\ref{thm:normal-kazhdan}, certified along its printed
proof.**  Let `H` be a countable group with a Kazhdan conjugation datum
`(Λ, ι, t, c)` and let `K ⊴ H` be a normal subgroup with property `(T)` such
that `K ⊆ N_comp`.  Then every corona representation `Θ : H → U(𝒬)` satisfies
`Θ(k) = 1` for all `k ∈ K`.

Same statement as
`ManuscriptExactWrappers.manuscriptNormalKazhdanObstruction`; the difference
is the route.  That wrapper reaches the conclusion through the universal
norm-MF residual, which is a stronger intermediate assertion than the
manuscript makes.  This declaration traverses the printed chain instead:
surviving corona representation → countable MF image → separated finite
models → moving corner, as `nk_05_assembly` and the four `nk_0i` lemmas.

The hypotheses are exactly the printed ones: `H` countable, the Kazhdan
source countable as required by Definition~\ref{def:pattern} (carried but
unused, exactly as in the print), the containment `K ⊆ N_comp`, and no
finiteness, centrality, or torsion hypothesis on `K`. -/
theorem manuscriptNormalKazhdanObstructionViaCoronaImage :
    ∀ {Gamma H : Type} [Group Gamma] [Group H]
      [_countableGamma : Countable Gamma] [Countable H]
      (C : KazhdanCompressionCore Gamma H)
      (K : Subgroup H) [K.Normal]
      (hT : HasKazhdanPropertyT.{0, 0} K)
      (hK : K ≤ C.defectNormal)
      (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
    let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (by
        simpa [X] using hd n)
    ∀ Theta : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      K ≤ Theta.ker := by
  intro Gamma H _ _ _ _ C K _ hT hK d hd
  exact nk_05_assembly C K hT hK
    (fun n ↦ naturalFiniteModel (d n)) (fun n ↦ by
      simpa using hd n)

end CoronaImageNormalKazhdan
end GroupApproximation
