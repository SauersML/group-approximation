import GroupApproximation.Analysis.ShulmanFillNormingCoronaRoute
import GroupApproximation.Analysis.ShulmanFillUnitalCorner

/-!
# What the conjugate residual asks for, unconditionally, on the factor images

`ShulmanFill.ConjugateWordNormingStatement` asks that a conjugated unital
compatible corona pair reproduce the amalgam norm of an arbitrary *word* in
the two factor images.  On the generators themselves — the elements of
`ι_{A₁}(A₁)` and `ι_{A₂}(A₂)`, before any product or sum is taken — the
printed hypotheses already answer it, with no citation and with equality
rather than an error term.

The reason is that the hypotheses supply a faithful compatible corona pair
outright.  `Analysis/CompatibleCoronaSupportCorner` unitalizes the printed
nonunital pair on its common support corner, keeping both maps faithful, and
`u = 1` is a legitimate conjugating unitary, so the conjugate shape is
inhabited.  Its evaluation coordinate restricts to the two corona embeddings,
which are isometric because they are injective.

Two consequences worth naming separately:

* `universalCStarAmalgam_factors_injective` — under the printed hypotheses the
  two canonical factor maps of the full amalgam are faithful, so `A₁` and `A₂`
  really are subalgebras of `A₁ *_C A₂`.  This is the part of Theorem 16 that
  needs no analysis at all.
* `exists_conjugate_corona_pair_isometric_on_factors` — the conjugate shape,
  inhabited, evaluating each factor isometrically.

So the whole analytic content of the residual sits in the passage from the
generators to their products: the norm of a word `a₁ b₁ a₂ b₂ ⋯` in the full
amalgam is a supremum over *all* compatible pairs, and a single corona pair
has no reason to compute it.  That passage is what
`Analysis/ShulmanFillNormingCoronaRoute` routes through Shulman's own proof.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

variable {C A₁ A₂ : Type} [CStarAlgebra C] [CStarAlgebra A₁] [CStarAlgebra A₂]
  (iA : C →⋆ₐ[ℂ] A₁) (iB : C →⋆ₐ[ℂ] A₂)
  [Nonempty (CStarAmalgamRepresentation iA iB)]
  (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
  (phiA : A₁ →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
  (phiB : A₂ →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))

/-- **Under the printed hypotheses of Theorem 16 the two factors embed in the
full amalgam.**  Unitalizing the corona pair on its common support corner
gives a compatible representation whose two factor maps are faithful, and a
coordinate faithful on a factor makes that factor's canonical map faithful. -/
theorem universalCStarAmalgam_factors_injective
    (hphiA : Function.Injective phiA) (hphiB : Function.Injective phiB)
    (hcomp : ∀ c : C, phiA (iA c) = phiB (iB c)) :
    Function.Injective (universalCStarAmalgamLeft iA iB) ∧
      Function.Injective (universalCStarAmalgamRight iA iB) := by
  haveI : Nontrivial A₁ := nontrivial_left_of_nonempty_representation iA iB
  obtain ⟨Z, hZ, l, r, hl, hr, hlr⟩ :=
    CompatibleCoronaSupportCorner.exists_compatible_injective_unital_supportCornerEmbeddings
      Y iA iB phiA phiB hphiA hphiB (by ext c; exact hcomp c)
  letI : ∀ n, Nonempty (Z n) := hZ
  exact ⟨universalCStarAmalgamLeft_injective_of_coordinate iA iB
      (CStarAmalgamRepresentation.ofCompatiblePair iA iB l r hlr) hl,
    universalCStarAmalgamRight_injective_of_coordinate iA iB
      (CStarAmalgamRepresentation.ofCompatiblePair iA iB l r hlr) hr⟩

/-- The canonical map of the left factor is isometric under the printed
hypotheses. -/
theorem norm_universalCStarAmalgamLeft
    (hphiA : Function.Injective phiA) (hphiB : Function.Injective phiB)
    (hcomp : ∀ c : C, phiA (iA c) = phiB (iB c)) (a : A₁) :
    ‖universalCStarAmalgamLeft iA iB a‖ = ‖a‖ := by
  have hinj :=
    (universalCStarAmalgam_factors_injective iA iB Y phiA phiB hphiA hphiB
      hcomp).1
  have hiso : Isometry (universalCStarAmalgamLeft iA iB) :=
    NonUnitalStarAlgHom.isometry
      (universalCStarAmalgamLeft iA iB).toNonUnitalStarAlgHom hinj
  exact hiso.norm_map_of_map_zero (map_zero _) a

/-- The canonical map of the right factor is isometric under the printed
hypotheses. -/
theorem norm_universalCStarAmalgamRight
    (hphiA : Function.Injective phiA) (hphiB : Function.Injective phiB)
    (hcomp : ∀ c : C, phiA (iA c) = phiB (iB c)) (b : A₂) :
    ‖universalCStarAmalgamRight iA iB b‖ = ‖b‖ := by
  have hinj :=
    (universalCStarAmalgam_factors_injective iA iB Y phiA phiB hphiA hphiB
      hcomp).2
  have hiso : Isometry (universalCStarAmalgamRight iA iB) :=
    NonUnitalStarAlgHom.isometry
      (universalCStarAmalgamRight iA iB).toNonUnitalStarAlgHom hinj
  exact hiso.norm_map_of_map_zero (map_zero _) b

/-- **The conjugate shape is inhabited, and isometric on both factors.**  This
is `ConjugateWordNormingStatement` with the word replaced by a generator and
the error term removed: the unitalized corona pair, conjugated by the unit,
evaluates each factor of the amalgam isometrically.  Nothing analytic is used;
the estimate the residual really asks for begins with products of
generators. -/
theorem exists_conjugate_corona_pair_isometric_on_factors
    (hphiA : Function.Injective phiA) (hphiB : Function.Injective phiB)
    (hcomp : ∀ c : C, phiA (iA c) = phiB (iB c)) :
    ∃ Z : ℕ → FiniteModel, ∃ hZ : ∀ n, Nonempty (Z n),
      letI : ∀ n, Nonempty (Z n) := hZ
      ∃ l : A₁ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
        ∃ r : A₂ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
          ∃ hlr : l.comp iA = r.comp iB,
            ∃ u : unitary (NormMatrixCStarCorona (fun n ↦ Z n)),
              ∃ hu : ∀ c : C,
                (u : NormMatrixCStarCorona (fun n ↦ Z n)) * l (iA c) =
                  l (iA c) * (u : NormMatrixCStarCorona (fun n ↦ Z n)),
                (∀ a : A₁, ‖universalCStarAmalgamEval iA iB
                    (conjugateRepresentation iA iB l r hlr u hu)
                    (universalCStarAmalgamLeft iA iB a)‖ = ‖a‖) ∧
                  ∀ b : A₂, ‖universalCStarAmalgamEval iA iB
                      (conjugateRepresentation iA iB l r hlr u hu)
                      (universalCStarAmalgamRight iA iB b)‖ = ‖b‖ := by
  haveI : Nontrivial A₁ := nontrivial_left_of_nonempty_representation iA iB
  obtain ⟨Z, hZ, l, r, hl, hr, hlr⟩ :=
    CompatibleCoronaSupportCorner.exists_compatible_injective_unital_supportCornerEmbeddings
      Y iA iB phiA phiB hphiA hphiB (by ext c; exact hcomp c)
  letI : ∀ n, Nonempty (Z n) := hZ
  have hisoL : Isometry l :=
    NonUnitalStarAlgHom.isometry l.toNonUnitalStarAlgHom hl
  have hisoR : Isometry r :=
    NonUnitalStarAlgHom.isometry r.toNonUnitalStarAlgHom hr
  refine ⟨Z, hZ, l, r, hlr, 1, one_commutes_amalgamated iA l, ?_, ?_⟩
  · intro a
    show ‖l a‖ = ‖a‖
    exact hisoL.norm_map_of_map_zero (map_zero _) a
  · intro b
    show ‖unitaryConj (1 : unitary (NormMatrixCStarCorona (fun n ↦ Z n)))
      (r b)‖ = ‖b‖
    rw [unitaryConj_one_apply]
    exact hisoR.norm_map_of_map_zero (map_zero _) b

/-- **The residual's own conclusion, unconditionally, at a generator.**  For
an element of either factor image the conjugate shape attains the amalgam norm
exactly, so the inequality the residual asks for holds for every `δ > 0`. -/
theorem conjugateWordNorming_on_factor_images
    (hphiA : Function.Injective phiA) (hphiB : Function.Injective phiB)
    (hcomp : ∀ c : C, phiA (iA c) = phiB (iB c))
    (y : UniversalCStarAmalgam iA iB)
    (hy : (∃ a : A₁, universalCStarAmalgamLeft iA iB a = y) ∨
      ∃ b : A₂, universalCStarAmalgamRight iA iB b = y)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z : ℕ → FiniteModel, ∃ hZ : ∀ n, Nonempty (Z n),
      letI : ∀ n, Nonempty (Z n) := hZ
      ∃ l : A₁ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
        ∃ r : A₂ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
          ∃ hlr : l.comp iA = r.comp iB,
            ∃ u : unitary (NormMatrixCStarCorona (fun n ↦ Z n)),
              ∃ hu : ∀ c : C,
                (u : NormMatrixCStarCorona (fun n ↦ Z n)) * l (iA c) =
                  l (iA c) * (u : NormMatrixCStarCorona (fun n ↦ Z n)),
                ‖y‖ - δ ≤ ‖universalCStarAmalgamEval iA iB
                  (conjugateRepresentation iA iB l r hlr u hu) y‖ := by
  obtain ⟨Z, hZ, l, r, hlr, u, hu, hleft, hright⟩ :=
    exists_conjugate_corona_pair_isometric_on_factors iA iB Y phiA phiB hphiA
      hphiB hcomp
  letI : ∀ n, Nonempty (Z n) := hZ
  refine ⟨Z, hZ, l, r, hlr, u, hu, ?_⟩
  rcases hy with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · have hy1 := hleft a
    have hy2 :=
      norm_universalCStarAmalgamLeft iA iB Y phiA phiB hphiA hphiB hcomp a
    rw [hy1, hy2]
    linarith
  · have hy1 := hright b
    have hy2 :=
      norm_universalCStarAmalgamRight iA iB Y phiA phiB hphiA hphiB hcomp b
    rw [hy1, hy2]
    linarith

end

end ShulmanFill
end GroupApproximation
