import GroupApproximation.Manuscript.NonMF.TheoremCAssembly
import GroupApproximation.Computability.PresentationCodeCompleteness
import GroupApproximation.Sofic.CDEOperatorMF

/-!
# `lem:seed`: the seed is the group of Theorem C

> **Lemma (`lem:seed`).**  There is a fixed finite presentation `P₋` whose
> group `E = G_{P₋}` is not MF.
>
> *Proof.*  Theorem C of `[NonMF]` gives a finitely presented torsion-free
> group that equals its own MF radical, and a nontrivial group equal to its own
> MF radical is not MF.  Fix one finite presentation code `P₋` for this group.

This module follows the printed proof literally.  `E` is the group of
Theorem C, read from
`TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs`, so every
declaration below takes that theorem's three hypotheses as explicit arguments:

* `hgreendlinger`, Osin's Lemma 4.4 at least-area diagrams;
* `hbridge`, Osin's Lemma 5.1 in the embedded form;
* `hKO`, Kotowski–Kotowski and Ollivier–Wise.

No `sorry` sits under any of them.  `E` is nontrivial because it is
acylindrically hyperbolic, and it is not MF because its MF radical is
everything.  `seedCodeC` is one finite presentation code for it, chosen by the
adequacy of the coding (`exists_code_mulEquiv`).

Until 2026-09-13 `E` was chosen from
`manuscriptTorsionFreeFullMFRadical_openAdmissions`, which rested on the five
`sorry`s `TheoremCAssembly` then carried; see that module's header for what
replaced them.
-/

namespace GroupApproximation

/-! ## A loxodromic element is not the identity -/

namespace HullGeometry

variable {G X : Type*} [Group G] [PseudoMetricSpace X] [MulAction G X]

/-- A loxodromic element is not the identity: the identity moves nothing,
while a loxodromic element moves the basepoint linearly far. -/
theorem IsLoxodromic.ne_one {g : G} {x : X} (h : IsLoxodromic g x) : g ≠ 1 := by
  rintro rfl
  obtain ⟨l, hl, B, _, hlin⟩ := h
  obtain ⟨n, hn⟩ := exists_nat_gt (B / l)
  have hdist := hlin n
  rw [one_pow, one_smul, dist_self] at hdist
  have : B < l * n := by
    rw [div_lt_iff₀ hl, mul_comm] at hn
    exact hn
  linarith

end HullGeometry

namespace Manuscript
namespace NonMF
namespace TorsionFree

/-- An acylindrically hyperbolic group is nontrivial: it contains a loxodromic
element. -/
theorem nontrivial_of_isAcylindricallyHyperbolic (G : Type) [Group G]
    [IsAcylindricallyHyperbolic G] : Nontrivial G := by
  obtain ⟨A, δ, _, _, g, _, _, _, hg, _, _⟩ := (‹IsAcylindricallyHyperbolic G›).out
  exact ⟨⟨g, 1, HullGeometry.IsLoxodromic.ne_one hg⟩⟩

end TorsionFree
end NonMF

namespace MFRecognition
namespace SeedFromTheoremC

open NonMF.TheoremC
open PresentationCodes

noncomputable section

variable
  (hgreendlinger :
    GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
  (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
  (hKO : KotowskiOllivierStatement)

/-- **The paper's `E`**: the group of Theorem C. -/
def E : Type :=
  (manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs hgreendlinger hbridge hKO).choose

instance instGroupE : Group (E hgreendlinger hbridge hKO) :=
  (manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs hgreendlinger hbridge
    hKO).choose_spec.choose

/-- The printed clauses of Theorem C, at `E`. -/
theorem E_spec :
    IsTwoGenerated (E hgreendlinger hbridge hKO) ∧
      Group.IsFinitelyPresented (E hgreendlinger hbridge hKO) ∧
      IsPowerTorsionFree (E hgreendlinger hbridge hKO) ∧
      NonMF.TorsionFree.IsAcylindricallyHyperbolic (E hgreendlinger hbridge hKO) ∧
      HasKazhdanPropertyT.{0, 0} (E hgreendlinger hbridge hKO) ∧
      manuscriptCoronaMFResidual (E hgreendlinger hbridge hKO) = ⊤ ∧
      (∀ (L : Type) (_ : Group L) (r : E hgreendlinger hbridge hKO →* L),
        Function.Surjective r → Nontrivial L → manuscriptCoronaMFResidual L = ⊤) ∧
      (∀ (L : Type) (_ : Group L) (r : E hgreendlinger hbridge hKO →* L),
        Function.Surjective r → Nontrivial L → ¬ IsOperatorMF L) :=
  (manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs hgreendlinger hbridge
    hKO).choose_spec.choose_spec

instance instFinitelyPresentedE :
    Group.IsFinitelyPresented (E hgreendlinger hbridge hKO) :=
  (E_spec hgreendlinger hbridge hKO).2.1

instance instAcylindricallyHyperbolicE :
    NonMF.TorsionFree.IsAcylindricallyHyperbolic (E hgreendlinger hbridge hKO) :=
  (E_spec hgreendlinger hbridge hKO).2.2.2.1

instance instCountableE : Countable (E hgreendlinger hbridge hKO) :=
  ChiodoBelegradek.countable_of_isFinitelyPresented (E hgreendlinger hbridge hKO)

instance instNontrivialE : Nontrivial (E hgreendlinger hbridge hKO) :=
  NonMF.TorsionFree.nontrivial_of_isAcylindricallyHyperbolic (E hgreendlinger hbridge hKO)

/-- "a nontrivial group equal to its own MF radical is not MF": `E` is not MF. -/
theorem E_not_isOperatorMF : ¬ IsOperatorMF (E hgreendlinger hbridge hKO) := by
  intro h
  exact (E_spec hgreendlinger hbridge hKO).2.2.2.2.2.2.2 (E hgreendlinger hbridge hKO)
    inferInstance (MonoidHom.id _) Function.surjective_id inferInstance h

/-- **"Fix one finite presentation code `P₋` for this group."** -/
def seedCodeC : PresentationCode :=
  (exists_code_mulEquiv (E hgreendlinger hbridge hKO)).choose

/-- The code presents `E`. -/
def seedCodeC_equiv :
    Carrier (seedCodeC hgreendlinger hbridge hKO) ≃* E hgreendlinger hbridge hKO :=
  (exists_code_mulEquiv (E hgreendlinger hbridge hKO)).choose_spec.some

/-- **`lem:seed`**: the seed presentation's group is not MF. -/
theorem not_isOperatorMF_seedCodeC :
    ¬ IsOperatorMF (Carrier (seedCodeC hgreendlinger hbridge hKO)) := by
  intro h
  exact E_not_isOperatorMF hgreendlinger hbridge hKO
    (h.comap (seedCodeC_equiv hgreendlinger hbridge hKO).symm.toMonoidHom
      (seedCodeC_equiv hgreendlinger hbridge hKO).symm.injective)

end

end SeedFromTheoremC
end MFRecognition
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.MFRecognition.SeedFromTheoremC.E_not_isOperatorMF
#audit_axioms GroupApproximation.Manuscript.MFRecognition.SeedFromTheoremC.not_isOperatorMF_seedCodeC
