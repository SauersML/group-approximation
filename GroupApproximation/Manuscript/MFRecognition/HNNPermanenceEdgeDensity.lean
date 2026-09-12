import GroupApproximation.Analysis.HNNTraceGeneratedDensity
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceCitations

/-!
# Two `*`-homomorphisms that agree on generators agree on `B₀`

This module proves the last printed sentence of Step 3 of
`thm:hnn-permanence` that was still assumed:

> two `*`-homomorphisms that agree on generators agree on `B₀`.

`B₀ = C*(ιρ(S))` is `groupGeneratedCStar` of the represented subgroup, and the
argument is the ordinary density one.  Its two halves are already on main:
`HNNTrace.groupGeneratedCStar_dense_span` says the linear span of the
represented generators is dense in `C*(ρ(H))`, and star-algebra homomorphisms
of C-star algebras are contractive, hence continuous.  Two continuous maps into
a Hausdorff space that agree on a dense set are equal, and agreement propagates
from the generators to their span because both maps are `ℂ`-linear.

With this, `HNNPermanenceCitations.EdgeDensityStatement` is discharged and the
corresponding field disappears from `HNNInputs`, leaving only the two cited
results of Steps 1–2 and the two obligations that are artefacts of the
formalization rather than statements of the manuscript.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

/-- A star-algebra homomorphism of C-star algebras is contractive, hence
continuous.

Built here rather than synthesized: `map_continuous` needs a
`ContinuousMapClass` instance for maps *out of* the subtype
`↥(groupGeneratedCStar rho)`, and that instance does not resolve through the
subtype's structure.  `NonUnitalStarAlgHom.norm_apply_le` — the same bound the
repository uses in `UniversalCStarHNN` — gives the Lipschitz constant `1`
directly, with no class search. -/
theorem starAlgHom_continuous {P : Type} [CStarAlgebra P] {E : Type}
    [CStarAlgebra E] (q : P →⋆ₐ[ℂ] E) : Continuous (q : P → E) := by
  have hlip : LipschitzWith 1 (q : P → E) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    simpa using
      NonUnitalStarAlgHom.norm_apply_le q.toNonUnitalStarAlgHom (x - y)
  exact hlip.continuous

/-- **Generators determine a `*`-homomorphism on `C*(ρ(H))`.**

Stated over a variable C-star algebra, so that the topological instances are
the ones carried by `CStarAlgebra` rather than a subtype topology — the same
reason `mem_closure_of_mem_groupGeneratedCStar` is stated that way. -/
theorem starAlgHom_ext_groupGeneratedCStar {H : Type} [Group H] {B : Type}
    [CStarAlgebra B] {E : Type} [CStarAlgebra E] (rho : H →* unitary B)
    (f g : groupGeneratedCStar rho →⋆ₐ[ℂ] E)
    (hgen : ∀ h : H,
      f (((groupGeneratedUnitaryHom rho h :
          unitary (groupGeneratedCStar rho)) : groupGeneratedCStar rho)) =
        g (((groupGeneratedUnitaryHom rho h :
          unitary (groupGeneratedCStar rho)) : groupGeneratedCStar rho))) :
    f = g := by
  letI : IsClosed ((groupGeneratedCStar rho : StarSubalgebra ℂ B) : Set B) :=
    groupGeneratedCStar_isClosed rho
  letI : CStarAlgebra (groupGeneratedCStar rho) :=
    groupGeneratedCStar_cStarAlgebra rho
  have heq : Set.EqOn (f : groupGeneratedCStar rho → E) g
      ((Submodule.span ℂ
        (Set.range (fun h : H ↦
          ((groupGeneratedUnitaryHom rho h :
            unitary (groupGeneratedCStar rho)) : groupGeneratedCStar rho))) :
        Submodule ℂ (groupGeneratedCStar rho)) :
          Set (groupGeneratedCStar rho)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨h, rfl⟩ := hy
        exact hgen h
    | zero => rw [map_zero, map_zero]
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, ha]
  have hfun : (f : groupGeneratedCStar rho → E) = g :=
    Continuous.ext_on (HNNTrace.groupGeneratedCStar_dense_span rho)
      (starAlgHom_continuous f) (starAlgHom_continuous g) heq
  exact DFunLike.coe_injective hfun

/-- **The printed density sentence of Step 3, proved.**

Printed: *"two `*`-homomorphisms that agree on generators agree on `B₀`"*.
This discharges `EdgeDensityStatement`, so it is no longer a field of
`HNNInputs`. -/
theorem edgeDensity_proved : EdgeDensityStatement := by
  intro G _ S T phi A _ X _ data E _ f g hgen
  exact starAlgHom_ext_groupGeneratedCStar _ f g hgen

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
