import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingRankTwo

/-!
# The unit group of the coefficient ring is not MF

`notes/rank-two-descent-note-2026-09-07.md`, §6:

> For every nonzero ring under the theorem, `j` embeds the non-MF group
> `EL₄(R)` into `R^×`, so `R^×` and every `GL_n(R)`, `n ≥ 1`, are not MF
> (non-MF, not full collapse).

The embedding is already built: `j : M₄(R) → R` of §3 is an injective
multiplicative unital map, so `Units.map` of it embeds `GL₄(R)` — and with it
`EL₄(R)` — into `R^×`.  Since every homomorphism from `EL₄(R)` to an MF group
is trivial, and `EL₄(R)` is nontrivial as soon as `R` is, no injective
homomorphism out of `EL₄(R)` can land in an MF group.  So `R^×` is not MF.

The parenthesis in the note is the point worth keeping in the printed
sentence: what is proved is that `R^×` fails to be MF, not that every
homomorphism out of it is trivial.  `R^×` contains, for instance, the central
units of `R`, about which nothing is claimed here.

## Where nontriviality is needed

If `R = 0` then `R^×` is trivial and is MF, so the hypothesis `Nontrivial R`
is not an artefact.  It enters exactly once, to say that the elementary root
`e₁₂(1)` of `EL₄(R)` is not the identity.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace FullDefectRankTwo

open RankDescent
open OneSidedCompressor

/-- **MF-ness of groups passes back along an injective homomorphism**, in
particular to subgroups.  This is the general form of the note's step; it is
not used below, where the contradiction is drawn directly from triviality, but
it is the statement a reader expects at this point. -/
theorem isOperatorMF_of_injective {G M : Type} [Group G] [Group M]
    (φ : G →* M) (hφ : Function.Injective φ) (hM : IsOperatorMF M) :
    IsOperatorMF G := by
  obtain ⟨X, hX, rho, hrho⟩ := hM
  exact ⟨X, hX, rho.comp φ, hrho.comp hφ⟩

section Embedding

variable {R : Type} [Ring R] (S T : Fin 4 → R)
  (hTS : ∀ i j, T i * S j = if i = j then 1 else 0)

include hTS

/-- The printed embedding `GL₄(R) → R^×` induced by the multiplicative map
`j`. -/
noncomputable def jUnits : (Matrix (Fin 4) (Fin 4) R)ˣ →* Rˣ :=
  Units.map (jHom S T hTS)

theorem jUnits_injective : Function.Injective (jUnits S T hTS) := by
  intro u v h
  apply Units.ext
  exact jMap_injective S T hTS (congrArg Units.val h)

/-- The embedding restricted to the elementary group. -/
noncomputable def elementaryToUnits : elementaryGroup (Fin 4) R →* Rˣ :=
  (jUnits S T hTS).comp (elementaryGroup (Fin 4) R).subtype

theorem elementaryToUnits_injective :
    Function.Injective (elementaryToUnits S T hTS) :=
  (jUnits_injective S T hTS).comp Subtype.val_injective

end Embedding

/-- `EL₄(R)` is nontrivial whenever `R` is: the root `e₁₂(1)` is not the
identity. -/
theorem elementaryRoot_one_ne_one {R : Type} [Ring R] [Nontrivial R] :
    elementaryRoot (0 : Fin 4) 1 (by decide) (1 : R) ≠ 1 := by
  intro h
  exact one_ne_zero ((elGen_eq_one_iff (0 : Fin 4) 1 (by decide) (1 : R)).mp h)

/-- **The unit-group consequence, at a fixed ring.**  If every homomorphism
from `EL₄(R)` to an MF group is trivial and `R` is nonzero, then `R^×` is not
MF: otherwise the embedding `EL₄(R) → R^×` would be both trivial and
injective on a nontrivial group. -/
theorem not_isOperatorMF_units_of_rankFour {R : Type} [Ring R] [Nontrivial R]
    (s t : R) (hts : t * s = 1)
    {m : ℕ} (a b : Fin m → R) (hab : ∑ k, a k * (1 - s * t) * b k = 1)
    (h4 : ∀ (M : Type) [Group M], IsOperatorMF M →
      ∀ (f : elementaryGroup (Fin 4) R →* M)
        (x : elementaryGroup (Fin 4) R), f x = 1) :
    ¬ IsOperatorMF Rˣ := by
  intro hMF
  set P : OneSidedInverse R := ⟨s, t, hts⟩ with hP
  have hab' : ∑ k, a k * P.e * b k = 1 := hab
  set Q : ProperlyInfiniteUnit R := ofFull P a b hab' with hQ
  have hTS := wordT_mul_wordS Q
  have hinj := elementaryToUnits_injective (wordS Q) (wordT Q) hTS
  have htriv := h4 Rˣ hMF (elementaryToUnits (wordS Q) (wordT Q) hTS)
  refine elementaryRoot_one_ne_one (R := R) (hinj ?_)
  rw [htriv, map_one]

/-! ## The printed statements -/

/-- **§6.**  For every nonzero countable ring satisfying the printed
hypothesis, the unit group `R^×` is not MF. -/
def PrintedUnitGroupNotMF : Prop :=
  ∀ (R : Type) [Ring R] [Countable R] [Nontrivial R] (s t : R), t * s = 1 →
    (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
      ¬ IsOperatorMF Rˣ

/-- **§6 in prime characteristic**, where the printed statement carries no
hypothesis at all. -/
def PrintedUnitGroupNotMFPrimeChar : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (R : Type) [Ring R] [Countable R] [Nontrivial R]
    [CharP R p] (s t : R), t * s = 1 →
      (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
        ¬ IsOperatorMF Rˣ

theorem manuscriptUnitGroupNotMFPrimeChar : PrintedUnitGroupNotMFPrimeChar := by
  intro p hp R _ _ _ _ s t hts hfull
  obtain ⟨m, a, b, hab⟩ := hfull
  refine not_isOperatorMF_units_of_rankFour s t hts a b hab
    (fun M _ hM f x ↦ ?_)
  exact manuscriptFullComplementaryIdempotentsPrimeCharRankTwo p hp R s t hts
    ⟨m, a, b, hab⟩ 4 (by norm_num) M hM f x

theorem manuscriptUnitGroupNotMFFromEJZ
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedUnitGroupNotMF := by
  intro R _ _ _ s t hts hfull
  obtain ⟨m, a, b, hab⟩ := hfull
  refine not_isOperatorMF_units_of_rankFour s t hts a b hab
    (fun M _ hM f x ↦ ?_)
  exact manuscriptFullComplementaryIdempotentsRankTwoFromEJZ hEJZ R s t hts
    ⟨m, a, b, hab⟩ 4 (by norm_num) M hM f x

end FullDefectRankTwo
end OneSidedMFRadical
end Manuscript
end GroupApproximation
