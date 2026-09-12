import GroupApproximation.Manuscript.NonMF.HullFillCorrectedInputs

/-!
# The three results `sec:torsion-free` cites and does not prove

`non_mf_groups_exist.tex`, section `sec:torsion-free`.  The section quotes three
statements from the literature.  This module states each of them as a **closed
named proposition**, in the printed words and with the printed hypotheses, and
bundles the three as `HullPrintedInputs`.  Nothing here is proved and nothing
here is postulated: a consumer that wants the section's conclusions takes a term
of the bundle as an argument, so every downstream statement carries the
citations in its own type.

## The three

* `HullSmallCancellationPrinted` — **`thm:hull`**, M. Hull, *Small cancellation
  in acylindrically hyperbolic groups*, **Theorem 7.1**, in the finite-set form
  the manuscript records, together with the sentence that follows it:

  > Let `G` be acylindrically hyperbolic, let `N ≤ G` be suitable with respect
  > to `A`, and let `g₁,…,g_m ∈ G` and a finite subset `Ω ⊆ G` be given.  Then
  > there is a surjective homomorphism `φ : G → Q` such that `Q` is
  > acylindrically hyperbolic, `φ|_Ω` is injective, `φ(gᵢ) ∈ φ(N)` for all `i`,
  > and every element of finite order in `Q` is the image of an element of the
  > same order in `G`.
  >
  > Hull's proof treats `m = 1` by passing to `G/⟪r⟫_G` for one element `r` and
  > the general case by induction on `m`, so `ker φ` is the normal closure of
  > `m` elements and `Q` is finitely presented when `G` is.

  The kernel clause is the last field of `HullCorrectedInputs.HullQuotientNG`,
  travelling with the quotient Hull's construction produces rather than
  quantified over arbitrary quotients — the form
  `HullFillKernelRefutation.not_kerNormallyGeneratedStatement` refutes.

* `OsinLemma71Printed` — D. Osin, *Acylindrically hyperbolic groups*,
  **Lemma 7.1**, in the case the proof of `lem:saturation` uses it:

  > The subgroup `N` is normal, and it is infinite because `G` is torsion-free
  > and `N ≠ 1`, so it acts non-elementarily on `Cay(G,A)` by Osin [Lemma 7.1].

  So the printed hypotheses are: `G` torsion-free, `N` normal and nontrivial.
  `HullCorrectedInputs.HullInputsCorrected.osinNonElementary` instead assumes
  Osin's `s`-normality of `N`, which is what his lemma asks for in general;
  `osinNonElementary_of_printed` derives that field from this one, using
  `ne_bot_of_isSNormal`, so the two agree and the printed form is the weaker
  hypothesis of the two.

* `HullSuitablePairPrinted` — Hull, **Corollary 5.7** and **Lemma 5.8**:

  > By Hull [Corollary 5.7 and Lemma 5.8], `N` contains two elements `h₁,h₂`
  > such that `N₀ = ⟨h₁,h₂⟩` is again suitable, possibly with respect to a
  > larger generating set `A' ⊇ A`, and Theorem `thm:hull` holds for `A'` as
  > well, since every finite subset of `G` lies in a ball of `Γ(G,A')`.

  The trailing clause costs nothing here: `HullSmallCancellationPrinted`
  quantifies over every `A : HullGeneratingSet G`, so it holds at `A'` by the
  same term that gives it at `A`.  **Over a torsion-free ambient group this
  citation is not needed at all**: `hullSuitablePair_of_torsionFree` proves the
  conclusion with `A' = A`, from
  `HullInputsProved.exists_pair_suitable_of_torsionFree`, and
  `lem:saturation` applies it only there.  The field is stated because the
  section prints it as a citation, and `HullPrintedInputs` does not carry it for
  that reason.

## The bundle

`HullPrintedInputs` has **two** fields, the two citations `lem:saturation`
actually consumes.  `HullPrintedInputs.toCorrected` produces
`HullCorrectedInputs.HullInputsCorrected` from it, so every existing consumer of
that bundle — `Saturation.saturation` and both printed forms of the torsion-free
theorem — runs off the printed statements without duplication.  The converse
does not hold and is not claimed: `HullInputsCorrected.smallCancellation` carries
an extra `IsPowerTorsionFree G` hypothesis that `thm:hull` does not print.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.HullCorrectedInputs

universe u

/-! ## `thm:hull` -/

/-- **`thm:hull`, Hull's small cancellation theorem, exactly as printed.**

> Let `G` be acylindrically hyperbolic, let `N ≤ G` be suitable with respect to
> `A`, and let `g₁,…,g_m ∈ G` and a finite subset `Ω ⊆ G` be given.  Then there
> is a surjective homomorphism `φ : G → Q` such that `Q` is acylindrically
> hyperbolic, `φ|_Ω` is injective, `φ(gᵢ) ∈ φ(N)` for all `i`, and every element
> of finite order in `Q` is the image of an element of the same order in `G`.

The four conclusions are the four fields of `HullQuotient`; the fifth field of
`HullQuotientNG` is the kernel clause of the sentence that follows the theorem,
*"so `ker φ` is the normal closure of `m` elements"*, which is what the printed
proof of `lem:saturation` uses for finite presentability of the quotient.

The hypotheses are the printed ones and no others.  In particular there is **no
torsion-freeness hypothesis on `G`** here, where
`HullInputsCorrected.smallCancellation` carries one. -/
def HullSmallCancellationPrinted : Prop :=
  ∀ {G : Type u} [Group G] [IsAcylindricallyHyperbolic G]
    (A : HullGeneratingSet G) {N : Subgroup G}, Suitable A.alphabet N →
      ∀ {m : ℕ} (g : Fin m → G) {Ω : Set G}, Ω.Finite →
        Nonempty (HullQuotientNG N g Ω)

/-! ## Osin's Lemma 7.1 -/

/-- **Osin, Lemma 7.1, in the printed case.**

> The subgroup `N` is normal, and it is infinite because `G` is torsion-free and
> `N ≠ 1`, so it acts non-elementarily on `Cay(G,A)` by Osin [Lemma 7.1].

The printed hypotheses are exactly these: `G` torsion-free, `N` normal, `N`
nontrivial.  Osin's own hypothesis is `s`-normality, which the printed sentence
derives from those three; `osinNonElementary_of_printed` shows that this form
still supplies the field the saturation lemma consumes. -/
def OsinLemma71Printed : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G), IsPowerTorsionFree G →
    ∀ (N : Subgroup G) [N.Normal], N ≠ ⊥ →
      ActsNonElementarily N (Cayley.base A.alphabet)

/-- An `s`-normal subgroup is nontrivial: taking `g = 1` in Osin's condition
makes `N` itself an infinite set, and the trivial subgroup is a singleton. -/
theorem ne_bot_of_isSNormal {G : Type u} [Group G] {N : Subgroup G}
    (h : HullSuitable.IsSNormal N) : N ≠ ⊥ := by
  intro hbot
  refine h 1 ?_
  refine Set.Finite.subset (Set.finite_singleton (1 : G)) ?_
  rintro x ⟨hx, -⟩
  rw [hbot, Subgroup.mem_bot] at hx
  exact hx

/-- The printed form of Osin's lemma supplies
`HullInputsCorrected.osinNonElementary`: `s`-normality is stronger than
nontriviality, by `ne_bot_of_isSNormal`. -/
theorem osinNonElementary_of_printed (h : OsinLemma71Printed.{u}) :
    ∀ {G : Type u} [Group G] (A : HullGeneratingSet G), IsPowerTorsionFree G →
      ∀ (N : Subgroup G) [N.Normal], HullSuitable.IsSNormal N →
        ActsNonElementarily N (Cayley.base A.alphabet) := by
  intro G _ A hG N _ hsn
  exact h A hG N (ne_bot_of_isSNormal hsn)

/-! ## Hull's Corollary 5.7 with Lemma 5.8 -/

/-- **Hull, Corollary 5.7 and Lemma 5.8, exactly as printed.**

> By Hull [Corollary 5.7 and Lemma 5.8], `N` contains two elements `h₁,h₂` such
> that `N₀ = ⟨h₁,h₂⟩` is again suitable, possibly with respect to a larger
> generating set `A' ⊇ A`, and Theorem `thm:hull` holds for `A'` as well, since
> every finite subset of `G` lies in a ball of `Γ(G,A')`.

*"possibly with respect to a larger generating set"* is the existential over
`A'` with `A.carrier ⊆ A'.carrier`.  *"and `thm:hull` holds for `A'` as well"* is
not a further clause to assume: `HullSmallCancellationPrinted` is quantified over
every Hull generating set of `G`, so it applies at `A'` unchanged.

This proposition is **not** a field of `HullPrintedInputs`, because
`lem:saturation` never needs it: see `hullSuitablePair_of_torsionFree`. -/
def HullSuitablePairPrinted : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) {N : Subgroup G},
    Suitable A.alphabet N →
      ∃ A' : HullGeneratingSet G, A.alphabet.carrier ⊆ A'.alphabet.carrier ∧
        ∃ h₁ ∈ N, ∃ h₂ ∈ N,
          Suitable A'.alphabet (Subgroup.closure ({h₁, h₂} : Set G))

/-- **Over a torsion-free ambient group Hull's Corollary 5.7 with Lemma 5.8 is a
theorem of this repository**, with `A' = A`.

`HullInputsProved.exists_pair_suitable_of_torsionFree` produces the pair against
the same generating set: non-elementarity is *contains two independent
loxodromic elements*, so the two elements it hands out already generate a
non-elementary subgroup, and Hull's Definition 1.4(3) is free over a torsion-free
group.  `lem:saturation` applies the citation only in this case, which is why
`HullPrintedInputs` does not carry it. -/
theorem hullSuitablePair_of_torsionFree {G : Type u} [Group G]
    (hG : IsPowerTorsionFree G) (A : HullGeneratingSet G) {N : Subgroup G}
    (hN : Suitable A.alphabet N) :
    ∃ A' : HullGeneratingSet G, A.alphabet.carrier ⊆ A'.alphabet.carrier ∧
      ∃ h₁ ∈ N, ∃ h₂ ∈ N,
        Suitable A'.alphabet (Subgroup.closure ({h₁, h₂} : Set G)) := by
  obtain ⟨h₁, hh₁, h₂, hh₂, hsuit⟩ := exists_pair_suitable_of_torsionFree hG hN
  exact ⟨A, subset_rfl, h₁, hh₁, h₂, hh₂, hsuit⟩

/-! ## The bundle -/

/-- **The literature `sec:torsion-free` cites and does not prove**, as the
section prints it.

Two fields, because Hull's Corollary 5.7 with Lemma 5.8 — the third printed
citation — is a theorem in the torsion-free case the section uses it in
(`hullSuitablePair_of_torsionFree`).

The sources are M. Hull, *Small cancellation in acylindrically hyperbolic
groups*, Theorem 7.1, and D. Osin, *Acylindrically hyperbolic groups*,
Lemma 7.1. -/
structure HullPrintedInputs : Type where
  /-- **`thm:hull`** — Hull, Theorem 7.1, with the kernel clause of the
  sentence following it. -/
  smallCancellation : HullSmallCancellationPrinted.{u}
  /-- **Osin, Lemma 7.1**, in the printed case: a nontrivial normal subgroup of
  a torsion-free acylindrically hyperbolic group acts non-elementarily. -/
  osinNonElementary : OsinLemma71Printed.{u}

namespace HullPrintedInputs

/-- The printed citations give the bundle every existing consumer takes.  The
small cancellation field only drops the extra `IsPowerTorsionFree G` hypothesis
that `HullInputsCorrected` carries and `thm:hull` does not print; the Osin field
is `osinNonElementary_of_printed`. -/
def toCorrected (h : HullPrintedInputs.{u}) : HullInputsCorrected.{u} where
  smallCancellation := by
    intro G _ _ _hG A N hN m t F hF
    exact h.smallCancellation A hN t hF
  osinNonElementary := by
    intro G _ A hG N _ hsn
    exact osinNonElementary_of_printed h.osinNonElementary A hG N hsn

end HullPrintedInputs

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation
