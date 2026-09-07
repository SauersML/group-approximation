import GroupApproximation.Manuscript.NonMF.FournierFacioParagraph
import GroupApproximation.Manuscript.NonMF.HullPrintedInputs
import GroupApproximation.Manuscript.NonMF.Saturation
import GroupApproximation.Manuscript.NonMF.TorsionFreeTheoremC
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion

/-!
# `thm:torsion-free`, along the printed proof

`non_mf_groups_exist.tex`, `thm:torsion-free` and its section `sec:torsion-free`.

> **Theorem (a torsion-free finitely presented example).**  There is a
> two-generated, finitely presented, torsion-free, acylindrically hyperbolic
> group `Q` with property (T) such that every homomorphism from `Q` to an MF
> group is trivial.  In particular, no nontrivial quotient of `Q` is MF.

and its proof:

> Let `N` be the normal closure of `S` in `G₀`; it is nontrivial because `S` is.
> By Lemma `lem:saturation` applied to `G₀`, `N`, and `Ω = ∅`, there is a
> surjective homomorphism `φ : G₀ → Q` with `Q` two-generated, finitely
> presented, torsion-free, and acylindrically hyperbolic, and `φ(N) = Q`.  The
> group `Q` is infinite because it is acylindrically hyperbolic, and it has
> property (T) as a quotient of `G₀`.
>
> By Lemma `lem:commutator-in-defect` applied to `φ`, `φ(S) ≤ 𝔇_Q(φ(Γ))`.  The
> subgroup `𝔇_Q(φ(Γ))` is normal in `Q`, and the normal closure of `φ(S)` is
> `φ(N) = Q`, so `𝔇_Q(φ(Γ)) = Q`.  Both `Q` and `φ(Γ)` have property (T), as
> quotients of `G₀` and `Γ` respectively.  By the last assertion of Theorem
> `thm:compression-criterion`, every homomorphism from `Q` to an MF group is
> trivial.  If a quotient `Q̄` of `Q` is MF, then the quotient map `Q → Q̄` is
> trivial, so `Q̄ = 1`.

## What the theorem rests on

Two hypotheses, and nothing else:

* `hFFF : FournierFacioParagraph` — the cited construction of `G₀`, `Γ`, `t`,
  `J` (Fournier-Facio §2), with `G₀` acylindrically hyperbolic (Hull,
  Corollary 7.4).
* `hHull : HullPrintedInputs` — Hull's Theorem 7.1 with its kernel clause, and
  Osin's Lemma 7.1.

Everything between them and the conclusion is proved here or is already in the
repository: `lem:saturation` is `TorsionFree.saturation`,
`lem:commutator-in-defect` is `SimpleInDefect.manuscriptLemmaCommutatorInDefect`
by the printed perfectness proof, and the last assertion of
`thm:compression-criterion` is
`OneSidedMFRadical.manuscriptOneSidedCompressionCriterion` together with
`OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets`.

This is a **second, independent route** to `thm:torsion-free`.
`TheoremC.manuscriptTorsionFreeFullMFRadical` reaches the same conclusion over
`TheoremC.LiteratureInputs`, which is the *earlier* printed construction of
`G₀` — Chiodo's universal group, a Kotowski--Ollivier density-model group, a
small-cancellation quotient, Minasyan--Osin, and Hull's Corollary 7.4 — five
citations where the current print has one, and with `F₂` in place of `J`.  The
current print takes `G₀` from Fournier-Facio directly, so the route in this
module is the printed one.  Both are proved and neither is deleted.

## Two statements of the conclusion

`PrintedTorsionFreeTheorem` is the printed theorem, clause for clause: the five
adjectives, *"every homomorphism from `Q` to an MF group is trivial"*, and
*"no nontrivial quotient of `Q` is MF"*.

`TheoremC.PrintedTorsionFreeFullMFRadical` states more: it replaces the
homomorphism clause by `Rad_MF(Q) = ⊤` and asserts the same of every nontrivial
quotient.  Over a countable group the two are equivalent for `Q` itself, by
`manuscriptFullRadicalKillsMFTargets` in one direction; the per-quotient clause
is genuinely stronger, and the proof here gives it, so both are proved from the
same two hypotheses.

No `#audit_closed_axioms` appears below: the macro refuses a declaration with a
leading input, and every endpoint here takes the two citations as hypotheses,
which is the point.  The macro becomes available for these names on the day
something inhabits `FournierFacioParagraph` and `HullPrintedInputs`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## `lem:saturation` as a closed proposition -/

/-- **`lem:saturation`, as one closed proposition.**

> Let `G` be finitely presented, torsion-free, and acylindrically hyperbolic, let
> `N ⊴ G` be nontrivial, and let `Ω ⊆ G` be finite.  Then there is a surjective
> homomorphism `φ : G → Q` such that `Q` is two-generated, finitely presented,
> torsion-free, and acylindrically hyperbolic, `φ|_Ω` is injective, and
> `φ(N) = Q`.

The conclusion is `TorsionFree.SaturationQuotient`, whose fields are the printed
clauses one for one. -/
def PrintedSaturation : Prop :=
  ∀ (G : Type u) [Group G] [Group.IsFinitelyPresented G]
    [IsAcylindricallyHyperbolic G], IsPowerTorsionFree G →
      ∀ (N : Subgroup G) [N.Normal], N ≠ ⊥ → ∀ {Ω : Set G}, Ω.Finite →
        Nonempty (SaturationQuotient N Ω)

/-- **`lem:saturation`, proved from the printed citations alone.**

`HullPrintedInputs` is the whole of the literature input: Hull's Theorem 7.1
with its kernel clause, and Osin's Lemma 7.1.  Hull's Corollary 5.7 with
Lemma 5.8 — the section's third citation — is not needed, because
`hullSuitablePair_of_torsionFree` proves it in the torsion-free case, which is
the only case the lemma uses. -/
theorem manuscriptSaturation (hHull : HullPrintedInputs.{u}) :
    PrintedSaturation.{u} := by
  intro G _ _ _ hG N _ hN Ω hΩ
  exact saturation hHull.toCorrected hG N hN hΩ

/-! ## The body of the printed proof -/

/-- **The two middle paragraphs of the printed proof of `thm:torsion-free`**, at
an arbitrary surjection `ρ` under which the normal closure of `S` maps onto the
target.

> By Lemma `lem:commutator-in-defect` applied to `φ`, `φ(S) ≤ 𝔇_Q(φ(Γ))`.  The
> subgroup `𝔇_Q(φ(Γ))` is normal in `Q`, and the normal closure of `φ(S)` is
> `φ(N) = Q`, so `𝔇_Q(φ(Γ)) = Q`.  Both `Q` and `φ(Γ)` have property (T), as
> quotients of `G₀` and `Γ` respectively.  By the last assertion of Theorem
> `thm:compression-criterion` …

Stated for an arbitrary target rather than only for the saturation quotient,
because the same three sentences give the conclusion for every further quotient
of that quotient — which is what
`TheoremC.PrintedTorsionFreeFullMFRadical` asks for. -/
theorem coronaMFResidual_eq_top_of_map_normalClosure_eq_top {G₀ : Type}
    [Group G₀] [Countable G₀] (F : PrintedFournierFacioData G₀)
    (hΓT : HasKazhdanPropertyT.{0, 0} ↥F.core)
    (hG₀T : HasKazhdanPropertyT.{0, 0} G₀)
    {L : Type} [Group L] (rho : G₀ →* L) (hrho : Function.Surjective rho)
    (htop : (Subgroup.normalClosure (F.conjFactor : Set G₀)).map rho = ⊤) :
    manuscriptCoronaMFResidual L = ⊤ := by
  letI : Countable L := hrho.countable
  -- "By Lemma `lem:commutator-in-defect` applied to `φ`, `φ(S) ≤ 𝔇_Q(φ(Γ))`."
  have hS : F.conjFactor.map rho ≤
      OneSidedMFRadical.printedDefect (F.core.map rho) :=
    manuscriptLemmaCommutatorInDefect F rho
  -- "The subgroup `𝔇_Q(φ(Γ))` is normal in `Q`, and the normal closure of
  -- `φ(S)` is `φ(N) = Q`, so `𝔇_Q(φ(Γ)) = Q`."
  have hNle : Subgroup.normalClosure (F.conjFactor : Set G₀) ≤
      (OneSidedMFRadical.printedDefect (F.core.map rho)).comap rho := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    exact hS (Subgroup.mem_map_of_mem rho hy)
  have hDtop : OneSidedMFRadical.printedDefect (F.core.map rho) = ⊤ := by
    refine top_unique ?_
    rw [← htop]
    exact Subgroup.map_le_iff_le_comap.mpr hNle
  -- "Both `Q` and `φ(Γ)` have property (T), as quotients of `G₀` and `Γ`."
  have hΓL : HasKazhdanPropertyT.{0, 0} ↥(F.core.map rho) := by
    have hrange : (rho.comp F.core.subtype).range = F.core.map rho := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact HasKazhdanPropertyT.of_surjective
      (rho.comp F.core.subtype).rangeRestrict
      (rho.comp F.core.subtype).rangeRestrict_surjective hΓT
  have hLT : HasKazhdanPropertyT.{0, 0} L :=
    HasKazhdanPropertyT.of_surjective rho hrho hG₀T
  -- "By the last assertion of Theorem `thm:compression-criterion` …"
  obtain ⟨-, -, hsat⟩ :=
    OneSidedMFRadical.manuscriptOneSidedCompressionCriterion L
      (F.core.map rho) hΓL
  exact hsat hLT hDtop

/-! ## The saturated quotient of the printed proof -/

/-- **The first paragraph of the printed proof of `thm:torsion-free`**, with its
conclusion in the form both printed statements consume.

> Let `N` be the normal closure of `S` in `G₀`; it is nontrivial because `S` is.
> By Lemma `lem:saturation` applied to `G₀`, `N`, and `Ω = ∅`, there is a
> surjective homomorphism `φ : G₀ → Q` with `Q` two-generated, finitely
> presented, torsion-free, and acylindrically hyperbolic, and `φ(N) = Q`.  …it
> has property (T) as a quotient of `G₀`.

The last conjunct is the conclusion of
`coronaMFResidual_eq_top_of_map_normalClosure_eq_top`, transported along every
surjection out of `Q`: `φ(N) = Q` survives composition with any further
surjection. -/
theorem exists_saturatedQuotient (hFFF : FournierFacioParagraph)
    (hHull : HullPrintedInputs.{0}) :
    ∃ (Q : Type) (_ : Group Q), IsTwoGenerated Q ∧
      Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
        IsAcylindricallyHyperbolic Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
          Countable Q ∧
            ∀ (L : Type) (_ : Group L) (r : Q →* L), Function.Surjective r →
              manuscriptCoronaMFResidual L = ⊤ := by
  obtain ⟨G₀, instG₀, hfp, htf, hT, hacyl, F, hΓT, -, -⟩ := hFFF
  letI := instG₀
  haveI := hfp
  haveI := hacyl
  haveI : Countable G₀ := ChiodoBelegradek.countable_of_isFinitelyPresented G₀
  -- "Put `S = tJt⁻¹`."  `S ≠ 1` because `J ≠ 1`: a simple group is nontrivial.
  haveI := F.simple
  obtain ⟨j, hjmem, hjne⟩ : ∃ j : G₀, j ∈ F.simpleFactor ∧ j ≠ 1 := by
    obtain ⟨jj, hjj⟩ := exists_ne (1 : ↥F.simpleFactor)
    exact ⟨(jj : G₀), jj.2, fun h => hjj (Subtype.ext (by simpa using h))⟩
  have hmemS : F.t * j * F.t⁻¹ ∈ F.conjFactor := by
    rw [F.conjFactor_def]
    exact Subgroup.mem_map.mpr ⟨j, hjmem, by simp⟩
  have hneS : F.t * j * F.t⁻¹ ≠ 1 := by
    intro h
    apply hjne
    have hj : j = F.t⁻¹ * (F.t * j * F.t⁻¹) * F.t := by group
    rw [hj, h]
    group
  -- "Let `N` be the normal closure of `S` in `G₀`; it is nontrivial because
  -- `S` is."
  have hNne : Subgroup.normalClosure (F.conjFactor : Set G₀) ≠ ⊥ := by
    intro hbot
    apply hneS
    have hmem : F.t * j * F.t⁻¹ ∈
        Subgroup.normalClosure (F.conjFactor : Set G₀) :=
      Subgroup.subset_normalClosure (SetLike.mem_coe.mpr hmemS)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  -- "By Lemma `lem:saturation` applied to `G₀`, `N`, and `Ω = ∅` …"
  obtain ⟨SQ⟩ := manuscriptSaturation hHull G₀ htf
    (Subgroup.normalClosure (F.conjFactor : Set G₀)) hNne
    (Ω := (∅ : Set G₀)) Set.finite_empty
  haveI : Countable SQ.Q := SQ.surjective.countable
  -- "…and it has property (T) as a quotient of `G₀`."
  have hQT : HasKazhdanPropertyT.{0, 0} SQ.Q :=
    HasKazhdanPropertyT.of_surjective SQ.q SQ.surjective hT
  refine ⟨SQ.Q, inferInstance,
    ⟨SQ.generatorOne, SQ.generatorTwo, SQ.twoGenerated⟩, inferInstance,
    SQ.torsionFree, inferInstance, hQT, inferInstance, ?_⟩
  intro L instL r hr
  letI := instL
  refine coronaMFResidual_eq_top_of_map_normalClosure_eq_top F hΓT hT
    (r.comp SQ.q) (hr.comp SQ.surjective) ?_
  rw [← Subgroup.map_map, SQ.map_eq_top]
  exact Subgroup.map_top_of_surjective r hr

/-! ## The printed theorem -/

/-- **`thm:torsion-free`, exactly as printed.**

> There is a two-generated, finitely presented, torsion-free, acylindrically
> hyperbolic group `Q` with property (T) such that every homomorphism from `Q`
> to an MF group is trivial.  In particular, no nontrivial quotient of `Q` is
> MF.

Seven clauses, in the printed order.  "MF" is `IsOperatorMF`, the
countability-free operator-norm predicate, so the last two clauses put no
countability binder on the targets. -/
def PrintedTorsionFreeTheorem : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
      IsAcylindricallyHyperbolic Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
        (∀ (M : Type) (_ : Group M), IsOperatorMF M →
          ∀ (f : Q →* M) (x : Q), f x = 1) ∧
        (∀ (L : Type) (_ : Group L) (r : Q →* L), Function.Surjective r →
          Nontrivial L → ¬ IsOperatorMF L)

/-- **`thm:torsion-free`, proved along the printed proof.**

The two hypotheses are the section's two literature inputs: the Fournier-Facio
paragraph and Hull's Theorem 7.1 with Osin's Lemma 7.1.  Everything else is
proved. -/
theorem manuscriptTorsionFreeTheorem (hFFF : FournierFacioParagraph)
    (hHull : HullPrintedInputs.{0}) : PrintedTorsionFreeTheorem := by
  obtain ⟨Q, instQ, hgen, hfp, htf, hacyl, hQT, hcount, hmain⟩ :=
    exists_saturatedQuotient hFFF hHull
  letI := instQ
  haveI := hcount
  have hQtop : manuscriptCoronaMFResidual Q = ⊤ :=
    hmain Q instQ (MonoidHom.id Q) Function.surjective_id
  -- "By the last assertion of Theorem `thm:compression-criterion`, every
  -- homomorphism from `Q` to an MF group is trivial."
  have hkill : ∀ (M : Type) (_ : Group M), IsOperatorMF M →
      ∀ (f : Q →* M) (x : Q), f x = 1 := by
    intro M instM hM f x
    letI := instM
    exact OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets Q M hQtop hM f x
  -- "If a quotient `Q̄` of `Q` is MF, then the quotient map `Q → Q̄` is trivial,
  -- so `Q̄ = 1`."
  refine ⟨Q, instQ, hgen, hfp, htf, hacyl, hQT, hkill, ?_⟩
  intro L instL r hr hne hMF
  letI := instL
  haveI := hne
  obtain ⟨y, hy⟩ := exists_ne (1 : L)
  obtain ⟨x, rfl⟩ := hr y
  exact hy (hkill L instL hMF r x)

/-- **`thm:torsion-free` in the stronger form
`TheoremC.PrintedTorsionFreeFullMFRadical` records**, from the same two printed
inputs.

That statement replaces *"every homomorphism from `Q` to an MF group is
trivial"* by `Rad_MF(Q) = Q` and asserts the same of every nontrivial quotient.
The printed proof gives it: `exists_saturatedQuotient`'s last conjunct already
holds at every surjective image of `Q`, because `φ(N) = Q` survives composition
with any further surjection. -/
theorem manuscriptTorsionFreeFullMFRadicalFromParagraph
    (hFFF : FournierFacioParagraph) (hHull : HullPrintedInputs.{0}) :
    TheoremC.PrintedTorsionFreeFullMFRadical := by
  obtain ⟨Q, instQ, hgen, hfp, htf, hacyl, hQT, hcount, hmain⟩ :=
    exists_saturatedQuotient hFFF hHull
  letI := instQ
  haveI := hcount
  have hQtop : manuscriptCoronaMFResidual Q = ⊤ :=
    hmain Q instQ (MonoidHom.id Q) Function.surjective_id
  refine ⟨Q, instQ, hgen, hfp, htf, hacyl, hQT, hQtop, ?_, ?_⟩
  · intro L instL r hr _
    exact hmain L instL r hr
  · intro L instL r hr hne hMF
    letI := instL
    haveI := hne
    haveI : Countable L := hr.countable
    have htop := hmain L instL r hr
    have hbot : manuscriptCoronaMFResidual L = ⊥ :=
      isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot.mp
        ((isCDEOperatorMF_iff_isOperatorMF L).mpr hMF)
    obtain ⟨x, hx⟩ := exists_ne (1 : L)
    apply hx
    have hmem : x ∈ manuscriptCoronaMFResidual L := by
      rw [htop]
      exact Subgroup.mem_top x
    rw [hbot] at hmem
    simpa using hmem

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation
