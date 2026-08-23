import GroupApproximation.Sofic.LiteralSignFreeRadicalReduction
import GroupApproximation.Sofic.SymmetricDoubleCovering
import GroupApproximation.Sofic.ShulmanMFTraceBridge

/-!
# The amalgam obligation behind the exact residual is the *symmetric* one

`LiteralSignFreeRadicalReduction.manuscriptSignFreeRadicalReduction` reduces the
manuscript's exact MF-residual identity to a single `Iff`:

```text
Res_MF(E) = q₁⁻¹(D)   ↔   (E/⟨w⟩)/D  is MF.
```

The manuscript discharges the right-hand side at paper level by identifying
`(E/⟨w⟩)/D` with `Σ *_B (B × C₂)` — a free-lamp amalgam over a two-element lamp
— and then invoking Shulman's MF theorem for amalgamated free products.  This
file records what the repository can already contribute to that step, and it is
deliberate about what it does not contribute.

## What is proved here

Everything below is stated *relative to the quotient identification*, which is
the paper-level ingredient and is not formalized anywhere in this tree.  Given
that identification, the results here show that the analytic obligation is
**exactly** the symmetric amalgam statement:

* `exactRadical_iff_isOperatorMF_symmetricDouble` — if the terminal quotient is
  the `C₂` free-lamp amalgam `G *_Γ (Γ × C₂)`, then the exact residual identity
  holds *if and only if* the symmetric double `G *_Γ G` is operator MF.  Both
  directions come from `SymmetricDoubleCovering`'s unconditional covering
  equivalence `isOperatorMF_freeLampFlip_iff_isOperatorMF_symmetricDouble`.
* `exactRadical_of_injective_symmetricDouble` — the same conclusion from the
  weaker input the manuscript actually uses: an injective homomorphism of the
  terminal quotient into a symmetric double that is operator MF.  This is the
  normal-form embedding `Σ *_B (B × C₂) ↪ G₀ *_B G₀` of the paper argument,
  followed by subgroup permanence.
* `signFreeCollapseDefect_eq_of_isOperatorMF_symmetricDouble` — the same with
  the identification taken at the *printed* defect `D/⟨w⟩` rather than at the
  witness-quantified collapse defect `D_coll`.  The equality `D_coll = D/⟨w⟩` is
  then a conclusion, which is the order the paper argument actually establishes
  it in.
* `manuscriptExactRadical_of_isOperatorMF_symmetricDouble` — both radical
  identities at once, for `E/⟨w⟩` and for `E`.
* `exactRadical_of_isMFTrace_symmetricDouble` — the entry point in trace form.
  An MF trace on `C⋆(G *_Γ G)` in Shulman's sense (`Analysis.ShulmanTraceClasses`)
  is enough, through `ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal`.

## Why the symmetric form is the right target

Shulman's Theorem 10 is a statement about `A *_C A`: two copies of one separable
MF algebra over one subalgebra.  The general amalgam `A *_C B` is a strictly
larger theorem.  The covering equivalence proved in `SymmetricDoubleCovering`
means the `C₂` free-lamp amalgam needs only the symmetric form, so the paper
argument's detour through a second residually finite group is not needed on the
group side once the identification is in hand — only the embedding, or the
isomorphism, and then the symmetric theorem.

## The two gaps, stated plainly

1. The identification of `(E/⟨w⟩)/D` with a free-lamp amalgam is a hypothesis in
   every declaration below.  It is a presentation calculation (`d = tct⁻¹`
   replaces `c`; the imposed relation `[d, B] = 1` makes the transported lamp
   relators redundant, and the central mark dies because `w = u²`), and it is
   not formalized.  Neither is the group `Σ` itself, nor the identification of
   the printed defect with the normal closure of the single commutator
   `⁅v₁, d⁆`.
2. Operator MF of the symmetric double is also a hypothesis.  Nothing in this
   tree proves it: `KunThomShulmanDouble.exists_not_isOperatorMF_symmetricDouble`
   shows it is false for general pairs, so it can only ever be proved from
   properties of the particular pair — which is where Shulman's C⋆-theorem, and
   the residual finiteness of `Σ`, enter.

Neither literature theorem is added as a hypothesis-free fact.  Callers supply
the proof terms at the boundary these declarations name.
-/

namespace GroupApproximation
namespace AmalgamMFTrace

open LiteralNonMFPresentation LiteralSignFreeQuotient
open LiteralSignFreeRadicalReduction

noncomputable section

/-! ## The identification turns the endpoint into the symmetric statement -/

/-- **The exact residual identity is equivalent to operator MF of a symmetric
double**, once the terminal quotient `(E/⟨w⟩)/D` is identified with a `C₂`
free-lamp amalgam `G *_Γ (Γ × C₂)`.

The forward direction reads the MF property of the terminal quotient off the
`Iff` of `manuscriptSignFreeRadicalReduction` and pushes it through the covering
equivalence; the reverse direction pulls the symmetric theorem back the same
way.  No property of `G` or `Γ` is used: the covering equivalence of
`SymmetricDoubleCovering` is unconditional. -/
theorem exactRadical_iff_isOperatorMF_symmetricDouble
    {G : Type} [Group G] {Γ : Subgroup G}
    (e : (SignFreeQuotient ⧸ signFreeCollapseDefect) ≃* FreeLamp G Γ FlipC2) :
    actualCoronaMFResidual MarkedGroup = signFreeCollapseDefect.comap proj ↔
      IsOperatorMF (SymmetricDouble G Γ) := by
  obtain ⟨-, -, hiff⟩ := manuscriptSignFreeRadicalReduction
  constructor
  · intro hEq
    refine isOperatorMF_symmetricDouble_of_isOperatorMF_freeLampFlip G Γ ?_
    exact CommensurabilityInvariance.isOperatorMF_of_mulEquiv e
      ((isCDEOperatorMF_iff_isOperatorMF
        (SignFreeQuotient ⧸ signFreeCollapseDefect)).mp (hiff.mp hEq))
  · intro hMF
    refine hiff.mpr ((isCDEOperatorMF_iff_isOperatorMF
      (SignFreeQuotient ⧸ signFreeCollapseDefect)).mpr ?_)
    exact CommensurabilityInvariance.isOperatorMF_of_mulEquiv e.symm
      (isOperatorMF_freeLampFlip_of_isOperatorMF_symmetricDouble G Γ hMF)

/-- **The manuscript's own shape of the input.**  The paper argument does not
produce an isomorphism onto a symmetric double; it produces an *embedding* of
`Σ *_B (B × C₂)` into `G₀ *_B G₀` by the normal-form theorem for amalgamated
free products, and then uses that subgroups of MF groups are MF.  That is
exactly this statement, with `IsOperatorMF.comap` supplying the permanence. -/
theorem exactRadical_of_injective_symmetricDouble
    {G : Type} [Group G] {Γ : Subgroup G}
    (f : (SignFreeQuotient ⧸ signFreeCollapseDefect) →* SymmetricDouble G Γ)
    (hf : Function.Injective f) (h : IsOperatorMF (SymmetricDouble G Γ)) :
    actualCoronaMFResidual MarkedGroup = signFreeCollapseDefect.comap proj := by
  obtain ⟨-, -, hiff⟩ := manuscriptSignFreeRadicalReduction
  exact hiff.mpr ((isCDEOperatorMF_iff_isOperatorMF
    (SignFreeQuotient ⧸ signFreeCollapseDefect)).mpr (h.comap f hf))

/-! ## Taking the identification at the printed defect instead

`signFreeCollapseDefect` quantifies over *every* involutive compression witness
in `E/⟨w⟩`, while the manuscript's presentation calculation identifies the
quotient by the single normal subgroup `D/⟨w⟩` generated by the base
commutators of the printed witness.  The two are equal, but the paper's proof
of `D_coll ≤ D/⟨w⟩` runs through the radical — it is a consequence of the MF
conclusion, not an input to it.  The statements below respect that order: they
take the identification at an arbitrary normal `N ≤ D_coll` and *derive*
`D_coll = N`. -/

/-- **`thm:collapse` at the literal witness.**  The collapse defect of the
sign-free quotient lies in that quotient's MF radical.  This is the universe-`0`
instance of `CollapseUniverseScope.involutiveCollapseDefect_le_actualCoronaMFResidual`
at the Kazhdan base image `Lbar` and the compressor `proj stable`. -/
theorem signFreeCollapseDefect_le_actualCoronaMFResidual :
    signFreeCollapseDefect ≤ actualCoronaMFResidual SignFreeQuotient :=
  CollapseUniverseScope.involutiveCollapseDefect_le_actualCoronaMFResidual
    Lbar_hasKazhdanPropertyT Lbar_compressed

/-- **The defect is pinned by the identification, not assumed to be.**  Let `N`
be any normal subgroup of `E/⟨w⟩` inside the collapse defect — the manuscript's
`D/⟨w⟩` is one, by `LiteralSignFreeRadicalReduction.collapsedCommutator_mem_defect`
and normality — and suppose `(E/⟨w⟩)/N` is the `C₂` free-lamp amalgam of a pair
whose symmetric double is operator MF.  Then

* the collapse defect *equals* `N`;
* the MF radical of `E/⟨w⟩` equals `N`; and
* the MF radical of `E` is its preimage.

The sandwich is `N ≤ D_coll ≤ Res_MF(E/⟨w⟩) ≤ N`, the last inclusion by
functoriality of the radical against a trivial radical downstairs.  So the
paper-level obligation may be stated at the printed defect, which is what the
presentation calculation actually produces. -/
theorem signFreeCollapseDefect_eq_of_isOperatorMF_symmetricDouble
    {G : Type} [Group G] {Γ : Subgroup G}
    {N : Subgroup SignFreeQuotient} [N.Normal] (hle : N ≤ signFreeCollapseDefect)
    (e : (SignFreeQuotient ⧸ N) ≃* FreeLamp G Γ FlipC2)
    (h : IsOperatorMF (SymmetricDouble G Γ)) :
    signFreeCollapseDefect = N ∧
      actualCoronaMFResidual SignFreeQuotient = N ∧
        actualCoronaMFResidual MarkedGroup =
          signFreeCollapseDefect.comap proj := by
  haveI : Countable (SignFreeQuotient ⧸ N) :=
    Function.Surjective.countable (QuotientGroup.mk'_surjective N)
  have hbotN : actualCoronaMFResidual (SignFreeQuotient ⧸ N) = ⊥ :=
    isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp
      ((isCDEOperatorMF_iff_isOperatorMF (SignFreeQuotient ⧸ N)).mpr
        (CommensurabilityInvariance.isOperatorMF_of_mulEquiv e.symm
          (isOperatorMF_freeLampFlip_of_isOperatorMF_symmetricDouble G Γ h)))
  have hResLe : actualCoronaMFResidual SignFreeQuotient ≤ N := by
    intro g hg
    have hmap : (QuotientGroup.mk' N) g ∈
        actualCoronaMFResidual (SignFreeQuotient ⧸ N) :=
      map_actualCoronaMFResidual_le (QuotientGroup.mk' N) ⟨g, hg, rfl⟩
    rw [hbotN, Subgroup.mem_bot, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hmap
    exact hmap
  have hdefect : signFreeCollapseDefect = N :=
    le_antisymm (signFreeCollapseDefect_le_actualCoronaMFResidual.trans hResLe)
      hle
  have hres : actualCoronaMFResidual SignFreeQuotient = N := by
    refine le_antisymm hResLe ?_
    rw [← hdefect]
    exact signFreeCollapseDefect_le_actualCoronaMFResidual
  refine ⟨hdefect, hres, ?_⟩
  rw [actualCoronaMFResidual_markedGroup_eq_comap, hres, hdefect]

/-! ## Both radical identities at once -/

/-- **The full exact computation, relative to the identification.**  The
residual of the sign-free quotient is the collapse defect itself, and the
residual of `E` is its preimage.  The first conjunct is the one the manuscript
displays as `Res_MF(E/⟨w⟩) = D`; it needs the collapse reduction together with
triviality of the residual upstairs, which is what the MF hypothesis buys. -/
theorem manuscriptExactRadical_of_isOperatorMF_symmetricDouble
    {G : Type} [Group G] {Γ : Subgroup G}
    (e : (SignFreeQuotient ⧸ signFreeCollapseDefect) ≃* FreeLamp G Γ FlipC2)
    (h : IsOperatorMF (SymmetricDouble G Γ)) :
    actualCoronaMFResidual SignFreeQuotient = signFreeCollapseDefect ∧
      actualCoronaMFResidual MarkedGroup = signFreeCollapseDefect.comap proj := by
  refine ⟨?_, (exactRadical_iff_isOperatorMF_symmetricDouble e).mpr h⟩
  obtain ⟨hcomap, -, -⟩ := manuscriptSignFreeRadicalReduction
  have hbot : actualCoronaMFResidual
      (SignFreeQuotient ⧸ signFreeCollapseDefect) = ⊥ :=
    isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp
      ((isCDEOperatorMF_iff_isOperatorMF
        (SignFreeQuotient ⧸ signFreeCollapseDefect)).mpr
        (CommensurabilityInvariance.isOperatorMF_of_mulEquiv e.symm
          (isOperatorMF_freeLampFlip_of_isOperatorMF_symmetricDouble G Γ h)))
  rw [hcomap, hbot]
  -- the kernel of `mk'` is the subgroup itself; named rather than left to
  -- `simp`, so the step does not move when the simp set does
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_bot, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]

/-! ## The trace form of the obligation -/

/-- **The obligation in Shulman's trace vocabulary.**  An MF trace on the full
group C⋆-algebra of the symmetric double — the five asymptotic clauses of
`ShulmanTrace.MFTraceModel`, measured in the operator norm — closes the exact
residual computation, again relative to the identification.

This is the statement to aim a formalization of Shulman's amalgam theorem at:
the trace side, not the group side, is where the analytic content lives, and
`ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal` already carries the
trace back to the group with nothing left to discharge. -/
theorem exactRadical_of_isMFTrace_symmetricDouble
    {G : Type} [Group G] {Γ : Subgroup G}
    (e : (SignFreeQuotient ⧸ signFreeCollapseDefect) ≃* FreeLamp G Γ FlipC2)
    (h : ShulmanTrace.IsMFTrace
      (fun a : MaximalGroupCStar (SymmetricDouble G Γ) ↦
        canonicalMaximalTrace (SymmetricDouble G Γ) a)) :
    actualCoronaMFResidual MarkedGroup = signFreeCollapseDefect.comap proj :=
  (exactRadical_iff_isOperatorMF_symmetricDouble e).mpr
    (ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal h)

end

end AmalgamMFTrace
end GroupApproximation
