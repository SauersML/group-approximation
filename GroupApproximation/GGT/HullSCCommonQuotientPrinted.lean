import GroupApproximation.GGT.HullSCUnionGeometryAssembly
import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Manuscript.NonMF.TorsionFreeRelativeQuotient

/-!
# `HullCommonQuotientPrinted` is not a citation

`non_mf_groups_exist.tex`, the proof of `cor:relative-quotient`:

> Hull's common quotient theorem [Hull, Corollary 7.4], applied to `G` and to
> the group `Q` of Theorem `thm:torsion-free`, gives a common quotient `P` that
> is acylindrically hyperbolic, with the map from `G` injective on a prescribed
> finite subset, since a torsion-free acylindrically hyperbolic group has no
> nontrivial finite normal subgroup.  For finitely generated inputs, the proof
> of that corollary applies Theorem `thm:hull` to the free product `G * Q` and
> then to the resulting quotient, each time with finitely many elements `gᵢ`, so
> `P` is torsion-free and finitely presented, as in the remark after
> Theorem `thm:hull`.

`Manuscript.NonMF.TorsionFreePrinted.HullCommonQuotientPrinted` is that
corollary in the form the printed proof uses it, and until this module nothing
inhabited it: `TorsionFreeRelativeQuotient.manuscriptRelativeQuotient` takes it
as a third hypothesis alongside `FournierFacioParagraph` and
`HullPrintedInputs`.

**It is a theorem of `HullSC.HullOneStepStatement`** — Hull's Theorem 7.1 for a
single relator — **and of nothing else.**  `hullCommonQuotientPrinted_of_oneStep`
proves it, and `manuscriptRelativeQuotient_of_oneStep` re-proves
`cor:relative-quotient` with the Corollary 7.4 hypothesis removed.

## What the docstring this module supersedes said

`GGT/HullSCCommonQuotient.lean` proves Hull's Corollary 7.4 at
`Manuscript.NonMF.TheoremC.HullCommonQuotientStatement`, the form the
*superseded* Fournier-Facio paragraph consumed, by exactly the printed proof:
two applications of Theorem 7.1 to the free product, the second legitimate
because `HullStep` carries `suitable_map_family`.  The header of
`Manuscript/NonMF/TorsionFreeRelativeQuotient.lean` nevertheless says

> Deriving it instead from `HullSmallCancellationPrinted` applied twice to
> `G * Q` would need acylindrical hyperbolicity of a free product of two
> acylindrically hyperbolic groups, and the suitability of the two factors in
> it; this repository has none of that, so the honest carrier is the citation.

Both halves of that "none of that" are on `origin/main`.  The free-product
geometry is `HullSCUnionGeometry.Assembly.freeProductUnionGeometryStatement_unconditional`
— hyperbolicity of `Γ(E ∗ H, A ⊔ B)` and acylindricity of the translation action
on it, both proved — and the suitability of the two factors on that alphabet is
`HullSC.actsNonElementarily_range_of_wordDist_eq` with
`Manuscript.NonMF.Saturation.suitable_of_torsionFree`.

The one thing the sentence gets right is that the *printed* `thm:hull` will not
do it.  `TorsionFreePrinted.HullSmallCancellationPrinted` produces a
`HullCorrectedInputs.HullQuotientNG`, which carries neither `alphabet_image` nor
`suitable_map_family`, and the second application of the theorem needs both: the
subgroup that has to stay suitable across the first quotient is the image of the
*second* factor, which is not the subgroup the first quotient was taken along,
and the injectivity radius of the composite is uncontrolled without the alphabet
clause.  So the reduction here is to Hull's Theorem 7.1 **as his construction
produces it**, `HullSC.HullOneStepStatement`, which is also what
`HullSC.hullBallFormNG_of_oneStep` reduces the printed form to.  That is a
statement about the same theorem of the same paper, and it is the section's
other citation; it is not the printed sentence.

## The delta from `TheoremC.HullCommonQuotientStatement`

Four differences, all of them in the printed statement's favour except the last,
which the existing proof already establishes and merely discards:

* the second group carries `[IsAcylindricallyHyperbolic G₂]` where
  `TheoremC.HullCommonQuotientStatement` carries `Infinite`, hyperbolicity and
  property (T).  Those three are used in the whole union-geometry chain for one
  purpose, visible in `HullSCUnionGeometry.freeProductUnionGeometryStatement_of`:
  to produce `Nonempty (HullGeneratingSet H)`.  Acylindrical hyperbolicity gives
  that outright, by `TorsionFree.exists_hullGeneratingSet`, since the class is
  taken here in its Cayley-graph form.  `HullSCUnionGeometry.isAcylindrical_unionAlphabet`
  and `HullSCUnionGeometry.exists_isHyperbolicSpace_cayley_unionAlphabet` take
  two Hull generating sets and no group-theoretic hypothesis at all;
* the prescribed set is a finite `Set G₁` rather than a `Finset`;
* **both** surjections are demanded.  `hullCommonQuotient_of_tower_corrected`
  builds both — `hEtop` and `hHtop` — and exposes only the first, using the
  second to transport property (T);
* property (T) of the quotient is not asserted, because
  `cor:relative-quotient` derives it from surjectivity of `a₂` and property (T)
  of `Q`.

## This does not resurrect the refuted free-product input

`HullSCCommonQuotientCorrected.not_freeProductStatement` disproves
`HullSC.FreeProductStatement` by taking `H = FreeGroup (Fin 1)`: the image of an
infinite cyclic group is a group of powers of one element, so it never acts
non-elementarily.  `FreeGroup (Fin 1)` is infinite, finitely presented and
torsion-free, which is all that statement asked of its second factor — but it is
virtually cyclic, and `nonElementary` is a field of
`TorsionFree.IsAcylindricallyHyperbolic`, so it does not satisfy the hypothesis
`nonempty_freeProductInput_of_acylindricallyHyperbolic` puts on `H`.  The
refutation is the reason that hypothesis is there and it is not a refutation of
this module.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

/-! ## The free product of two acylindrically hyperbolic groups -/

/-- **The free product input of Hull's Corollary 7.4, over two acylindrically
hyperbolic factors, unconditionally.**

Every field of `FreeProductInput` is discharged:

* `Gamma` is `Monoid.Coprod E H`; finite presentation and torsion-freeness
  (`Higman.isPowerTorsionFree_coprod`, Kurosh in the form this repository proves
  it) are closure properties of the free product;
* `inj` is `coprod_inl_injective`;
* `alphabet` is the union of the two factors' Hull alphabets, whose Cayley graph
  is hyperbolic (`exists_isHyperbolicSpace_cayley_unionAlphabet`), whose
  translation action is acylindrical (`isAcylindrical_unionAlphabet`), and on
  which `E ∗ H` acts non-elementarily because either factor does;
* `suitable` and `suitable'` are Hull's Definition 1.4 for the two factors:
  clause (1) because each factor is isometrically embedded in the union and acts
  non-elementarily on its own Cayley graph, and clause (3) free over a
  torsion-free ambient group.

The two `IsAcylindricallyHyperbolic` hypotheses are what
`HullSCCommonQuotientCorrected.not_freeProductStatement` shows cannot be
dropped from the second factor. -/
theorem nonempty_freeProductInput_of_acylindricallyHyperbolic
    (E H : Type) [Group E] [Group H]
    [Group.IsFinitelyPresented E] [Group.IsFinitelyPresented H]
    [IsAcylindricallyHyperbolic E] [IsAcylindricallyHyperbolic H]
    (hEtf : IsPowerTorsionFree E) (hHtf : IsPowerTorsionFree H) :
    Nonempty (FreeProductInput E H) := by
  obtain ⟨A⟩ := exists_hullGeneratingSet E
  obtain ⟨B⟩ := exists_hullGeneratingSet H
  obtain ⟨δ, hδ⟩ :=
    HullSCUnionGeometry.exists_isHyperbolicSpace_cayley_unionAlphabet A B
  have hacyl := HullSCUnionGeometry.isAcylindrical_unionAlphabet A B
  have hcar : (unionAlphabet A.alphabet B.alphabet).carrier
      = UnionCarrier A.alphabet B.alphabet := rfl
  have hEne : ActsNonElementarily
      (Monoid.Coprod.inl : E →* Monoid.Coprod E H).range
      (Cayley.base (unionAlphabet A.alphabet B.alphabet)) :=
    actsNonElementarily_range_of_wordDist_eq
      (Monoid.Coprod.inl : E →* Monoid.Coprod E H)
      (wordDist_inl_eq hcar) A.nonElementary
  have hHne : ActsNonElementarily
      (Monoid.Coprod.inr : H →* Monoid.Coprod E H).range
      (Cayley.base (unionAlphabet A.alphabet B.alphabet)) :=
    actsNonElementarily_range_of_wordDist_eq
      (Monoid.Coprod.inr : H →* Monoid.Coprod E H)
      (wordDist_inr_eq hcar) B.nonElementary
  have htf : IsPowerTorsionFree (Monoid.Coprod E H) :=
    Higman.isPowerTorsionFree_coprod hEtf hHtf
  exact ⟨{ Gamma := Monoid.Coprod E H
           group := inferInstance
           fp := inferInstance
           torsionFree := htf
           emb := Monoid.Coprod.inl
           emb' := Monoid.Coprod.inr
           inj := coprod_inl_injective
           alphabet :=
             ⟨unionAlphabet A.alphabet B.alphabet, δ, hδ, hacyl,
               actsNonElementarily_top_of_subgroup hEne⟩
           suitable := suitable_of_torsionFree htf hEne
           suitable' := suitable_of_torsionFree htf hHne }⟩

/-! ## Corollary 7.4 at the printed statement -/

/-- **`HullCommonQuotientPrinted` from Hull's Theorem 7.1 for every `m`.**

The proof is `hullCommonQuotient_of_tower_corrected`'s, with the free product
input supplied by `nonempty_freeProductInput_of_acylindricallyHyperbolic` rather
than assumed, and with the second surjection kept:

* form `Γ = G₁ ∗ G₂` with both factors suitable on the union alphabet;
* pick a radius `R₁` whose ball of `Γ(Γ, 𝒜)` contains the image of `Ω`, and a
  finite generating family of `Γ`;
* **first application**, at `Γ`, along the image of `G₁`, with the image of `G₂`
  carried as the prescribed suitable family: the display
  `Q₁ = ⟨q₁(t₁),…,q₁(t_m)⟩ ≤ q₁(G₁) ≤ Q₁` makes `Q₁` a quotient of `G₁`;
* **second application**, at `Q₁`, along the image of `G₂` — which is still
  suitable, by `HullStep.suitable_map_family`, and that clause is why the
  printed `thm:hull` cannot be used here;
* torsion-freeness through `torsionFree_of_finiteOrder_lift`, finite
  presentation through `Group.IsFinitelyPresented.of_surjective` and the kernel
  clause, acylindrical hyperbolicity from the quotient's own Hull alphabet, and
  injectivity on `Ω` from the two ball clauses composed.

`HasTrivialFiniteRadical` is not used: over torsion-free groups it is a theorem
(`TorsionFreePrinted.hasTrivialFiniteRadical_of_torsionFree`), and the printed
proof supplies it only to meet the hypothesis `K(Gᵢ) = 1` of Hull's own
statement.  The two hypotheses are kept in the Prop because the print states
them, and they are discarded here because this proof does not go through Hull's
statement but through his Theorem 7.1. -/
theorem hullCommonQuotientPrinted_of_tower (htower : HullTowerStatement.{0}) :
    HullCommonQuotientPrinted := by
  classical
  intro G₁ G₂ instG₁ instG₂ instfp₁ instfp₂ instah₁ instah₂ h₁tf h₂tf _ _ Ω hΩ
  letI := instG₁
  letI := instG₂
  haveI := instfp₁
  haveI := instfp₂
  haveI := instah₁
  haveI := instah₂
  -- `Γ = G₁ ∗ G₂`, with both factors suitable.
  obtain ⟨I⟩ :=
    nonempty_freeProductInput_of_acylindricallyHyperbolic G₁ G₂ h₁tf h₂tf
  -- a ball of `Γ(Γ, 𝒜)` containing the image of the prescribed finite set
  have hΩfin : ((I.emb : G₁ → I.Gamma) '' Ω).Finite := hΩ.image _
  obtain ⟨R₁, hR₁⟩ := exists_subset_cayleyBall I.alphabet.alphabet hΩfin
  -- a finite generating family of `Γ`
  obtain ⟨m, t, htop⟩ := exists_finite_generating_family I.Gamma
  -- **First application**: absorb all of `Γ` into the image of `G₁`.
  obtain ⟨D₁⟩ := htower (S := fun _ : Fin 1 => I.emb'.range)
    I.torsionFree I.alphabet
    I.suitable (fun _ => I.suitable') t R₁
  have hq₁top : I.emb.range.map D₁.step.q = ⊤ :=
    map_eq_top_of_generators_mem D₁.step.q D₁.step.surjective htop D₁.mem_map
  have hQ₁tf : IsPowerTorsionFree D₁.step.Q :=
    torsionFree_of_finiteOrder_lift I.torsionFree D₁.step.q
      D₁.step.finiteOrder_lift
  obtain ⟨T₁, -, hT₁ker⟩ := D₁.kerNormallyGenerated
  haveI : Group.IsFinitelyPresented D₁.step.Q :=
    Group.IsFinitelyPresented.of_surjective D₁.step.q D₁.step.surjective
      ⟨(T₁ : Set I.Gamma), T₁.finite_toSet, hT₁ker.symm⟩
  -- a ball of `Γ(Q₁, 𝒜₁)` containing the image of the prescribed finite set
  have hΩfin₂ : ((D₁.step.q : I.Gamma → D₁.step.Q) ''
      ((I.emb : G₁ → I.Gamma) '' Ω)).Finite := hΩfin.image _
  obtain ⟨R₂, hR₂⟩ :=
    exists_subset_cayleyBall D₁.step.hullSet.alphabet hΩfin₂
  -- a finite generating family of `Q₁`
  obtain ⟨m₂, t₂, htop₂⟩ := exists_finite_generating_family D₁.step.Q
  -- **Second application**: absorb all of `Q₁` into the image of `G₂`.
  obtain ⟨D₂⟩ := htower (S := fun j : Fin 0 => Fin.elim0 j) hQ₁tf D₁.step.hullSet
    (D₁.step.suitable_map_family 0) (fun j : Fin 0 => Fin.elim0 j) t₂ R₂
  have hq₂top : (I.emb'.range.map D₁.step.q).map D₂.step.q = ⊤ :=
    map_eq_top_of_generators_mem D₂.step.q D₂.step.surjective htop₂ D₂.mem_map
  have hQ₂tf : IsPowerTorsionFree D₂.step.Q :=
    torsionFree_of_finiteOrder_lift hQ₁tf D₂.step.q D₂.step.finiteOrder_lift
  obtain ⟨T₂, -, hT₂ker⟩ := D₂.kerNormallyGenerated
  haveI hQ₂fp : Group.IsFinitelyPresented D₂.step.Q :=
    Group.IsFinitelyPresented.of_surjective D₂.step.q D₂.step.surjective
      ⟨(T₂ : Set D₁.step.Q), T₂.finite_toSet, hT₂ker.symm⟩
  -- the composite `Γ ↠ Q₂`
  have hcomp : ∀ (K : Subgroup I.Gamma),
      (K.map D₁.step.q).map D₂.step.q
        = K.map (D₂.step.q.comp D₁.step.q) := by
    intro K
    rw [Subgroup.map_map]
  -- `G₁ ↠ Q₂`
  have hEtop : I.emb.range.map (D₂.step.q.comp D₁.step.q) = ⊤ := by
    rw [← hcomp, hq₁top]
    exact Subgroup.map_top_of_surjective D₂.step.q D₂.step.surjective
  -- `G₂ ↠ Q₂`
  have hHtop : I.emb'.range.map (D₂.step.q.comp D₁.step.q) = ⊤ := by
    rw [← hcomp]
    exact hq₂top
  have hsurj : ∀ (K : Type) [Group K] (e : K →* I.Gamma),
      e.range.map (D₂.step.q.comp D₁.step.q) = ⊤ →
        Function.Surjective ((D₂.step.q.comp D₁.step.q).comp e) := by
    intro K _ e hK y
    have hy : y ∈ e.range.map (D₂.step.q.comp D₁.step.q) := by
      rw [hK]
      exact Subgroup.mem_top y
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hg
    refine ⟨x, ?_⟩
    show (D₂.step.q.comp D₁.step.q) (e x) = y
    rw [hx]
    exact hgy
  refine ⟨D₂.step.Q, D₂.step.group,
    (D₂.step.q.comp D₁.step.q).comp I.emb,
    (D₂.step.q.comp D₁.step.q).comp I.emb',
    hsurj G₁ I.emb hEtop, hsurj G₂ I.emb' hHtop, hQ₂fp, hQ₂tf,
    isAcylindricallyHyperbolic_of_hullGeneratingSet D₂.step.hullSet, ?_⟩
  -- injectivity on the prescribed finite set
  intro x hx y hy hxy
  have hx₁ : I.emb x ∈ cayleyBall I.alphabet.alphabet R₁ :=
    hR₁ (Set.mem_image_of_mem _ hx)
  have hy₁ : I.emb y ∈ cayleyBall I.alphabet.alphabet R₁ :=
    hR₁ (Set.mem_image_of_mem _ hy)
  have hx₂ : D₁.step.q (I.emb x) ∈ cayleyBall D₁.step.hullSet.alphabet R₂ :=
    hR₂ (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hx))
  have hy₂ : D₁.step.q (I.emb y) ∈ cayleyBall D₁.step.hullSet.alphabet R₂ :=
    hR₂ (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hy))
  have hstep₂ : D₂.step.q (D₁.step.q (I.emb x))
      = D₂.step.q (D₁.step.q (I.emb y)) := hxy
  have hstep₁ : D₁.step.q (I.emb x) = D₁.step.q (I.emb y) :=
    D₂.step.injOn hx₂ hy₂ hstep₂
  exact I.inj (D₁.step.injOn hx₁ hy₁ hstep₁)

/-- **`HullCommonQuotientPrinted` from Hull's Theorem 7.1 for one relator.**

`hullTower_of_oneStep` is the induction on `m`, so the whole of Hull's
Corollary 7.4, in the form the printed proof of `cor:relative-quotient` applies
it, rests on `HullOneStepStatement` and nothing else. -/
theorem hullCommonQuotientPrinted_of_oneStep (h : HullOneStepStatement.{0}) :
    HullCommonQuotientPrinted :=
  hullCommonQuotientPrinted_of_tower (hullTowerStatement_of_oneStep h)

/-! ## `cor:relative-quotient` with one citation fewer -/

/-- **`cor:relative-quotient`, from two hypotheses instead of three.**

`TorsionFreePrinted.manuscriptRelativeQuotient` takes `FournierFacioParagraph`,
`HullPrintedInputs` and `HullCommonQuotientPrinted`.  The third is now proved,
so the corollary rests on the Fournier-Facio paragraph and on Hull's
Theorem 7.1 — the latter in the one-relator construction form, which is a
strictly stronger reading of `thm:hull` than the printed sentence and is the
form `HullSC.hullBallFormNG_of_oneStep` already reduces the printed statement
to.  `HullPrintedInputs` is still needed for Osin's Lemma 7.1 and for
`lem:saturation`, which runs off the printed statement. -/
theorem manuscriptRelativeQuotient_of_oneStep (hFFF : FournierFacioParagraph)
    (hHull : HullPrintedInputs.{0}) (hOne : HullOneStepStatement.{0}) :
    PrintedRelativeQuotient :=
  manuscriptRelativeQuotient hFFF hHull (hullCommonQuotientPrinted_of_oneStep hOne)

/-! ## The axioms

`#audit_closed_axioms` is not available for these names: it rejects a
declaration with a leading input, and two of the three endpoints take Hull's
Theorem 7.1 as a hypothesis, which is the point.  `#audit_axioms` is the gate
that applies — it fails the build on anything outside
`propext / Classical.choice / Quot.sound` — and what it has to report is that no
`sorryAx` reaches them: the reduction of Corollary 7.4 to Theorem 7.1 is
complete, not partial. -/

#audit_axioms GroupApproximation.HullSC.nonempty_freeProductInput_of_acylindricallyHyperbolic

#audit_axioms GroupApproximation.HullSC.hullCommonQuotientPrinted_of_oneStep

#audit_axioms GroupApproximation.HullSC.manuscriptRelativeQuotient_of_oneStep

end HullSC
end GroupApproximation
