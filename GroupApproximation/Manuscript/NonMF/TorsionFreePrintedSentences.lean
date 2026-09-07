import GroupApproximation.Manuscript.NonMF.RegularNonMFAlgebra

/-!
# Sentence carriers for the printed proofs of `sec:torsion-free`

`non_mf_groups_exist.tex`, the proofs of `lem:saturation`, `thm:torsion-free`,
`cor:relative-quotient` and `cor:regular-nonmf-algebra`.

The statements of all four are already carried, each by one closed proposition
with the section's citations as its explicit hypotheses.  This module adds the
**printed-proof sentences**: one `manuscriptSentence_*` lemma per printed
sentence, its docstring quoting the sentence, its statement the printed clause,
and its proof drawn from the landed modules.  The pattern is
`Manuscript/OneSidedMFRadical/NormalKazhdanPrintedRoute.lean`.

Every citation stays where it was.  A sentence that **is** a cited input becomes
a lemma taking the corresponding named proposition as a hypothesis and returning
the printed clause — `manuscriptSentence_saturationOsinNonElementary` takes
`OsinLemma71Printed`, `manuscriptSentence_saturationApplyHull` takes
`HullSmallCancellationPrinted`, `manuscriptSentence_relativeQuotientCommonQuotient`
takes `HullCommonQuotientPrinted`, and
`manuscriptSentence_algebraSimpleUniqueTraceStableRank` takes both C⋆-algebraic
propositions.  Nothing is assumed that the statement-level endpoints do not
already assume, and no sentence is proved from a hypothesis its own printed
sentence does not cite.

Three printed sentences of the section are **not** citations even though the
print writes them as such, and their carriers take no hypothesis:

* `manuscriptSentence_saturationTwoGeneratedSuitable` — Hull's Corollary 5.7
  with Lemma 5.8, proved over a torsion-free ambient group, with `A' = A`;
* `manuscriptSentence_relativeQuotientTrivialFiniteRadical` and
  `manuscriptSentence_algebraTrivialFiniteRadical` — *"a torsion-free
  acylindrically hyperbolic group has no nontrivial finite normal subgroup"*,
  where normality is not even used.

One printed clause has no carrier and cannot have one here: *"it contains a
non-degenerate hyperbolically embedded subgroup [Osin, Theorem 1.2]"*.  This
development has no vocabulary for *hyperbolically embedded*, and the printed
proof uses that clause only to reach the hypothesis of Dahmani--Guirardel--Osin,
which `DGOTheorem235Printed` states directly.  The docstring of
`manuscriptSentence_algebraTrivialFiniteRadical` records the omission.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrintedSentences

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.Manuscript.NonMF.HullCorrectedInputs
open GroupApproximation.ReducedGroupCStarTrace

/-! ## `lem:saturation`, printed proof -/

/-- **`lem:saturation`, printed sentence.**

> The subgroup `N` is normal, and it is infinite because `G` is torsion-free and
> `N ≠ 1` …

Both halves: the set `N` is infinite, and `N` meets each of its conjugates in an
infinite set, which is Osin's `s`-normality and the hypothesis his Lemma 7.1
takes. -/
theorem manuscriptSentence_saturationNormalInfinite {G : Type} [Group G]
    (hG : IsPowerTorsionFree G) (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    (N : Set G).Infinite ∧ HullSuitable.IsSNormal N :=
  ⟨infinite_coe_of_torsionFree_of_ne_bot hG hN, isSNormal_of_torsionFree hG N hN⟩

/-- **`lem:saturation`, printed sentence.**

> … so it acts non-elementarily on `Cay(G,A)` by Osin [Lemma 7.1] …

The citation, in the printed case: `G` torsion-free, `N` normal and nontrivial.
`OsinLemma71Printed` is that statement and this lemma is its application. -/
theorem manuscriptSentence_saturationOsinNonElementary
    (hOsin : OsinLemma71Printed.{0}) {G : Type} [Group G]
    (hG : IsPowerTorsionFree G) (A : HullGeneratingSet G) (N : Subgroup G)
    [N.Normal] (hN : N ≠ ⊥) :
    ActsNonElementarily N (Cayley.base A.alphabet) :=
  hOsin A hG N hN

/-- **`lem:saturation`, printed sentence.**

> … since `G` is torsion-free, `N` normalizes no nontrivial finite subgroup, so
> `N` is suitable.

Both clauses.  The first is free over a torsion-free group — there is no
nontrivial finite subgroup for anything to normalize — and with the
non-elementarity just obtained it is the whole of Hull's Definition 1.4. -/
theorem manuscriptSentence_saturationSuitable {G : Type} [Group G]
    (hG : IsPowerTorsionFree G) {A : Alphabet G} {N : Subgroup G}
    (hne : ActsNonElementarily N (Cayley.base A)) :
    HullSuitable.NormalizesNoNontrivialFinite N ∧ Suitable A N :=
  ⟨HullSuitable.normalizesNoNontrivialFinite_of_torsionFree hG N,
    suitable_of_torsionFree hG hne⟩

/-- **`lem:saturation`, printed sentence.**

> By Hull [Corollary 5.7 and Lemma 5.8], `N` contains two elements `h₁, h₂` such
> that `N₀ = ⟨h₁,h₂⟩` is again suitable, possibly with respect to a larger
> generating set `A' ⊇ A` …

**This sentence is a citation in the print and a theorem here.**  Over a
torsion-free ambient group the conclusion holds with `A' = A`: the repository's
non-elementarity is *contains two independent loxodromic elements*, so the pair
already generates a non-elementary subgroup, and Hull's clause (3) is free.  So
the lemma takes no hypothesis, and the existential over `A'` is witnessed by `A`
itself.  `HullSuitablePairPrinted` records the printed sentence including its
alphabet hedge. -/
theorem manuscriptSentence_saturationTwoGeneratedSuitable {G : Type} [Group G]
    (hG : IsPowerTorsionFree G) (A : HullGeneratingSet G) {N : Subgroup G}
    (hN : Suitable A.alphabet N) :
    ∃ A' : HullGeneratingSet G, A.alphabet.carrier ⊆ A'.alphabet.carrier ∧
      ∃ h₁ ∈ N, ∃ h₂ ∈ N,
        Suitable A'.alphabet (Subgroup.closure ({h₁, h₂} : Set G)) :=
  hullSuitablePair_of_torsionFree hG A hN

/-- **`lem:saturation`, printed sentence.**

> … and Theorem `thm:hull` holds for `A'` as well, since every finite subset of
> `G` lies in a ball of `Cay(G,A')`.

Two clauses.  The "since" clause is `exists_subset_cayleyBall`, proved.  The
main clause costs nothing: `HullSmallCancellationPrinted` is quantified over
every Hull generating set of `G`, so the same term that gives `thm:hull` at `A`
gives it at `A'`. -/
theorem manuscriptSentence_saturationHullAtLargerAlphabet
    (hHull : HullSmallCancellationPrinted.{0}) {G : Type} [Group G]
    [IsAcylindricallyHyperbolic G] (A' : HullGeneratingSet G)
    {N₀ : Subgroup G} (hN₀ : Suitable A'.alphabet N₀) {m : ℕ} (g : Fin m → G)
    {Ω : Set G} (hΩ : Ω.Finite) :
    (∀ F : Set G, F.Finite → ∃ R : ℕ, F ⊆ cayleyBall A'.alphabet R) ∧
      Nonempty (HullQuotientNG N₀ g Ω) :=
  ⟨fun _ hF => exists_subset_cayleyBall A'.alphabet hF, hHull A' hN₀ g hΩ⟩

/-- **`lem:saturation`, printed sentence.**

> Apply Theorem `thm:hull` to `N₀` with `g₁, …, g_m` a finite generating set of
> `G` and with the set `Ω`.

The finite generating family is `exists_finite_generating_family`, proved from
finite presentation; the application is the citation. -/
theorem manuscriptSentence_saturationApplyHull
    (hHull : HullSmallCancellationPrinted.{0}) {G : Type} [Group G]
    [Group.IsFinitelyPresented G] [IsAcylindricallyHyperbolic G]
    (A' : HullGeneratingSet G) {N₀ : Subgroup G}
    (hN₀ : Suitable A'.alphabet N₀) {Ω : Set G} (hΩ : Ω.Finite) :
    ∃ (m : ℕ) (g : Fin m → G), Subgroup.closure (Set.range g) = ⊤ ∧
      Nonempty (HullQuotientNG N₀ g Ω) := by
  obtain ⟨m, g, htop⟩ := exists_finite_generating_family G
  exact ⟨m, g, htop, hHull A' hN₀ g hΩ⟩

/-- **`lem:saturation`, printed sentence.**

> Then `Q = ⟨φ(g₁), …, φ(g_m)⟩ ≤ φ(N₀) ≤ φ(N) ≤ Q`, so `Q = φ(N₀) =
> ⟨φ(h₁), φ(h₂)⟩` and `φ(N) = Q`.

The displayed chain and its two consequences, in the printed order: the images
of the generators lie in `φ(N₀)`, which therefore is everything; the image of a
two-generated subgroup is generated by the two images; and `N₀ ≤ N` pushes the
equality up to `N`. -/
theorem manuscriptSentence_saturationDisplay {G Q : Type} [Group G] [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) {m : ℕ} {g : Fin m → G}
    (htop : Subgroup.closure (Set.range g) = ⊤) {h₁ h₂ : G} {N : Subgroup G}
    (hle : Subgroup.closure ({h₁, h₂} : Set G) ≤ N)
    (hmem : ∀ i : Fin m, q (g i) ∈ (Subgroup.closure ({h₁, h₂} : Set G)).map q) :
    (Subgroup.closure ({h₁, h₂} : Set G)).map q = ⊤ ∧
      Subgroup.closure ({q h₁, q h₂} : Set Q) = ⊤ ∧ N.map q = ⊤ := by
  have h0 := map_eq_top_of_generators_mem q hq htop hmem
  refine ⟨h0, ?_, map_eq_top_of_le q hle h0⟩
  rw [← closure_pair_map q h₁ h₂]
  exact h0

/-- **`lem:saturation`, printed sentence.**

> The quotient is torsion-free by Theorem `thm:hull` …

The clause of `thm:hull` used is the last one: an element of finite order in the
quotient lifts to an element of the *same* order, which over a torsion-free
source can only be the identity. -/
theorem manuscriptSentence_saturationQuotientTorsionFree {G Q : Type} [Group G]
    [Group Q] (hG : IsPowerTorsionFree G) (q : G →* Q)
    (hlift : ∀ y : Q, IsOfFinOrder y → ∃ x : G, q x = y ∧ orderOf x = orderOf y) :
    IsPowerTorsionFree Q :=
  torsionFree_of_finiteOrder_lift hG q hlift

/-- **`lem:saturation`, printed sentence.**

> … and finitely presented because `ker φ` is normally generated by `m`
> elements.

Only finiteness of the normal generating set is used; the bound by `m` is
carried by `HullQuotientNG` and not needed here. -/
theorem manuscriptSentence_saturationQuotientFinitelyPresented {G Q : Type}
    [Group G] [Group.IsFinitelyPresented G] [Group Q] (q : G →* Q)
    (hq : Function.Surjective q) {S : Finset G}
    (hker : q.ker = Subgroup.normalClosure (S : Set G)) :
    Group.IsFinitelyPresented Q :=
  Group.IsFinitelyPresented.of_surjective q hq
    ⟨(S : Set G), S.finite_toSet, hker.symm⟩

/-! ## `thm:torsion-free`, printed proof -/

/-- **`thm:torsion-free`, printed sentence.**

> Let `N` be the normal closure of `S` in `G₀`; it is nontrivial because `S` is.

`S = tJt⁻¹` is nontrivial because `J` is simple, hence nontrivial. -/
theorem manuscriptSentence_theoremNormalClosureNeBot {E : Type} [Group E]
    (F : PrintedFournierFacioData E) :
    F.conjFactor ≠ ⊥ ∧ Subgroup.normalClosure (F.conjFactor : Set E) ≠ ⊥ :=
  ⟨conjFactor_ne_bot F, normalClosure_conjFactor_ne_bot F⟩

/-- **`thm:torsion-free`, printed sentence.**

> By Lemma `lem:saturation` applied to `G₀`, `N`, and `Ω = ∅`, there is a
> surjective homomorphism `φ : G₀ → Q` with `Q` two-generated, finitely
> presented, torsion-free, and acylindrically hyperbolic, and `φ(N) = Q`.

The application, at the empty protected set.  Every printed clause is a field of
`SaturationQuotient`. -/
theorem manuscriptSentence_theoremApplySaturation (hHull : HullPrintedInputs.{0})
    {G₀ : Type} [Group G₀] [Group.IsFinitelyPresented G₀]
    [IsAcylindricallyHyperbolic G₀] (hG₀ : IsPowerTorsionFree G₀)
    (N : Subgroup G₀) [N.Normal] (hN : N ≠ ⊥) :
    Nonempty (SaturationQuotient N (∅ : Set G₀)) :=
  manuscriptSaturation hHull G₀ hG₀ N hN (Ω := (∅ : Set G₀)) Set.finite_empty

/-- **`thm:torsion-free`, printed sentence.**

> The group `Q` is infinite because it is acylindrically hyperbolic …

The non-elementarity clause hands out a loxodromic element, which has infinite
order. -/
theorem manuscriptSentence_theoremQuotientInfinite (Q : Type) [Group Q]
    [IsAcylindricallyHyperbolic Q] : Infinite Q :=
  infinite_of_acylHyperbolic Q

/-- **`thm:torsion-free`, printed sentence.**

> … and it has property (T) as a quotient of `G₀`. -/
theorem manuscriptSentence_theoremQuotientKazhdan {G₀ Q : Type} [Group G₀]
    [Group Q] (hG₀T : HasKazhdanPropertyT.{0, 0} G₀) (q : G₀ →* Q)
    (hq : Function.Surjective q) : HasKazhdanPropertyT.{0, 0} Q :=
  HasKazhdanPropertyT.of_surjective q hq hG₀T

/-- **`thm:torsion-free`, printed sentence.**

> By `eq:defect-functorial`, `φ(S) ≤ 𝔇_Q(φ(Γ))`.

The display applied to `φ`, on top of the section's own `S ≤ 𝔇_{G₀}(Γ)`. -/
theorem manuscriptSentence_theoremDefectFunctorial {E : Type} [Group E]
    (F : PrintedFournierFacioData E) {Q : Type} [Group Q] (phi : E →* Q) :
    F.conjFactor.map phi ≤ OneSidedMFRadical.printedDefect (F.core.map phi) :=
  map_conjFactor_le_printedDefect_of_functorial F phi

/-- **`thm:torsion-free`, printed sentence.**

> The subgroup `𝔇_Q(φ(Γ))` is normal in `Q`, and the normal closure of `φ(S)` is
> `φ(N) = Q`, so `𝔇_Q(φ(Γ)) = Q`.

Both clauses: normality, which is by construction since the defect is a normal
closure, and the conclusion, which is normality plus the containment of the
previous sentence plus `φ(N) = Q`. -/
theorem manuscriptSentence_theoremDefectEqTop {E : Type} [Group E]
    (F : PrintedFournierFacioData E) {Q : Type} [Group Q] (phi : E →* Q)
    (htop : (Subgroup.normalClosure (F.conjFactor : Set E)).map phi = ⊤) :
    (OneSidedMFRadical.printedDefect (F.core.map phi)).Normal ∧
      OneSidedMFRadical.printedDefect (F.core.map phi) = ⊤ := by
  refine ⟨inferInstance, ?_⟩
  have hS := map_conjFactor_le_printedDefect_of_functorial F phi
  have hNle : Subgroup.normalClosure (F.conjFactor : Set E) ≤
      (OneSidedMFRadical.printedDefect (F.core.map phi)).comap phi := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    exact hS (Subgroup.mem_map_of_mem phi hy)
  refine top_unique ?_
  rw [← htop]
  exact Subgroup.map_le_iff_le_comap.mpr hNle

/-- **`thm:torsion-free`, printed sentence.**

> Both `Q` and `φ(Γ)` have property (T), as quotients of `G₀` and `Γ`,
> respectively. -/
theorem manuscriptSentence_theoremBothKazhdan {G₀ : Type} [Group G₀]
    (F : PrintedFournierFacioData G₀)
    (hΓT : HasKazhdanPropertyT.{0, 0} ↥F.core)
    (hG₀T : HasKazhdanPropertyT.{0, 0} G₀) {Q : Type} [Group Q] (phi : G₀ →* Q)
    (hphi : Function.Surjective phi) :
    HasKazhdanPropertyT.{0, 0} Q ∧
      HasKazhdanPropertyT.{0, 0} ↥(F.core.map phi) := by
  refine ⟨HasKazhdanPropertyT.of_surjective phi hphi hG₀T, ?_⟩
  have hrange : (phi.comp F.core.subtype).range = F.core.map phi := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact HasKazhdanPropertyT.of_surjective
    (phi.comp F.core.subtype).rangeRestrict
    (phi.comp F.core.subtype).rangeRestrict_surjective hΓT

/-- **`thm:torsion-free`, printed sentence.**

> By the last assertion of Theorem `thm:compression-criterion`, every
> homomorphism from `Q` to an MF group is trivial.

The last assertion is the saturated case `𝔇_Q(L) = Q`, which gives the full MF
radical; the sentence's own words then follow from
`manuscriptFullRadicalKillsMFTargets`. -/
theorem manuscriptSentence_theoremHomsTrivial {Q : Type} [Group Q] [Countable Q]
    (L : Subgroup Q) (hLT : HasKazhdanPropertyT.{0, 0} ↥L)
    (hQT : HasKazhdanPropertyT.{0, 0} Q)
    (hD : OneSidedMFRadical.printedDefect L = ⊤) :
    manuscriptCoronaMFResidual Q = ⊤ ∧
      ∀ (M : Type) (_ : Group M), IsOperatorMF M →
        ∀ (f : Q →* M) (x : Q), f x = 1 := by
  obtain ⟨-, -, hsat⟩ :=
    OneSidedMFRadical.manuscriptOneSidedCompressionCriterion Q L hLT
  have htop := hsat hQT hD
  refine ⟨htop, ?_⟩
  intro M instM hM f x
  letI := instM
  exact OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets Q M htop hM f x

/-- **`thm:torsion-free`, printed sentence.**

> If a quotient `Q̄` of `Q` is MF, then the quotient map `Q → Q̄` is trivial, so
> `Q̄ = 1`. -/
theorem manuscriptSentence_theoremQuotientTrivial {Q : Type} [Group Q]
    (hkill : ∀ (M : Type) (_ : Group M), IsOperatorMF M →
      ∀ (f : Q →* M) (x : Q), f x = 1)
    (L : Type) (instL : Group L) (r : Q →* L) (hr : Function.Surjective r)
    (hMF : IsOperatorMF L) : ∀ y : L, y = 1 := by
  letI := instL
  intro y
  obtain ⟨x, rfl⟩ := hr y
  exact hkill L instL hMF r x

/-! ## `cor:relative-quotient`, printed proof -/

/-- **`cor:relative-quotient`, printed sentence, its "since" clause.**

> … since a torsion-free acylindrically hyperbolic group has no nontrivial
> finite normal subgroup.

Torsion-freeness alone does it, and normality is not used: a finite *subgroup*
of a torsion-free group is already trivial.  This discharges the `K(Gᵢ) = 1`
hypothesis of Hull's Corollary 7.4. -/
theorem manuscriptSentence_relativeQuotientTrivialFiniteRadical {G : Type}
    [Group G] (hG : IsPowerTorsionFree G) : HasTrivialFiniteRadical G :=
  hasTrivialFiniteRadical_of_torsionFree hG

/-- **`cor:relative-quotient`, printed sentence.**

> Hull's common quotient theorem [Hull, Corollary 7.4], applied to `G` and to
> the group `Q` of Theorem `thm:torsion-free`, gives a common quotient `P` that
> is acylindrically hyperbolic, with the map from `G` injective on a prescribed
> finite subset …

The citation, applied at the two groups the printed proof applies it to.  The
`K(Gᵢ) = 1` hypotheses are supplied by the previous sentence, so they do not
appear as arguments. -/
theorem manuscriptSentence_relativeQuotientCommonQuotient
    (hCQ : HullCommonQuotientPrinted) (G Q : Type) [Group G] [Group Q]
    [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented Q]
    [IsAcylindricallyHyperbolic G] [IsAcylindricallyHyperbolic Q]
    (hG : IsPowerTorsionFree G) (hQ : IsPowerTorsionFree Q)
    {Ω : Set G} (hΩ : Ω.Finite) :
    ∃ (P : Type) (_ : Group P) (a₁ : G →* P) (a₂ : Q →* P),
      Function.Surjective a₁ ∧ Function.Surjective a₂ ∧
        Group.IsFinitelyPresented P ∧ IsPowerTorsionFree P ∧
          IsAcylindricallyHyperbolic P ∧ Set.InjOn a₁ Ω :=
  hCQ G Q hG hQ (manuscriptSentence_relativeQuotientTrivialFiniteRadical hG)
    (manuscriptSentence_relativeQuotientTrivialFiniteRadical hQ) hΩ

/-- **`cor:relative-quotient`, printed sentence.**

> For finitely generated inputs, the proof of that corollary consists of two
> applications of Theorem `thm:hull` to the free product `G*Q`, so `P` is
> torsion-free and finitely presented, as in the remark after Theorem
> `thm:hull`.

The sentence's content is the *remark*, applied to the quotient those two
applications produce: torsion-freeness from the finite-order lift, finite
presentation from the finitely generated kernel.  Stated over that data rather
than over the free product, because this development has neither acylindrical
hyperbolicity of a free product nor suitability of its factors — which is why
`HullCommonQuotientPrinted` carries the two conclusions rather than deriving
them. -/
theorem manuscriptSentence_relativeQuotientTorsionFreeFinitelyPresented
    {G P : Type} [Group G] [Group.IsFinitelyPresented G] [Group P]
    (hG : IsPowerTorsionFree G) (a₁ : G →* P) (ha₁ : Function.Surjective a₁)
    (hlift : ∀ y : P, IsOfFinOrder y → ∃ x : G, a₁ x = y ∧ orderOf x = orderOf y)
    {S : Finset G} (hker : a₁.ker = Subgroup.normalClosure (S : Set G)) :
    IsPowerTorsionFree P ∧ Group.IsFinitelyPresented P :=
  ⟨manuscriptSentence_saturationQuotientTorsionFree hG a₁ hlift,
    manuscriptSentence_saturationQuotientFinitelyPresented a₁ ha₁ hker⟩

/-- **`cor:relative-quotient`, printed sentence.**

> As a quotient of `Q`, the group `P` is two-generated and has property (T) …

Both clauses, from surjectivity alone: the images of two generators generate,
and property (T) passes to quotients. -/
theorem manuscriptSentence_relativeQuotientTwoGeneratedKazhdan {Q P : Type}
    [Group Q] [Group P] (hgen : IsTwoGenerated Q)
    (hQT : HasKazhdanPropertyT.{0, 0} Q) (a₂ : Q →* P)
    (ha₂ : Function.Surjective a₂) :
    IsTwoGenerated P ∧ HasKazhdanPropertyT.{0, 0} P := by
  obtain ⟨x, y, hxy⟩ := hgen
  refine ⟨⟨a₂ x, a₂ y, ?_⟩, HasKazhdanPropertyT.of_surjective a₂ ha₂ hQT⟩
  rw [← closure_pair_map a₂ x y, hxy]
  exact Subgroup.map_top_of_surjective a₂ ha₂

/-- **`cor:relative-quotient`, printed sentence.**

> … and every homomorphism from `P` to an MF group pulls back to one from `Q`,
> so it is trivial.

The pullback is the composite with the surjection `Q ↠ P`, and triviality is
the full MF radical of `P` inherited from that of every quotient of `Q`. -/
theorem manuscriptSentence_relativeQuotientHomsTrivial {P : Type} [Group P]
    [Countable P] (hPtop : manuscriptCoronaMFResidual P = ⊤) :
    ∀ (M : Type) (_ : Group M), IsOperatorMF M →
      ∀ (f : P →* M) (x : P), f x = 1 := by
  intro M instM hM f x
  letI := instM
  exact OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets P M hPtop hM f x

/-! ## `cor:regular-nonmf-algebra`, printed proof -/

/-- **`cor:regular-nonmf-algebra`, printed sentence.**

> The group `Q` is countable, torsion-free, and acylindrically hyperbolic, so it
> contains a non-degenerate hyperbolically embedded subgroup [Osin, Theorem 1.2]
> and has no nontrivial finite normal subgroup.

**Only the last clause is carried.**  This development has no vocabulary for
*hyperbolically embedded*, and the printed proof uses that clause only to reach
the hypothesis of Dahmani--Guirardel--Osin, which `DGOTheorem235Printed` states
at the hypotheses named in this sentence.  So Osin's Theorem 1.2 is folded into
that citation rather than carried on its own; nothing else in the corollary uses
it. -/
theorem manuscriptSentence_algebraTrivialFiniteRadical {Q : Type} [Group Q]
    (hQ : IsPowerTorsionFree Q) : HasTrivialFiniteRadical Q :=
  hasTrivialFiniteRadical_of_torsionFree hQ

/-- **`cor:regular-nonmf-algebra`, printed sentence.**

> Dahmani, Guirardel, and Osin give simplicity and uniqueness of the trace
> [DGO, Theorem 2.35], and Gerasimova and Osin give density of the invertible
> elements, which is stable rank one [GO, Theorem 1.1].

The two citations, applied at the hypotheses the previous sentence supplies.
"which is stable rank one" is the definition `IsStableRankOne`, so the second
citation's conclusion and the corollary's adjective are the same statement. -/
theorem manuscriptSentence_algebraSimpleUniqueTraceStableRank
    (hDGO : DGOTheorem235Printed) (hGO : GerasimovaOsinTheorem11Printed)
    (Q : Type) [Group Q] [Countable Q] [IsAcylindricallyHyperbolic Q]
    (hQ : IsPowerTorsionFree Q) :
    IsSimpleCStar (ReducedGroupCStar Q) ∧
      HasUniqueTracialState (ReducedGroupCStar Q) ∧
        IsStableRankOne (ReducedGroupCStar Q) :=
  ⟨(hDGO Q (manuscriptSentence_algebraTrivialFiniteRadical hQ)).1,
    (hDGO Q (manuscriptSentence_algebraTrivialFiniteRadical hQ)).2,
    hGO Q (manuscriptSentence_algebraTrivialFiniteRadical hQ)⟩

/-- **`cor:regular-nonmf-algebra`, printed sentence, first clause.**

> The algebra is separable and generated by the canonical unitaries of the two
> generators …

Separability from countability of the group; the two canonical unitaries are the
left translations by the two generators, and the closed star-subalgebra they
generate is `C*_r(Q)` — an algebraic fact, since the elements whose left
translation lies in a star-subalgebra form a subgroup. -/
theorem manuscriptSentence_algebraSeparableGenerated (Q : Type) [Group Q]
    [Countable Q] {g₁ g₂ : Q}
    (hgen : Subgroup.closure ({g₁, g₂} : Set Q) = ⊤) :
    TopologicalSpace.SeparableSpace (ReducedGroupCStar Q) ∧
      leftRegularOperator Q g₁ ∈
          unitary (GroupHilbert Q →L[ℂ] GroupHilbert Q) ∧
        leftRegularOperator Q g₂ ∈
            unitary (GroupHilbert Q →L[ℂ] GroupHilbert Q) ∧
          (StarAlgebra.adjoin ℂ
            ({leftRegularOperator Q g₁, leftRegularOperator Q g₂} :
              Set (GroupHilbert Q →L[ℂ] GroupHilbert Q))).topologicalClosure
            = reducedGroupCStarSubalgebra Q :=
  ⟨(reducedGroupCStar_separable_stablyFinite Q).1,
    unitary_leftRegularOperator Q g₁, unitary_leftRegularOperator Q g₂,
    topologicalClosure_adjoin_pair hgen⟩

/-- **`cor:regular-nonmf-algebra`, printed sentence, second clause.**

> … its canonical trace is faithful, so it is stably finite … -/
theorem manuscriptSentence_algebraStablyFinite (Q : Type) [Group Q]
    [Countable Q] : IsStablyFiniteCStarAlgebra (ReducedGroupCStar Q) :=
  (reducedGroupCStar_separable_stablyFinite Q).2

/-- **`cor:regular-nonmf-algebra`, printed sentence, third clause.**

> … and an embedding into a norm matrix corona would embed `Q` into the corona's
> unitary group, against Theorem `thm:torsion-free`.

The group input is exactly the failure of MF-ness for `Q`, which
`thm:torsion-free` supplies through the full MF radical together with
nontriviality. -/
theorem manuscriptSentence_algebraNotMF (Q : Type) [Group Q] [Countable Q]
    (h : ¬ IsCDEOperatorMF Q) : ¬ IsMFAlgebra (ReducedGroupCStar Q) :=
  not_isMFAlgebra_reducedGroupCStar Q h

/-- **`cor:regular-nonmf-algebra`, the group input of its last clause.**

> … against Theorem `thm:torsion-free`.

A nontrivial group whose MF radical is everything is not MF: the identity is a
homomorphism to an MF group and would have to be trivial. -/
theorem manuscriptSentence_algebraNotCDEOperatorMF {Q : Type} [Group Q]
    [Countable Q] [Nontrivial Q] (htop : manuscriptCoronaMFResidual Q = ⊤) :
    ¬ IsCDEOperatorMF Q := by
  intro hMF
  have hbot : manuscriptCoronaMFResidual Q = ⊥ :=
    isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot.mp hMF
  obtain ⟨x, hx⟩ := exists_ne (1 : Q)
  apply hx
  have hmem : x ∈ manuscriptCoronaMFResidual Q := by
    rw [htop]
    exact Subgroup.mem_top x
  rw [hbot] at hmem
  simpa using hmem

end TorsionFreePrintedSentences
end NonMF
end Manuscript
end GroupApproximation
