import GroupApproximation.GGT.RelHypDefinition

/-!
# Osin's Theorem 2.4, at the statement Osin states

D. Osin, *Small cancellations over relatively hyperbolic groups and embedding
theorems*, Ann. of Math. **172** (2010) 1--39 (arXiv:math/0411039).

Four generations of `GGT/RelHypOsinTheorem24*.lean` transcribed the §4
small-cancellation *machinery* -- Definitions 4.1 and 4.2, the condition
`C(ε, µ, λ, c, ρ)` -- as if it were Theorem 2.4, and every one of them was
refuted; issue #52 records the four clause diffs of the last.  Theorem 2.4
carries no small-cancellation hypothesis at all.  This module states it.

> **Theorem 2.4.**  Let `G` be a group hyperbolic relative to a collection of
> subgroups `{H_λ}_{λ∈Λ}`, `H` a suitable subgroup of `G`, and `t₁,…,t_m`
> arbitrary elements of `G`.  Then there exists an epimorphism `η : G → Ḡ` such
> that:
> 1. `Ḡ` is hyperbolic relative to `{η(H_λ)}_{λ∈Λ}`.
> 2. For any `i`, `η(tᵢ) ∈ η(H)`.
> 3. The restriction of `η` to `⋃_λ H_λ` is injective.
> 4. `η(H)` is a suitable subgroup of `Ḡ`.
> 5. Every element of finite order in `Ḡ` is an image of an element of finite
>    order in `G`.

All five clauses are transcribed, including the two the manuscript does not
consume: faithfulness is the point of this module, and a later prover owes
clause 4 in any case, since Osin's own induction runs on it.

## What this does and does not replace

It does **not** replace `GGT/RelHypFournierFacioProp23.lean`.  Theorem 2.4's
conclusion has **no finite-presentation clause**, and
`FournierFacioQuotientStatement` requires one.  That clause reaches the
manuscript through Fournier-Facio's parenthetical "(finitely presented)", which
[FF25] justifies by reading Osin's *proof*: "the proof of [Osi10, Theorem 2.4]
produces the quotient by adding `k` small cancellation relations, one for each
element `gᵢ`, in particular the construction preserves finite presentability."

So the architecture is a refinement, not a substitution:

    FournierFacioProposition23
      ⟸ OsinTheorem24Statement                       (a published statement)
      + OsinTheorem24FinitePresentationAddendum      (a published *proof*)
      + suitability of `H₀` in `U ∗ H₀`              (owed in-repo)

The addendum below is the second line, and isolating it is the point: it turns
an invisible parenthetical into an object an auditor can see.  It is stated as
"the kernel of `η` is the normal closure of a finite set", which is what the
quoted sentence actually asserts, rather than as "`Ḡ` is finitely presented",
which is a consequence -- `Group.IsFinitelyPresented.of_surjective` derives the
latter from the former and finite presentation of `G`.

## Two transcription decisions, recorded

**`osinElementaryClosure` is a `Set`, not a `Subgroup`.**  Osin's Theorem 2.1
asserts that `E_G(g)` *is* a subgroup, and only for `g` hyperbolic of infinite
order.  Declaring it a `Subgroup` here would oblige a closure proof that is
false in general and is itself a citation; Definition 2.2 needs only the set.
`one_mem_osinElementaryClosure` below records that `1` lies in every one of
them, so the last clause of `IsSuitableSubgroup` -- read as an implication --
says exactly `E(f₁) ∩ E(f₂) = {1}` and not `= ∅`, which would be unsatisfiable.

**The exponent is positive.**  Osin writes `E_G(g) = {f : f⁻¹ gⁿ f = g^{±n}` for
some `n ∈ ℕ}`.  Taken with `n = 0` allowed, `g⁰ = 1` and every `f` qualifies, so
`E_G(g)` would be all of `G`, `IsSuitableSubgroup` would be unsatisfiable in any
nontrivial group, and `OsinTheorem24Statement` would be **vacuously true**.
`0 < n` is therefore not a decoration; it is what keeps the hypothesis
inhabited.

This module deliberately does **not** reuse `GGT/ElementaryClosure.
elementaryClosure`.  That is `{h | ∃ n m : ℤ, n ≠ 0 ∧ m ≠ 0 ∧ h gⁿ h⁻¹ = gᵐ}` --
the commensurator of `⟨g⟩`, strictly larger than Osin's `±n` condition, and a
different definition.  It stays where it is, for the acylindrical lane; a bridge
can be proved if a consumer ever needs one.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

/-! ## 1.  Osin's §2 vocabulary -/

section Vocabulary

variable {G : Type*} [Group G] {ι : Type*}

/-- **A parabolic element** (Osin, §2): one conjugate into some peripheral
subgroup. -/
def IsParabolicElement (Hfam : ι → Subgroup G) (g : G) : Prop :=
  ∃ (l : ι) (c : G), c⁻¹ * g * c ∈ Hfam l

/-- **A hyperbolic element** (Osin, §2): one that is not parabolic.  With an
empty peripheral family every element is hyperbolic, which is the ordinary
hyperbolic-group specialisation of the theory. -/
def IsHyperbolicElement (Hfam : ι → Subgroup G) (g : G) : Prop :=
  ¬ IsParabolicElement Hfam g

/-- **Commensurability in `G`** (Osin, §2): `f^k` is conjugate to `g^l` for some
nonzero `k, l`.  Named against Mathlib's `Commensurable`, which is a relation
between subgroups. -/
def OsinCommensurable (f g : G) : Prop :=
  ∃ (k l : ℤ) (c : G), k ≠ 0 ∧ l ≠ 0 ∧ c⁻¹ * f ^ k * c = g ^ l

/-- **The maximal elementary subgroup `E_G(g)`** (Osin, Theorem 2.1), as a
**set**: the elements conjugating some positive power of `g` to that power or
its inverse.  See the header for why this is a `Set` and why `0 < n` is
load-bearing. -/
def osinElementaryClosure (g : G) : Set G :=
  {f | ∃ n : ℕ, 0 < n ∧ (f⁻¹ * g ^ n * f = g ^ n ∨ f⁻¹ * g ^ n * f = (g ^ n)⁻¹)}

/-- **A suitable subgroup** (Osin, Definition 2.2): one containing two
non-commensurable hyperbolic elements of infinite order whose maximal elementary
subgroups meet trivially. -/
def IsSuitableSubgroup (Hfam : ι → Subgroup G) (H : Subgroup G) : Prop :=
  ∃ f₁ ∈ H, ∃ f₂ ∈ H,
    IsHyperbolicElement Hfam f₁ ∧ IsHyperbolicElement Hfam f₂ ∧
      (∀ n : ℕ, 0 < n → f₁ ^ n ≠ 1) ∧ (∀ n : ℕ, 0 < n → f₂ ^ n ≠ 1) ∧
        ¬ OsinCommensurable f₁ f₂ ∧
          ∀ f, f ∈ osinElementaryClosure f₁ → f ∈ osinElementaryClosure f₂ →
            f = 1

end Vocabulary

/-! ## 2.  The model tests

The checks the standing rule asks for before a `Prop` built on this vocabulary
goes into hypothesis position: that `E_G(g)` is inhabited in the way Definition
2.2 reads it, that suitability is not satisfied by objects that plainly should
not satisfy it, and that the peripheral dichotomy degenerates the right way.

The tests below are all negative; the positive one lives elsewhere, and the
reason is a dependency direction rather than a gap.  `IsSuitableSubgroup` is a
predicate on a peripheral family and a subgroup, and carries no
relative-hyperbolicity hypothesis --- that is a separate binder of
`OsinTheorem24Statement`.  So it is satisfiable far below the manuscript's
configuration: with `ι = Empty` every element is hyperbolic in Osin's sense by
`isHyperbolicElement_of_isEmpty` below, and the free group of rank two, read as
`ℤ ∗ ℤ`, satisfies the rest.
`GGT/RelHypSuitabilityResidue.isSuitableSubgroup_intPair` proves exactly that,
and `isSuitableSubgroup_freeProduct_intPair` upgrades it to a *nonempty*
peripheral family --- suitability of the partner factor in `U ∗ (ℤ ∗ ℤ)` for an
arbitrary `U`.  That module imports this one, so the witness cannot be repeated
here without a cycle; it is cited rather than duplicated.

What has no witness in this repository is not the predicate but the
**configuration** the manuscript needs: suitability at `U ∗ H₀` with `H₀`
torsion-free hyperbolic with property `(T)`.  That routes through
`Manuscript.NonMF.TheoremC.KotowskiOllivierStatement` --- Kotowski--Kotowski and
Ollivier--Wise, the density model at a parameter between `1/3` and `1/2` ---
which is itself a recorded debt, and through
`GGT/RelHypSuitabilityResidue.HyperbolicSuitabilityStatement`, the residue that
survives the free-product reduction.  The negative tests below pin the
definition from the side that matters, since the failure mode these definitions
could have had is being satisfied by objects Osin's theorem says nothing
about. -/

section ModelTests

variable {G : Type*} [Group G] {ι : Type*}

/-- `1 ∈ E_G(g)`, so the last clause of `IsSuitableSubgroup` says the
intersection is `{1}` rather than `∅`. -/
theorem one_mem_osinElementaryClosure (g : G) :
    (1 : G) ∈ osinElementaryClosure g := by
  refine ⟨1, one_pos, Or.inl ?_⟩
  simp

/-- `g ∈ E_G(g)`, the other element Definition 2.2 is really about. -/
theorem self_mem_osinElementaryClosure (g : G) :
    g ∈ osinElementaryClosure g := by
  refine ⟨1, one_pos, Or.inl ?_⟩
  simp

/-- **The trivial subgroup is never suitable.**  The sharp check: were it
suitable, `OsinTheorem24Statement` would assert a quotient sending an arbitrary
finite set into `η(⊥) = 1` while staying injective on the peripherals.  The
infinite-order clause is what rules it out. -/
theorem not_isSuitableSubgroup_bot (Hfam : ι → Subgroup G) :
    ¬ IsSuitableSubgroup Hfam (⊥ : Subgroup G) := by
  rintro ⟨f₁, hf₁, f₂, -, -, -, hord₁, -, -, -⟩
  rw [Subgroup.mem_bot] at hf₁
  subst hf₁
  exact hord₁ 1 one_pos (one_pow 1)

/-- **A subgroup whose elements are pairwise commensurable is not suitable.**  So
no elementary subgroup is, which is the content Osin's Definition 2.2 is
carrying. -/
theorem not_isSuitableSubgroup_of_commensurable (Hfam : ι → Subgroup G)
    {H : Subgroup G} (h : ∀ f ∈ H, ∀ g ∈ H, OsinCommensurable f g) :
    ¬ IsSuitableSubgroup Hfam H := by
  rintro ⟨f₁, hf₁, f₂, hf₂, -, -, -, -, hnc, -⟩
  exact hnc (h f₁ hf₁ f₂ hf₂)

/-- **No abelian group has a suitable subgroup.**

The sharpest of the cheap tests, and the one that checks the definition is doing
the work Osin needs it to do: suitability is what excludes the elementary case,
and in an abelian group `E(g)` is everything, so the trivial-intersection clause
collapses the witness to `1` and contradicts its infinite order.  A definition
that had let an abelian group through would have been too weak, in exactly the
way `OsinRelatorDesign`'s missing non-elementarity was. -/
theorem not_isSuitableSubgroup_of_comm (hG : ∀ x y : G, x * y = y * x)
    (Hfam : ι → Subgroup G) (H : Subgroup G) :
    ¬ IsSuitableSubgroup Hfam H := by
  rintro ⟨f₁, -, f₂, -, -, -, hord₁, -, -, htriv⟩
  have hmem₂ : f₁ ∈ osinElementaryClosure f₂ := by
    refine ⟨1, one_pos, Or.inl ?_⟩
    rw [pow_one, mul_assoc, hG f₂ f₁, inv_mul_cancel_left]
  have h1 : f₁ = 1 := htriv f₁ (self_mem_osinElementaryClosure f₁) hmem₂
  exact hord₁ 1 one_pos (by rw [h1, one_pow])

/-- **With no peripheral subgroups every element is hyperbolic.**  The theorem's
`ι = Empty` specialisation is therefore about ordinary hyperbolic groups, and is
not vacuous. -/
theorem isHyperbolicElement_of_isEmpty [IsEmpty ι] (Hfam : ι → Subgroup G)
    (g : G) : IsHyperbolicElement Hfam g := by
  intro h
  obtain ⟨l, -, -⟩ := h
  exact IsEmpty.false l

/-- **Suitability passes to larger subgroups**, since its witnesses do. -/
theorem IsSuitableSubgroup.mono {Hfam : ι → Subgroup G} {H K : Subgroup G}
    (hHK : H ≤ K) (h : IsSuitableSubgroup Hfam H) : IsSuitableSubgroup Hfam K := by
  obtain ⟨f₁, hf₁, f₂, hf₂, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨f₁, hHK hf₁, f₂, hHK hf₂, h1, h2, h3, h4, h5, h6⟩

end ModelTests

/-! ## 3.  The theorem -/

section Statement

variable {G : Type} [Group G] {ι : Type}

/-- **The conclusion of Theorem 2.4**, as a predicate on the quotient, so that
the statement and its finite-presentation addendum do not have to repeat it.

The five clauses are Osin's, in his order, with surjectivity of `η` -- "an
epimorphism" -- first.  Clause 3 is injectivity on the **union** of the
peripheral subgroups, which is what he writes and is stronger than injectivity
on each: it also forbids two peripherals from being identified with each
other. -/
def IsOsin24Quotient (Hfam : ι → Subgroup G) (H : Subgroup G) (t : Set G)
    (Q : Type) [Group Q] (eta : G →* Q) : Prop :=
  Function.Surjective eta ∧
    IsRelativelyHyperbolic Q (fun l => (Hfam l).map eta) ∧
      (∀ x ∈ t, eta x ∈ H.map eta) ∧
        Set.InjOn eta (⋃ l, (Hfam l : Set G)) ∧
          IsSuitableSubgroup (fun l => (Hfam l).map eta) (H.map eta) ∧
            ∀ q : Q, (∃ n : ℕ, 0 < n ∧ q ^ n = 1) →
              ∃ g : G, (∃ m : ℕ, 0 < m ∧ g ^ m = 1) ∧ eta g = q

end Statement

/-- **Osin, Ann. of Math. 172 (2010), Theorem 2.4**, verbatim.

The finitely many elements `t₁,…,t_m` are a finite subset of `G`.  Nothing is
assumed of `G` beyond relative hyperbolicity -- in particular no finite
generation, since the relative generating set carried by
`IsRelativelyHyperbolic` is finite while the peripheral subgroups need not
be. -/
def OsinTheorem24Statement : Prop :=
  ∀ (G : Type) (_ : Group G) (ι : Type) (Hfam : ι → Subgroup G),
    IsRelativelyHyperbolic G Hfam →
      ∀ H : Subgroup G, IsSuitableSubgroup Hfam H →
        ∀ t : Set G, t.Finite →
          ∃ (Q : Type) (_ : Group Q) (eta : G →* Q),
            IsOsin24Quotient Hfam H t Q eta

/-- **The finite-presentation addendum**, which is read off Osin's *proof* and
not off any published statement.

[FF25, Proposition 2.3]'s proof paragraph: "The proof of [Osi10, Theorem 2.4]
produces the quotient by adding `k` small cancellation relations, one for each
element `gᵢ`, in particular the construction preserves finite presentability."
The assertion is about the kernel, so that is what is stated: `η` may be chosen
with `ker η` the normal closure of a finite set.  Finite presentation of `Ḡ` is
then a consequence rather than a second citation, through
`Group.IsFinitelyPresented.of_surjective`.

This is a **strictly stronger** hypothesis than `OsinTheorem24Statement`
(`osinTheorem24Statement_of_finitePresentationAddendum` drops the clause), and
it is the only part of the Fournier-Facio quotient sentence that no published
statement supports.  Keeping it separate is the point of the split. -/
def OsinTheorem24FinitePresentationAddendum : Prop :=
  ∀ (G : Type) (_ : Group G) (ι : Type) (Hfam : ι → Subgroup G),
    IsRelativelyHyperbolic G Hfam →
      ∀ H : Subgroup G, IsSuitableSubgroup Hfam H →
        ∀ t : Set G, t.Finite →
          ∃ (Q : Type) (_ : Group Q) (eta : G →* Q),
            IsOsin24Quotient Hfam H t Q eta ∧
              (MonoidHom.ker eta).IsFinitelyNormallyGenerated

/-- The addendum implies the theorem: it is the same statement with one further
conclusion clause. -/
theorem osinTheorem24Statement_of_finitePresentationAddendum
    (h : OsinTheorem24FinitePresentationAddendum) : OsinTheorem24Statement := by
  intro G instG ι Hfam hrh H hsuit t htfin
  obtain ⟨Q, instQ, eta, hq, -⟩ := h G instG ι Hfam hrh H hsuit t htfin
  exact ⟨Q, instQ, eta, hq⟩

end RelHyp
end GGT
end GroupApproximation
