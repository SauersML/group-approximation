import GroupApproximation.Sofic.KazhdanCliffordConstruction
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The small-cancellation realization of the Kazhdan--Clifford datum

> **NO MANUSCRIPT CLAIM, AND NO LITERATURE INPUT IS TO BE ADDED HERE.**  (An
> earlier version of this header also said "not in the build"; the module is
> now root-imported, which is fine — everything in it is unconditional.  What
> must not change is the second half: no hypothesis naming a theorem *about*
> Fournier-Facio's group may be introduced.)  On
> 2026-08-16 every Fournier-Facio mention in `non_mf_groups_exist.tex` was
> audited and found to carry **no formal debt**.  There are five, not the
> three a first pass finds: a prior-work citation in the introduction, the
> `remark` this module is about, a personal-communication credit placed
> after the proof of `thm:saturation`, and two in `\subsection*{Questions}`.
> None occurs inside a `theorem`, `mainthm`, `proposition`, `lemma`,
> `corollary` or `proof` environment — four are body text and one is a
> `remark` — as determined by bracket-matching those environments over the
> whole file, not by reading context. The former conditional endpoint wrappers
> have since been retired. The explicit construction boundary now lives in
> `Sofic/FournierFacioHullBridge`: it takes
> proof-carrying two-stage data and is not exported as a closed manuscript
> theorem. Nothing the manuscript proves depends on a Fournier-Facio input, so
> nothing is owed here.
>
> This module records the remark's own deduction in unconditional form.
> Nothing below is conditional.  Everything from here down describes the
> remark and what is proved about it.
>
> (An earlier version of this header asserted that the companion module
> `Monsters/RealizationEmbedding` "was deleted the same day".  That is not
> true: the file is present and tracked, and it is the right treatment of the
> universality clause — see below.  The standing instruction is to read and
> reuse it, never to author a replacement and never to delete it.)

Manuscript: `non_mf_groups_exist.tex`, Remark `rem:ff-realization`
("a small-cancellation realization").
The remark sits immediately after the proof of
Theorem `thm:kazhdan-clifford`; locate it by the label rather than by line
number, which drifts as the surrounding sections are edited.

## What the remark says

It reports a suggestion of Fournier-Facio: the affine base of the explicit
construction can be replaced by the finitely presented torsion-free
property-`(T)` group `P` of the torsion-free nonsofic paper.  Since `P`
contains a copy of every finitely presented torsion-free group, it contains a
direct product `P₁ × P₂` with `Pᵢ ≅ P`; the remark then asserts that
`α : P ≅ P₁ ≤ P`, together with any `a ∈ P₂ \ {1}`, "satisfies the hypotheses
of Theorem `thm:kazhdan-clifford`", and closes by observing that `E(P, α, a)`
contains involutions whatever the base, so the affine base is still what
Theorems A, D and E are proved for.

**The remark is load-bearing for no numbered result.**  It states no theorem,
corollary, proposition or lemma; it carries no `\leanverified` badge; and the
only cross-reference to it anywhere in the manuscript is a `cf.` pointer from
the Questions preamble.  No numbered result uses the existence of
Fournier-Facio's group.

## What the remark deduces, and what is proved here

The remark makes exactly one mathematical deduction, and it is proved here
**unconditionally**:

> if a group `P` admits an injective homomorphism `f : P × P →* P`, then
> `α := f ∘ inl` is an injective endomorphism of `P`, and `f (1, b)` lies
> outside the image of `α` for every `b ≠ 1`.

No property of Fournier-Facio's group is assumed anywhere below; the only
input is the abstract self-embedding `f`, which is data, not a literature
theorem.  Composed with `kazhdanCliffordConstruction`, this gives the remark's
conclusion for every finitely presented property-`(T)` group carrying such an
`f`, including the remark's closing observation that the resulting group
contains an involution.  The single point at which the external literature
input would enter is the passage from universality of `P` to the existence of
`f`; that passage is deliberately absent from this file, and the module that
once carried it as a hypothesis has been deleted.

## Where the universality sentence is handled, and why not here

The remark's first sentence — *"His finitely presented torsion-free
property-`(T)` group `P` contains a copy of every finitely presented
torsion-free group, in particular a direct product `P₁ × P₂` with `Pᵢ ≅ P`"* —
is a theorem of the cited paper and is not proved anywhere in this
development.  It is handled in the companion module
`Monsters/RealizationEmbedding`, and handled correctly: universality appears
there as the explicit hypothesis `huniv` of the *single* implication
`rem_ff_realization_selfSquareEmbedding_of_universal`, whose proved content is
the closure step (`P × P` is again finitely presented and again torsion-free,
so a universal `P` receives an injection from its own square).  The same file
also exhibits, unconditionally, a group that embeds its own direct square, so
the algebraic hypothesis this module consumes is visibly not vacuous.

That is the right shape, and it should not be replaced by a structure tagged
as a literature input in the manner of
`Computability.MarkovMFConsequences.AdianRabinReduction`:

* the sentence is load-bearing for nothing.  It appears in a `remark`, the
  remark carries no `\leanverified` badge, and no numbered result in the
  manuscript cites it.  A tagged input exists to keep an *owed* citation
  visible; there is no debt here to keep visible.  The corpus's literature
  roster is empty in both places it lives (`scripts/Audit.lean`'s
  `literatureInputNames` and `notes/NON_MF_LITERATURE_INPUTS.txt`), and this
  would be the first entry ever;
* a structure would be a corpus-defined premise that nothing in the corpus
  ever discharges, which is exactly the shape
  `scripts/check_non_mf_unconditional.py` reports as a finding.  A plain
  `∀`-hypothesis in Mathlib vocabulary, which is what `huniv` is, carries the
  same information without inviting anyone to build on an undischarged
  package.

What the deduction below actually consumes is the self-embedding
`f : P × P →* P`, which is *data*.  Every theorem here quantifies over it, so
a reader who does supply Fournier-Facio's group together with its embedding
gets the remark's conclusion with nothing assumed on their behalf.
-/

namespace GroupApproximation.Monsters.FournierFacioRealization

universe w

/-! ## The datum extracted from a self-embedding of the direct square -/

section Algebra

variable {P : Type*} [Group P]

/-- The endomorphism `α : P ≅ P₁ ≤ P` of the remark: the self-embedding of
the direct square restricted to the first factor. -/
def selfEmbeddingEndomorphism (f : P × P →* P) : P →* P :=
  f.comp (MonoidHom.inl P P)

@[simp] theorem selfEmbeddingEndomorphism_apply (f : P × P →* P) (p : P) :
    selfEmbeddingEndomorphism f p = f (p, 1) := rfl

/-- The corresponding embedding of the second factor, `P ≅ P₂ ≤ P`. -/
def secondFactorEmbedding (f : P × P →* P) : P →* P :=
  f.comp (MonoidHom.inr P P)

@[simp] theorem secondFactorEmbedding_apply (f : P × P →* P) (p : P) :
    secondFactorEmbedding f p = f (1, p) := rfl

/-- The element `a ∈ P₂` of the remark, produced from `b ∈ P \ {1}`. -/
def secondFactorElement (f : P × P →* P) (b : P) : P := f (1, b)

@[simp] theorem secondFactorElement_eq (f : P × P →* P) (b : P) :
    secondFactorElement f b = f (1, b) := rfl

/-- **Remark `rem:ff-realization`, first hypothesis of
Theorem `thm:kazhdan-clifford`.**  `α` is an injective endomorphism. -/
theorem rem_ff_realization_alpha_injective (f : P × P →* P)
    (hf : Function.Injective f) :
    Function.Injective (selfEmbeddingEndomorphism f) := by
  intro x y hxy
  have hxy' : f (x, 1) = f (y, 1) := hxy
  have hpair : ((x, 1) : P × P) = (y, 1) := hf hxy'
  have hfst := congrArg Prod.fst hpair
  exact hfst

/-- The second-factor embedding is injective as well, so that `P₂ ≅ P`. -/
theorem rem_ff_realization_beta_injective (f : P × P →* P)
    (hf : Function.Injective f) :
    Function.Injective (secondFactorEmbedding f) := by
  intro x y hxy
  have hxy' : f (1, x) = f (1, y) := hxy
  have hpair : ((1, x) : P × P) = (1, y) := hf hxy'
  have hsnd := congrArg Prod.snd hpair
  exact hsnd

/-- **Remark `rem:ff-realization`, second hypothesis of
Theorem `thm:kazhdan-clifford`.**  Every nonidentity element of the second
factor lies outside `α(P) = P₁`.  This is the step that makes `a ∉ α(P)`
automatic: the two factors of an embedded direct square meet trivially. -/
theorem rem_ff_realization_a_notMem_range (f : P × P →* P)
    (hf : Function.Injective f) {b : P} (hb : b ≠ 1) :
    secondFactorElement f b ∉ Set.range (selfEmbeddingEndomorphism f) := by
  rintro ⟨p, hp⟩
  have hp' : f (p, 1) = f (1, b) := hp
  have hpair : ((p, 1) : P × P) = (1, b) := hf hp'
  have hsnd := congrArg Prod.snd hpair
  have hb1 : b = 1 := hsnd.symm
  exact hb hb1

/-- `P₁ ≅ P`: the first factor of the embedded direct square is a copy of the
whole group, as the remark asserts. -/
noncomputable def rem_ff_realization_firstFactorEquiv (f : P × P →* P)
    (hf : Function.Injective f) : P ≃* (selfEmbeddingEndomorphism f).range :=
  MonoidHom.ofInjective (rem_ff_realization_alpha_injective f hf)

/-- `P₂ ≅ P`: the second factor is likewise a copy of the whole group. -/
noncomputable def rem_ff_realization_secondFactorEquiv (f : P × P →* P)
    (hf : Function.Injective f) : P ≃* (secondFactorEmbedding f).range :=
  MonoidHom.ofInjective (rem_ff_realization_beta_injective f hf)

/-- The two factors commute elementwise: the subgroup they generate really is
a direct product `P₁ × P₂`. -/
theorem rem_ff_realization_factors_commute (f : P × P →* P) (p q : P) :
    Commute (selfEmbeddingEndomorphism f p) (secondFactorEmbedding f q) := by
  have h : Commute ((p, 1) : P × P) (1, q) := by
    have hmul : ((p, 1) : P × P) * (1, q) = (1, q) * (p, 1) := by simp
    exact hmul
  simpa using h.map f

/-- The two factors meet trivially, completing the direct-product picture
`P₁ × P₂ ≤ P` of the remark. -/
theorem rem_ff_realization_factors_disjoint (f : P × P →* P)
    (hf : Function.Injective f) :
    (selfEmbeddingEndomorphism f).range ⊓ (secondFactorEmbedding f).range =
      ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hx₁
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hx₂
  have hp' : f (p, 1) = x := hp
  have hq' : f (1, q) = x := hq
  have hpair : ((p, 1) : P × P) = (1, q) := hf (hp'.trans hq'.symm)
  have hfst := congrArg Prod.fst hpair
  have hp1 : p = 1 := hfst
  rw [Subgroup.mem_bot, ← hp', hp1]
  exact map_one f

end Algebra

/-! ## The remark's deduction, run through Theorem `thm:kazhdan-clifford` -/

section Manuscript

open KazhdanCliffordConstruction

variable {P : Type} [Group P] [Group.IsFinitelyPresented P]

/-- **Remark `rem:ff-realization`, the deduction.**  A self-embedding of the
direct square of a finitely presented property-`(T)` group supplies exactly
the data that Theorem `thm:kazhdan-clifford` consumes, and the resulting
extension is not MF.

The hypotheses are the manuscript's own hypotheses on the base, quantified
over all such bases; no statement about any particular group is assumed. -/
theorem rem_ff_realization_not_isCDEOperatorMF
    (hT : HasKazhdanPropertyTComplex.{0, w} P) (f : P × P →* P)
    (hf : Function.Injective f) {b : P} (hb : b ≠ 1) :
    ¬ IsCDEOperatorMF
      (Extension (selfEmbeddingEndomorphism f) (secondFactorElement f b)) :=
  (kazhdanCliffordConstruction (selfEmbeddingEndomorphism f)
      (rem_ff_realization_alpha_injective f hf) (secondFactorElement f b) hT
      (rem_ff_realization_a_notMem_range f hf hb)).2.2.2.2.2.2

/-- **Remark `rem:ff-realization`, closing sentence: "The group `E(P, α, a)`
contains involutions whatever the base."**  The distinguished central mark is
already a nontrivial involution, so the extension has torsion no matter which
base the construction is run on -- which is why the small-cancellation base
buys no torsion-free example. -/
theorem rem_ff_realization_contains_involution
    (hT : HasKazhdanPropertyTComplex.{0, w} P) (f : P × P →* P)
    (hf : Function.Injective f) {b : P} (hb : b ≠ 1) :
    ∃ x : Extension (selfEmbeddingEndomorphism f) (secondFactorElement f b),
      x ≠ 1 ∧ x ^ 2 = 1 := by
  have h := kazhdanCliffordConstruction (selfEmbeddingEndomorphism f)
    (rem_ff_realization_alpha_injective f hf) (secondFactorElement f b) hT
    (rem_ff_realization_a_notMem_range f hf hb)
  exact ⟨mark (selfEmbeddingEndomorphism f) (secondFactorElement f b),
    h.2.2.1, h.2.2.2.1⟩

/-- The base embeds in the realized extension, as in the main construction. -/
theorem rem_ff_realization_base_injective
    (hT : HasKazhdanPropertyTComplex.{0, w} P) (f : P × P →* P)
    (hf : Function.Injective f) {b : P} (hb : b ≠ 1) :
    Function.Injective
      (iota (selfEmbeddingEndomorphism f) (secondFactorElement f b)) :=
  (kazhdanCliffordConstruction (selfEmbeddingEndomorphism f)
      (rem_ff_realization_alpha_injective f hf) (secondFactorElement f b) hT
      (rem_ff_realization_a_notMem_range f hf hb)).2.1

/-- **Remark `rem:ff-realization`, closing sentence, at the generality it is
printed in: "The group `E(P, α, a)` contains involutions *whatever the
base*."**

`rem_ff_realization_contains_involution` proves this for the bases the remark
constructs — the ones carrying a self-embedding of the direct square — which
is weaker than what the sentence says.  The sentence quantifies over every
base the Kazhdan--Clifford construction accepts, and that is what is stated
here: for *any* finitely presented group with an injective self-map and an
element outside its image, the distinguished mark of the extension is a
nontrivial central involution.

Property `(T)` is not needed and is not assumed: nontriviality of the mark is
the Clifford-model computation `mark_ne_one`, which uses only injectivity of
`α` and `a ∉ α(Γ₀)`.  That is the point of the sentence — the torsion is
structural, so replacing the affine base by a small-cancellation one cannot
buy a torsion-free example. -/
theorem rem_ff_realization_contains_involution_any_base
    {Γ₀ : Type} [Group Γ₀] [Group.IsFinitelyPresented Γ₀]
    (alpha : Γ₀ →* Γ₀) (hAlpha : Function.Injective alpha) (a : Γ₀)
    (ha : a ∉ Set.range alpha) :
    ∃ x : Extension alpha a, x ≠ 1 ∧ x ^ 2 = 1 ∧
      ∀ g : Extension alpha a, Commute x g :=
  ⟨mark alpha a, mark_ne_one alpha hAlpha a ha, mark_sq alpha a,
    mark_central alpha a⟩

/-- The realized extension is finitely presented. -/
theorem rem_ff_realization_finitelyPresented
    (hT : HasKazhdanPropertyTComplex.{0, w} P) (f : P × P →* P)
    (hf : Function.Injective f) {b : P} (hb : b ≠ 1) :
    Group.IsFinitelyPresented
      (Extension (selfEmbeddingEndomorphism f) (secondFactorElement f b)) :=
  (kazhdanCliffordConstruction (selfEmbeddingEndomorphism f)
      (rem_ff_realization_alpha_injective f hf) (secondFactorElement f b) hT
      (rem_ff_realization_a_notMem_range f hf hb)).1

end Manuscript

end GroupApproximation.Monsters.FournierFacioRealization
