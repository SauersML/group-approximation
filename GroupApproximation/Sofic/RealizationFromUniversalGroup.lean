import GroupApproximation.Sofic.KazhdanCliffordConstruction

/-!
# The realization reduction of `rem:ff-realization`

`non_mf_groups_exist.tex`, `\begin{remark}[a small-cancellation realization]`
(`\label{rem:ff-realization}`), reads:

> Fournier-Facio has pointed out (personal communication, 2026) that the affine
> base of Sections 3-4 can be replaced by a small-cancellation construction as
> in [FFF].  His finitely presented torsion-free property-(T) group `P` contains
> every finitely presented torsion-free group, in particular a direct product
> `P₁ × P₂` with `Pᵢ ≅ P`.  Choosing an isomorphism `α : P → P₁ ≤ P` and any
> `a ∈ P₂ ∖ {1}` gives the input required by Theorem `thm:kazhdan-clifford`.
> The group `E(P,α,a)` has torsion even though `P` does not, since the
> construction adjoins the involution `c`.

The remark has two separable halves, and proof-ledger rows `KC.21` and `KC.22`
mark both `MISSING`.

**`KC.21` is literature and stays literature.**  That some finitely presented
torsion-free property-(T) group contains every finitely presented torsion-free
group is Fournier-Facio's theorem, cited to [FFF] and a personal
communication.  Nothing in this file asserts it, and nothing here supplies a
hypothesis standing in for it.  `ContainsSquare P` below is a *datum carried as
an explicit argument by every statement in the file*: no theorem here claims
that any particular group admits one.  A reader looking for the existence
claim will not find it, because it is not proved anywhere in this development.

**`KC.22` is the reduction, and it is unconditional.**  The word "gives" in the
printed sentence hides a small argument, and that argument needs no property of
`P` at all: for an arbitrary group containing `P × P`, the composite
`P ≅ P₁ ≤ P` is an injective endomorphism, it is proper, and any nontrivial
element of the second factor lies outside its image.  The last of these is the
step the remark compresses hardest — `a ∉ P₁` is not immediate from `a ∈ P₂`,
it needs `P₁ ∩ P₂ = 1`, which is what the direct-product structure supplies.
`disjoint_factors` isolates exactly that, and `emb_inr_not_mem_range_alpha` is
the conclusion drawn from it.

The printed direct product `P₁ × P₂ ≤ P` with `Pᵢ ≅ P` is carried here as an
injective homomorphism `P × P →* P`, which is the same data: `P₁` and `P₂` are
its two factor images (`firstFactor`, `secondFactor`), each isomorphic to `P`
because each factor inclusion is injective, and `alphaEquivFirstFactor` is the
printed isomorphism `α : P → P₁`.

`realization` then instantiates `kazhdanCliffordConstruction` at that datum,
universally quantified over every finitely presented property-(T) group
containing a square of itself, and returns the printed conclusions: the
extension is finitely presented, carries a nontrivial central involution, and
is not MF.  Torsion-freeness of `P` is printed but is *not* a hypothesis of the
construction and is therefore not taken; the remark mentions it only to observe
that `E(P,α,a)` does not inherit it.
-/

namespace GroupApproximation
namespace RealizationFromUniversalGroup

open KazhdanCliffordConstruction

universe w

/-! ## The disjointness step the remark compresses -/

section Abstract

variable {P : Type*} [Group P]

/-- **`a ∈ P₂ ∖ {1}` lies outside `P₁`, hence outside the image of `α`.**  This
is the content of the printed "and any `a ∈ P₂ ∖ {1}`": nothing about `P₂`
places `a` outside `α(P) = P₁` except that the two factors of a direct product
intersect trivially. -/
theorem not_mem_range_of_mem_disjoint
    {P₁ P₂ : Subgroup P} (hdisj : Disjoint P₁ P₂) {α : P →* P}
    (hα : ∀ g : P, α g ∈ P₁) {a : P} (haMem : a ∈ P₂) (ha : a ≠ 1) :
    a ∉ Set.range α := by
  rintro ⟨g, rfl⟩
  exact ha (Subgroup.disjoint_def.mp hdisj (hα g) haMem)

/-- An endomorphism missing a single element is not surjective.  This is the
properness the construction's abstract form asks for. -/
theorem not_surjective_of_not_mem_range {α : P →* P} {a : P}
    (ha : a ∉ Set.range α) : ¬ Function.Surjective α :=
  fun hsurj ↦ ha (hsurj a)

/-- The first factor inclusion of a direct product is injective. -/
theorem monoidHom_inl_injective :
    Function.Injective (MonoidHom.inl P P) :=
  fun _ _ hxy ↦ congrArg Prod.fst hxy

/-- The second factor inclusion of a direct product is injective. -/
theorem monoidHom_inr_injective :
    Function.Injective (MonoidHom.inr P P) :=
  fun _ _ hxy ↦ congrArg Prod.snd hxy

end Abstract

/-! ## The printed datum -/

/-- **The input `rem:ff-realization` extracts from Fournier-Facio's theorem.**
A group containing a direct product of two copies of itself, recorded as an
injective homomorphism from `P × P`.

This structure is a *hypothesis*, never a claim.  Every declaration below takes
one as an explicit argument; none constructs one.  What would construct one for
a suitable `P` is Fournier-Facio's theorem, which is proof-ledger row `KC.21`,
is cited to the literature and a personal communication, and is not formalized
in this development. -/
structure ContainsSquare (P : Type*) [Group P] where
  /-- The embedding of `P × P`, whose image is the printed `P₁ × P₂ ≤ P`. -/
  emb : (P × P) →* P
  /-- Injectivity: the image really is a copy of `P × P`. -/
  emb_injective : Function.Injective emb

namespace ContainsSquare

variable {P : Type*} [Group P] (h : ContainsSquare P)

/-- The printed `α : P → P₁ ≤ P`, as an endomorphism of `P`: embed `P` as the
first factor. -/
def alpha : P →* P := h.emb.comp (MonoidHom.inl P P)

/-- The printed first factor `P₁`, the image of `α`. -/
def firstFactor : Subgroup P := h.alpha.range

/-- The printed second factor `P₂`. -/
def secondFactor : Subgroup P := (h.emb.comp (MonoidHom.inr P P)).range

@[simp] theorem alpha_apply (g : P) : h.alpha g = h.emb (g, 1) := rfl

@[simp] theorem embInr_apply (b : P) :
    (h.emb.comp (MonoidHom.inr P P)) b = h.emb (1, b) := rfl

/-- The second factor inclusion into `P` is injective, so `P₂ ≅ P`. -/
theorem embInr_injective :
    Function.Injective (h.emb.comp (MonoidHom.inr P P)) := by
  intro x y hxy
  simp only [h.embInr_apply] at hxy
  exact congrArg Prod.snd (h.emb_injective hxy)

/-- **(1)** `α` is an injective endomorphism of `P`. -/
theorem alpha_injective : Function.Injective h.alpha := by
  intro x y hxy
  simp only [h.alpha_apply] at hxy
  exact congrArg Prod.fst (h.emb_injective hxy)

/-- The printed isomorphism `α : P → P₁`: `α` is injective, so it is an
isomorphism onto its image, which is `P₁` by definition. -/
noncomputable def alphaEquivFirstFactor : P ≃* h.firstFactor :=
  MonoidHom.ofInjective h.alpha_injective

/-- `P₂` is a copy of `P` as well, so the printed `Pᵢ ≅ P` holds for both
factors. -/
noncomputable def secondFactorEquiv : P ≃* h.secondFactor :=
  MonoidHom.ofInjective h.embInr_injective

theorem alpha_mem_firstFactor (g : P) : h.alpha g ∈ h.firstFactor :=
  MonoidHom.mem_range.mpr ⟨g, rfl⟩

theorem emb_inr_mem_secondFactor (b : P) : h.emb (1, b) ∈ h.secondFactor :=
  MonoidHom.mem_range.mpr ⟨b, rfl⟩

/-- **The direct-product structure, in the only form the remark uses it.**  The
two factors meet trivially. -/
theorem disjoint_factors : Disjoint h.firstFactor h.secondFactor := by
  rw [Subgroup.disjoint_def]
  intro x hx1 hx2
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hx1
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hx2
  rw [h.alpha_apply] at hg
  rw [h.embInr_apply] at hb
  have hemb : h.emb ((g, 1) : P × P) = h.emb ((1, b) : P × P) := by
    rw [hg, hb]
  have hg1 : g = 1 := congrArg Prod.fst (h.emb_injective hemb)
  rw [← hg, hg1]
  exact map_one h.emb

/-- **(3)** Any nontrivial element of the second factor lies outside the image
of `α`.  Proved directly from injectivity of the embedding, which is the same
argument `disjoint_factors` packages through the subgroup lattice. -/
theorem emb_inr_not_mem_range_alpha {b : P} (hb : b ≠ 1) :
    h.emb (1, b) ∉ Set.range h.alpha := by
  rintro ⟨g, hg⟩
  rw [h.alpha_apply] at hg
  have hpair : ((g, 1) : P × P) = (1, b) := h.emb_injective hg
  exact hb (congrArg Prod.snd hpair).symm

/-- **(2)** `α` is proper as soon as the second factor is nontrivial, which is
what "any `a ∈ P₂ ∖ {1}`" presupposes. -/
theorem not_surjective_alpha {b : P} (hb : b ≠ 1) :
    ¬ Function.Surjective h.alpha :=
  not_surjective_of_not_mem_range (h.emb_inr_not_mem_range_alpha hb)

end ContainsSquare

/-! ## The reduction -/

/-- **`KC.22`.**  The printed data supply exactly the two hypotheses
`thm:kazhdan-clifford` asks of `(α, a)`: injectivity, and an element outside
the image.  Properness is recorded alongside because the manuscript's abstract
states the hypothesis in that form.

No property of `P` is used: this holds for every group containing a square of
itself, with no finiteness, torsion or Kazhdan assumption. -/
theorem construction_hypotheses {P : Type*} [Group P] (h : ContainsSquare P)
    {b : P} (hb : b ≠ 1) :
    Function.Injective h.alpha ∧
      ¬ Function.Surjective h.alpha ∧
      h.emb (1, b) ∉ Set.range h.alpha :=
  ⟨h.alpha_injective, h.not_surjective_alpha hb,
    h.emb_inr_not_mem_range_alpha hb⟩

/-- **The realization, as far as it is unconditional.**  For *every* finitely
presented property-(T) group containing a direct product of two copies of
itself, and every nontrivial `b`, the Kazhdan--Clifford extension at the
printed data `α = ` first-factor embedding and `a = ` the image of `b` in the
second factor is finitely presented, carries a nontrivial central involution,
and is not MF.

This is the whole of `rem:ff-realization` except its first sentence.  Whether
any group satisfies the hypotheses is `KC.21`, is Fournier-Facio's theorem, and
is not decided here. -/
theorem realization {P : Type} [Group P] [Group.IsFinitelyPresented P]
    (hT : HasKazhdanPropertyTComplex.{0, w} P)
    (h : ContainsSquare P) {b : P} (hb : b ≠ 1) :
    Group.IsFinitelyPresented (Extension h.alpha (h.emb (1, b))) ∧
      mark h.alpha (h.emb (1, b)) ≠ 1 ∧
      mark h.alpha (h.emb (1, b)) ^ 2 = 1 ∧
      (∀ g : Extension h.alpha (h.emb (1, b)),
        Commute (mark h.alpha (h.emb (1, b))) g) ∧
      ¬ IsCDEOperatorMF (Extension h.alpha (h.emb (1, b))) := by
  obtain ⟨hfp, _, hne, hsq, hcentral, _, hMF⟩ :=
    kazhdanCliffordConstruction h.alpha h.alpha_injective (h.emb (1, b)) hT
      (h.emb_inr_not_mem_range_alpha hb)
  exact ⟨hfp, hne, hsq, hcentral, hMF⟩

/-- **The remark's closing sentence.**  `E(P,α,a)` has torsion, witnessed by
the marked word: an `x ≠ 1` with `x ^ 2 = 1` in the extension.

Until 2026-08-18 the manuscript attributed the torsion to the adjoined
involution `c` instead, and this docstring recorded the resulting mismatch of
witness (ledger row `KC.23`).  An external audit found that reason to be a
non-sequitur in its own right — a presentation relation `c ^ 2 = 1` does not
show `c ≠ 1`, since the presented quotient may collapse `c` — and
`\ref{rem:ff-realization}` now attributes the torsion to the nontrivial central
involution `w` that `\ref{thm:kazhdan-clifford}` produces.  That `w` is exactly
the marked word exhibited below, so the printed witness and this one are the
same element and `KC.23` is `EXACT` in both columns.
-/
theorem exists_involution {P : Type} [Group P] [Group.IsFinitelyPresented P]
    (hT : HasKazhdanPropertyTComplex.{0, w} P)
    (h : ContainsSquare P) {b : P} (hb : b ≠ 1) :
    ∃ x : Extension h.alpha (h.emb (1, b)), x ≠ 1 ∧ x ^ 2 = 1 := by
  obtain ⟨_, hne, hsq, _, _⟩ := realization hT h hb
  exact ⟨mark h.alpha (h.emb (1, b)), hne, hsq⟩

end RealizationFromUniversalGroup
end GroupApproximation
