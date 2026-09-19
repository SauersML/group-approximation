import GroupApproximation.Analysis.KKTheoryKGroups

/-!
# The universal coefficient theorem

`Analysis.TikuisisWhiteWinter` carries the UCT as an **uninterpreted
predicate parameter** `UCT : Type u → Prop`, with the explicit note that
"`KK`-theory does not exist in this development or in mathlib, so no honest
definition can be given here".  With `Analysis.KKTheoryKasparov` in place that
is no longer true, and this file replaces the parameter by a definition.

## The definition, and why this one

Rosenberg and Schochet (*The Künneth theorem and the universal coefficient
theorem for Kasparov's generalized `K`-functor*, Duke Math. J. **55** (1987),
431--474) prove that for a separable C⋆-algebra `A` the following are
equivalent:

1. for every `σ`-unital `B` the natural sequence
   `0 → Ext¹(K_*(A), K_{*+1}(B)) → KK(A,B) → Hom(K_*(A), K_*(B)) → 0`
   is exact --- "`A` satisfies the UCT";
2. `A` belongs to the bootstrap class `N`;
3. **`A` is `KK`-equivalent to a commutative C⋆-algebra.**

Form 3 is taken as the definition here (`SatisfiesUCT`).  Three reasons, in
order of weight.

* It is *statable*.  Form 1 quantifies over the graded group `K_*` and over
  `Ext¹`; `K₁` needs the suspension `C₀(ℝ) ⊗ A`, which this development cannot
  build (see `Analysis.KKTheoryKGroups`).  Writing form 1 today would mean
  writing a fragment of it and calling it the UCT.
* It is the form the *closure* arguments use.  Everything one proves about the
  UCT class --- that it contains the commutative algebras, that it is closed
  under `KK`-equivalence, under homotopy equivalence, under isomorphism --- is
  immediate from form 3 and requires an argument from form 1.
* It is the form Tikuisis--White--Winter's proof consumes.  The UCT enters
  their argument through the Dadarlat--Eilers stable uniqueness theorem, whose
  hypothesis is membership in the bootstrap class.

The equivalence `1 ↔ 3` is Rosenberg--Schochet's theorem, and it is **not**
proved here.  It is recorded as `RosenbergSchochetInput` --- with the half of
form 1 that *is* statable, the surjectivity of the degree-zero comparison map
`gamma` --- so that a reader can see precisely which implication is being
taken on trust and in which direction it is used.  No theorem below consumes
it: the definition is form 3 throughout.

## What is proved, unconditionally

* commutative algebras satisfy the UCT;
* the UCT class is closed under `KK`-equivalence, under mutually inverse
  `⋆`-homomorphisms, and under homotopy equivalence;
* `ℂ` satisfies the UCT;
* a UCT algebra has the `K`-theory of a commutative algebra
  (`kZero_of_satisfiesUCT`), which is the concrete `K`-theoretic shadow of
  the definition.
-/

namespace GroupApproximation
namespace KK

namespace KasparovTheory

universe u

variable (T : KasparovTheory.{u})

/-! ## The bootstrap class -/

/-- **`A` satisfies the universal coefficient theorem** when it is
`KK`-equivalent to a commutative C⋆-algebra.

This is Rosenberg--Schochet's characterization of the bootstrap class `N`,
taken as the definition; see the module docstring for why. -/
def SatisfiesUCT (A : SepCStarAlgebra.{u}) : Prop :=
  ∃ C : SepCStarAlgebra.{u}, C.IsCommutative ∧ T.KKEquivalent A C

variable {T}

/-- **A commutative C⋆-algebra satisfies the UCT.**  It is `KK`-equivalent to
itself. -/
theorem satisfiesUCT_of_isCommutative {A : SepCStarAlgebra.{u}}
    (hA : A.IsCommutative) : T.SatisfiesUCT A :=
  ⟨A, hA, kkEquivalent_refl A⟩

/-- **The UCT class is closed under `KK`-equivalence.**  This is the closure
property every application uses, and under the definition taken here it is
exactly the transitivity of `KK`-equivalence. -/
theorem SatisfiesUCT.of_kkEquivalent {A B : SepCStarAlgebra.{u}}
    (hA : T.SatisfiesUCT A) (h : T.KKEquivalent A B) : T.SatisfiesUCT B := by
  obtain ⟨C, hC, hAC⟩ := hA
  exact ⟨C, hC, KKEquivalent.trans h.symm hAC⟩

/-- The UCT class is closed under isomorphism. -/
theorem SatisfiesUCT.of_inverse {A B : SepCStarAlgebra.{u}}
    (hA : T.SatisfiesUCT A) (f : A →⋆ₐ[ℂ] B) (g : B →⋆ₐ[ℂ] A)
    (hgf : ∀ a : A, g (f a) = a) (hfg : ∀ b : B, f (g b) = b) :
    T.SatisfiesUCT B :=
  hA.of_kkEquivalent (kkEquivalent_of_inverse f g hgf hfg)

/-- The UCT class is closed under homotopy equivalence. -/
theorem SatisfiesUCT.of_homotopyEquiv {A B : SepCStarAlgebra.{u}}
    (hA : T.SatisfiesUCT A) (f : A →⋆ₐ[ℂ] B) (g : B →⋆ₐ[ℂ] A)
    (hgf : Homotopic (g.comp f) (StarAlgHom.id ℂ A))
    (hfg : Homotopic (f.comp g) (StarAlgHom.id ℂ B)) :
    T.SatisfiesUCT B :=
  hA.of_kkEquivalent (kkEquivalent_of_homotopyEquiv f g hgf hfg)

/-! ## The scalars -/

/-- **`ℂ` satisfies the UCT.**  Stated at universe `0`, where `ℂ` lives.

This is the base case of every bootstrap argument, and here it is a theorem
rather than a citation: `ℂ` is commutative. -/
theorem complexAlgebra_satisfiesUCT {T₀ : KasparovTheory.{0}} :
    T₀.SatisfiesUCT complexAlgebra :=
  satisfiesUCT_of_isCommutative complexAlgebra_isCommutative

/-! ## The `K`-theoretic shadow -/

/-- **A UCT algebra has the `K`-theory of a commutative algebra.**

This is the only consequence of the UCT that the present development can
compute, and it is proved rather than assumed: `KK`-equivalence transports
`K₀` (`kZero_addEquiv_of_kkEquivalent`), so the definition of `SatisfiesUCT`
delivers a commutative model for `K₀` on the nose. -/
theorem kZero_of_satisfiesUCT {T₀ : KasparovTheory.{0}} (hb : T₀.IsBilinear)
    {A : SepCStarAlgebra.{0}} (hA : T₀.SatisfiesUCT A) :
    ∃ C : SepCStarAlgebra.{0}, C.IsCommutative ∧
      Nonempty (KZero T₀ A ≃+ KZero T₀ C) := by
  obtain ⟨C, hC, hAC⟩ := hA
  exact ⟨C, hC, kZero_addEquiv_of_kkEquivalent hb hAC⟩

/-! ## The Rosenberg--Schochet theorem, as a typed input -/

/-- **The universal coefficient sequence, in the degree it can be written.**

The full Rosenberg--Schochet sequence is a statement about the graded group
`K_*`; its degree-zero fragment says that the comparison map
`gamma : KK(A,B) → Hom(K₀ A, K₀ B)` is *surjective*.  That fragment is
expressible with the `K`-theory this development has, and it is exactly what
`RosenbergSchochetInput` asserts of algebras in the bootstrap class.

Injectivity modulo `Ext¹` --- the other half of the sequence --- is not
expressible here, because `Ext¹` of the graded `K`-groups is not; that is
recorded in the docstring of `RosenbergSchochetInput` rather than silently
dropped. -/
def UCTComparisonSurjective (T₀ : KasparovTheory.{0}) (hb : T₀.IsBilinear)
    (A : SepCStarAlgebra.{0}) : Prop :=
  ∀ (B : SepCStarAlgebra.{0}) (θ : KZero T₀ A →+ KZero T₀ B),
    ∃ x : T₀.Grp A B, gamma hb x = θ

/-- **Rosenberg--Schochet, as a typed input.**

Duke Math. J. 55 (1987), Theorem 1.17 and Proposition 5.3: an algebra in the
bootstrap class satisfies the universal coefficient sequence, and conversely.
Only the direction used is asserted, and only in the degree that can be
stated: a UCT algebra --- in the sense of `SatisfiesUCT`, i.e.
`KK`-equivalent to a commutative one --- has surjective comparison map.

**What is dropped, and it is deliberate.**  The sequence also asserts that the
kernel of the comparison map is `Ext¹(K_*(A), K_{*+1}(B))`, and it asserts
naturality.  Neither is expressible without `K₁` and `Ext¹`.  Consequently
this input is *weaker* than the theorem it names, which is the safe direction:
a theorem proved from it is proved from less than Rosenberg--Schochet.

**No inhabitant is constructed here, and nothing in this development consumes
this input** --- `SatisfiesUCT` is defined by `KK`-equivalence throughout, and
the Tikuisis--White--Winter assembly consumes that definition, not this
sequence.  It is stated so that the reader can see what "the UCT" means in the
literature the manuscript cites, and check that the definition used here is
the same notion. -/
structure RosenbergSchochetInput (T₀ : KasparovTheory.{0}) (hb : T₀.IsBilinear) :
    Prop where
  /-- A bootstrap-class algebra has surjective `K`-theoretic comparison
  map. -/
  comparison_surjective : ∀ A : SepCStarAlgebra.{0},
    T₀.SatisfiesUCT A → UCTComparisonSurjective T₀ hb A

end KasparovTheory

end KK
end GroupApproximation
