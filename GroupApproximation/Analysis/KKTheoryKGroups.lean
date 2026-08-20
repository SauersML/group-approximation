import GroupApproximation.Analysis.KKTheoryKasparov

/-!
# `K`-theory in its `KK`-picture, and the comparison map of the UCT

Kasparov's theorem `K₀(A) ≅ KK(ℂ, A)` makes the `KK`-picture available as a
*definition* of `K`-theory once `KK` is in hand, and that is what is used
here: `KZero T A := T.Grp ℂ A`.  Nothing is thereby assumed --- the definition
is a definition --- but two things should be said plainly.

**Why not the projection picture.**  The classical construction of `K₀(A)` is
the Grothendieck group of Murray--von Neumann classes of projections in
`M∞(A)`.  The repository has the equivalence relation
(`GroupApproximation.MurrayVonNeumannEquiv`, in
`Analysis.FiniteCStarMurrayVonNeumann`) but not the monoid: assembling it
needs block-diagonal sums, padding maps between matrix sizes, and permutation
unitaries realizing commutativity, none of which exists here.  Building it
would not, in any case, connect to `KK` without Kasparov's theorem, so the
`KK`-picture is both cheaper and more honest about what is being assumed.

**Why only `K₀`.**  `K₁(A) = KK(C₀(ℝ), A)` needs the suspension `C₀(ℝ) ⊗ A`,
hence the tensor product of a non-unital commutative algebra with `A`; the
repository has tensor products of C⋆-algebras
(`Analysis.CStarMinTensorNorm`) but not `C₀(ℝ)` itself.  So the graded group
`K_*` is not available, and the universal coefficient sequence --- which is a
statement about `K_*`, not about `K₀` alone --- cannot be written in full.
What *can* be written, and is written in
`Analysis.UniversalCoefficientTheorem`, is its degree-zero comparison map and
the surjectivity half.

## Universe

`ℂ` lives in `Type 0`, so the unit object of the Kasparov category does, and
these definitions are stated for `KasparovTheory.{0}`.  Every separable
C⋆-algebra is `Type 0`-sized up to isomorphism, so this is not a restriction
on the mathematics; it is a restriction on the *presentation* of an algebra,
and the Tikuisis--White--Winter assembly, which quantifies over a universe,
keeps the UCT abstract precisely so that it does not have to care.

## What is proved

All of it unconditionally, from the axioms of `KasparovTheory`:

* `gamma` --- the comparison map `KK(A,B) → Hom(K₀ A, K₀ B)`, as a genuine
  `AddMonoidHom`, defined by Kasparov product on the right;
* `gamma_unit`, `gamma_product` --- `gamma` is a functor;
* `kZero_addEquiv_of_kkEquivalent` --- **`KK`-equivalent algebras have
  isomorphic `K`-theory**.  This is the theorem that makes the bootstrap class
  a `K`-theoretic notion, and it is proved here rather than assumed.
-/

namespace GroupApproximation
namespace KK

namespace KasparovTheory

variable (T : KasparovTheory.{0})

noncomputable section

/-! ## `K`-theory -/

/-- **`K₀` in its `KK`-picture**: `K₀(A) = KK(ℂ, A)`.

An `abbrev` rather than a `def`, so that the `AddCommGroup` instance carried
by `T.Grp` is found by instance search without unfolding. -/
abbrev KZero (A : SepCStarAlgebra.{0}) : Type := T.Grp complexAlgebra A

variable {T}

/-! ## The comparison map -/

/-- **The comparison map of the universal coefficient theorem.**  A
`KK`-class `x ∈ KK(A,B)` acts on `K₀(A) = KK(ℂ,A)` by Kasparov product on the
right, giving a homomorphism `K₀(A) → K₀(B)`.  This is the map the UCT
asserts to be surjective with kernel an `Ext` group.

Additivity is exactly the left-additivity clause of `IsBilinear`, which is why
that clause is carried as a hypothesis here. -/
def gamma (hb : T.IsBilinear) {A B : SepCStarAlgebra.{0}} (x : T.Grp A B) :
    KZero T A →+ KZero T B :=
  AddMonoidHom.mk' (fun z => T.product z x) fun z z' => (hb z z' x x).1

@[simp] theorem gamma_apply (hb : T.IsBilinear) {A B : SepCStarAlgebra.{0}}
    (x : T.Grp A B) (z : KZero T A) : gamma hb x z = T.product z x := rfl

/-- The comparison map of the identity class is the identity. -/
theorem gamma_unit (hb : T.IsBilinear) (A : SepCStarAlgebra.{0}) :
    gamma hb (T.unit A) = AddMonoidHom.id (KZero T A) := by
  ext z
  rw [gamma_apply, T.product_unit z]
  rfl

/-- **The comparison map is functorial.**  Note the order: `gamma` is
covariant, so the product `x · y` acts as "first `x`, then `y`". -/
theorem gamma_product (hb : T.IsBilinear) {A B C : SepCStarAlgebra.{0}}
    (x : T.Grp A B) (y : T.Grp B C) :
    gamma hb (T.product x y) = (gamma hb y).comp (gamma hb x) := by
  ext z
  rw [gamma_apply, AddMonoidHom.comp_apply, gamma_apply, gamma_apply,
    T.product_assoc z x y]

/-! ## `K`-theory is a `KK`-invariant -/

/-- **`KK`-equivalent algebras have isomorphic `K`-theory.**

The comparison maps of the two implementing classes are mutually inverse, by
functoriality and the two identities defining a `KK`-equivalence.  Stated as
`Nonempty` because the implementing classes are only known to exist: choosing
one of them is exactly the content of the existential in `KKEquivalent`, and
nothing downstream needs a *canonical* isomorphism. -/
theorem kZero_addEquiv_of_kkEquivalent (hb : T.IsBilinear)
    {A B : SepCStarAlgebra.{0}} (h : T.KKEquivalent A B) :
    Nonempty (KZero T A ≃+ KZero T B) := by
  obtain ⟨x, y, hxy, hyx⟩ := h
  have hleft : ∀ z : KZero T A, gamma hb y (gamma hb x z) = z := by
    intro z
    have h1 : gamma hb (T.product x y) = (gamma hb y).comp (gamma hb x) :=
      gamma_product hb x y
    rw [hxy, gamma_unit hb A] at h1
    have h2 := congrArg (fun f : KZero T A →+ KZero T A => f z) h1
    simpa using h2.symm
  have hright : ∀ w : KZero T B, gamma hb x (gamma hb y w) = w := by
    intro w
    have h1 : gamma hb (T.product y x) = (gamma hb x).comp (gamma hb y) :=
      gamma_product hb y x
    rw [hyx, gamma_unit hb B] at h1
    have h2 := congrArg (fun f : KZero T B →+ KZero T B => f w) h1
    simpa using h2.symm
  exact ⟨{ toFun := fun z => gamma hb x z
           invFun := fun w => gamma hb y w
           left_inv := hleft
           right_inv := hright
           map_add' := fun z z' => (gamma hb x).map_add z z' }⟩

end

end KasparovTheory

end KK
end GroupApproximation
