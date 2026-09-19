import GroupApproximation.KTheory.BlockMoves
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# `K₀` in the projection picture

For a compact Hausdorff `X` the campaign's model of a complex vector bundle is
a projection `p : Matrix (Fin N) (Fin N) C(X, ℂ)`, with bundle isomorphism
given by Murray--von Neumann equivalence and direct sum by `blockSum`.  This
file builds, over an arbitrary `*`-ring `A`, the monoid of stable isomorphism
classes of such projections and its Grothendieck group.  Taking
`A = C(X, ℂ)` gives `K⁰(X)`; taking `A` a C-star algebra gives operator
`K₀(A)`.  Nothing below is analytic: the whole construction is `*`-ring
algebra, which is exactly why the projection picture is the cheap one.

## The equivalence

`Cycle A` is a projection in *some* matrix algebra over `A`.  Two cycles
present the same class when they are related by a chain of three elementary
moves, packaged as the inductive relation `Cycle.Step`:

* `mvn` -- Murray--von Neumann equivalence inside a fixed matrix size;
* `reindex` -- relabelling the matrix by an `Equiv` of index sets;
* `pad` -- adjoining a zero block, i.e. adding a rank-zero bundle.

`Cycle.Rel` is the equivalence closure `Relation.EqvGen Cycle.Step`.  Taking
the closure rather than writing the transitive relation by hand costs nothing
here: every consumer below works with the moves, never with a normal form, so
the closure buys the equivalence-relation proof for free and leaves the
substantive content -- that the block sum descends and is a commutative monoid
-- where it belongs, in the reindexing identities of `BlockMoves.lean`.

That these three moves are the classical stable-isomorphism relation is the
*definition* adopted here, not a theorem proved here: the tree contains no
second definition of stable isomorphism to compare it against, so there is
nothing to state.  What is checked is that the relation is an equivalence, that
the block sum descends along it, and that the quotient is a commutative monoid.
Should a lane later introduce a rival definition -- a padding-and-cancellation
form, say -- the agreement becomes a real obligation and belongs in that lane.

`reindex` is a genuine generator and not an instance of `mvn`: an `Equiv`
`Fin m ≃ Fin n` forces `m = n`, and relabelling is then conjugation by a
permutation unitary, but exhibiting that unitary is exactly the permutation
matrix the block calculus is set up to avoid.

## What is proved

* `Cycle.setoid` -- `Rel` is an equivalence relation;
* `VMonoid A` -- the quotient, with `AddCommMonoid` structure whose addition is
  the block sum: associativity is `blockSum_assoc`, commutativity is
  `blockSum_comm`, and the unit is the empty matrix;
* `KZero A` -- its Grothendieck group.
-/

namespace GroupApproximation
namespace KTheory

open Matrix

/-- A `K`-theory cycle over `A`: a projection in some matrix algebra over `A`.

Over `A = C(X, ℂ)` this is the campaign's model of a complex vector bundle on
`X`, presented by a continuous projection-valued map. -/
structure Cycle (A : Type*) [NonUnitalSemiring A] [StarRing A] where
  /-- The size of the ambient matrix algebra. -/
  size : ℕ
  /-- The projection presenting the bundle. -/
  proj : Matrix (Fin size) (Fin size) A
  /-- The presenting matrix is a projection. -/
  isProj : IsStarProjection proj

namespace Cycle

variable {A : Type*} [NonUnitalSemiring A] [StarRing A]

/-- Two cycles of the same size with the same projection are equal: the
`isProj` field is a proposition. -/
theorem eq_of_proj_eq {n : ℕ} {p q : Matrix (Fin n) (Fin n) A}
    {hp : IsStarProjection p} {hq : IsStarProjection q} (h : p = q) :
    (⟨n, p, hp⟩ : Cycle A) = ⟨n, q, hq⟩ := by
  subst h; rfl

/-- The zero cycle: the empty matrix, presenting the rank-zero bundle. -/
instance : Zero (Cycle A) := ⟨⟨0, 0, IsStarProjection.zero _⟩⟩

/-- The sum of cycles is the block sum of the presenting projections. -/
instance : Add (Cycle A) :=
  ⟨fun x y => ⟨x.size + y.size, blockSum x.proj y.proj,
    isStarProjection_blockSum x.isProj y.isProj⟩⟩

@[simp] theorem size_add (x y : Cycle A) : (x + y).size = x.size + y.size := rfl
@[simp] theorem proj_add (x y : Cycle A) : (x + y).proj = blockSum x.proj y.proj := rfl
@[simp] theorem size_zero : (0 : Cycle A).size = 0 := rfl
@[simp] theorem proj_zero : (0 : Cycle A).proj = 0 := rfl

/-- **The three elementary moves on cycles.**  See the module docstring. -/
inductive Step : Cycle A → Cycle A → Prop
  | mvn {n : ℕ} {p q : Matrix (Fin n) (Fin n) A} {hp : IsStarProjection p}
      {hq : IsStarProjection q} (h : MurrayVonNeumannEquiv p q) :
      Step ⟨n, p, hp⟩ ⟨n, q, hq⟩
  | reindex {n m : ℕ} {p : Matrix (Fin n) (Fin n) A} {hp : IsStarProjection p}
      (e : Fin m ≃ Fin n) :
      Step ⟨n, p, hp⟩ ⟨m, p.submatrix e e, isStarProjection_submatrix e hp⟩
  | pad {n : ℕ} {p : Matrix (Fin n) (Fin n) A} {hp : IsStarProjection p} (a : ℕ) :
      Step ⟨n, p, hp⟩
        ⟨n + a, blockSum p (0 : Matrix (Fin a) (Fin a) A),
          isStarProjection_blockSum hp (IsStarProjection.zero _)⟩

/-- **Stable isomorphism of cycles.** -/
def Rel : Cycle A → Cycle A → Prop := Relation.EqvGen Step

theorem rel_of_step {x y : Cycle A} (h : Step x y) : Rel x y := Relation.EqvGen.rel _ _ h

theorem rel_refl (x : Cycle A) : Rel x x := Relation.EqvGen.refl _

theorem rel_symm {x y : Cycle A} (h : Rel x y) : Rel y x := Relation.EqvGen.symm _ _ h

theorem rel_trans {x y z : Cycle A} (h₁ : Rel x y) (h₂ : Rel y z) : Rel x z :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

theorem rel_equivalence : Equivalence (Rel (A := A)) := Relation.EqvGen.is_equivalence _

instance setoid : Setoid (Cycle A) := ⟨Rel, rel_equivalence⟩

/-- A cycle is stably isomorphic to any relabelling of it. -/
theorem rel_reindex {n m : ℕ} {p : Matrix (Fin n) (Fin n) A} (hp : IsStarProjection p)
    (e : Fin m ≃ Fin n) :
    Rel (⟨n, p, hp⟩ : Cycle A) ⟨m, p.submatrix e e, isStarProjection_submatrix e hp⟩ :=
  rel_of_step (Step.reindex e)

/-- The relabelled form of a cycle, in the shape in which the moves below
produce it. -/
theorem rel_reindex_eq {n m : ℕ} {p : Matrix (Fin n) (Fin n) A}
    {q : Matrix (Fin m) (Fin m) A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (e : Fin m ≃ Fin n) (h : p.submatrix e e = q) :
    Rel (⟨n, p, hp⟩ : Cycle A) ⟨m, q, hq⟩ := by
  subst h
  exact rel_reindex hp e

/-! ## The block sum descends -/

/-- **The block sum is commutative up to stable isomorphism.** -/
theorem rel_add_comm (x y : Cycle A) : Rel (x + y) (y + x) :=
  rel_reindex_eq (isStarProjection_blockSum x.isProj y.isProj)
    (isStarProjection_blockSum y.isProj x.isProj) (finSumSwap y.size x.size)
    (blockSum_comm x.proj y.proj)

/-- One elementary move on the left summand survives adding a fixed cycle on
the right. -/
theorem Step.rel_add_right {x y : Cycle A} (h : Step x y) (z : Cycle A) :
    Rel (x + z) (y + z) := by
  obtain ⟨c, s, hs⟩ := z
  cases h with
  | @mvn n p q hp hq hpq =>
      exact rel_of_step
        (Step.mvn (murrayVonNeumannEquiv_blockSum hpq (MurrayVonNeumannEquiv.refl hs)))
  | @reindex n m p hp e =>
      refine rel_reindex_eq (isStarProjection_blockSum hp hs)
        (isStarProjection_blockSum (isStarProjection_submatrix e hp) hs)
        (finSumCongr e (Equiv.refl (Fin c))) ?_
      rw [blockSum_submatrix]
      simp
  | @pad n p hp a =>
      -- `(p ⊞ s)`  →pad→  `(p ⊞ s) ⊞ 0` ←reindex← `p ⊞ (s ⊞ 0)`
      --            ←reindex← `p ⊞ (0 ⊞ s)` →reindex→ `(p ⊞ 0) ⊞ s`
      have h₁ : Rel (⟨n + c, blockSum p s, isStarProjection_blockSum hp hs⟩ : Cycle A)
          ⟨n + c + a, blockSum (blockSum p s) (0 : Matrix (Fin a) (Fin a) A),
            isStarProjection_blockSum (isStarProjection_blockSum hp hs)
              (IsStarProjection.zero _)⟩ :=
        rel_of_step (Step.pad a)
      have h₂ : Rel (⟨n + (c + a),
            blockSum p (blockSum s (0 : Matrix (Fin a) (Fin a) A)),
            isStarProjection_blockSum hp
              (isStarProjection_blockSum hs (IsStarProjection.zero _))⟩ : Cycle A)
          ⟨n + c + a, blockSum (blockSum p s) (0 : Matrix (Fin a) (Fin a) A),
            isStarProjection_blockSum (isStarProjection_blockSum hp hs)
              (IsStarProjection.zero _)⟩ :=
        rel_reindex_eq _ _ (finSumAssoc n c a) (blockSum_assoc p s 0)
      have h₃ : Rel (⟨n + (a + c),
            blockSum p (blockSum (0 : Matrix (Fin a) (Fin a) A) s),
            isStarProjection_blockSum hp
              (isStarProjection_blockSum (IsStarProjection.zero _) hs)⟩ : Cycle A)
          ⟨n + (c + a), blockSum p (blockSum s (0 : Matrix (Fin a) (Fin a) A)),
            isStarProjection_blockSum hp
              (isStarProjection_blockSum hs (IsStarProjection.zero _))⟩ := by
        refine rel_reindex_eq _ _ (finSumCongr (Equiv.refl (Fin n)) (finSumSwap c a)) ?_
        rw [blockSum_submatrix, blockSum_comm]
        simp
      have h₄ : Rel (⟨n + (a + c),
            blockSum p (blockSum (0 : Matrix (Fin a) (Fin a) A) s),
            isStarProjection_blockSum hp
              (isStarProjection_blockSum (IsStarProjection.zero _) hs)⟩ : Cycle A)
          ⟨n + a + c, blockSum (blockSum p (0 : Matrix (Fin a) (Fin a) A)) s,
            isStarProjection_blockSum
              (isStarProjection_blockSum hp (IsStarProjection.zero _)) hs⟩ :=
        rel_reindex_eq _ _ (finSumAssoc n a c) (blockSum_assoc p 0 s)
      exact rel_trans h₁ (rel_trans (rel_symm h₂) (rel_trans (rel_symm h₃) h₄))

theorem rel_add_right {x y : Cycle A} (h : Rel x y) (z : Cycle A) : Rel (x + z) (y + z) := by
  induction h with
  | rel _ _ hxy => exact hxy.rel_add_right z
  | refl _ => exact rel_refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

theorem rel_add_left {x y : Cycle A} (h : Rel x y) (z : Cycle A) : Rel (z + x) (z + y) :=
  rel_trans (rel_add_comm z x) (rel_trans (rel_add_right h z) (rel_add_comm y z))

theorem rel_add {x y x' y' : Cycle A} (hx : Rel x x') (hy : Rel y y') :
    Rel (x + y) (x' + y') :=
  rel_trans (rel_add_right hx y) (rel_add_left hy x')

/-! ## The monoid laws, on representatives -/

theorem rel_add_assoc (x y z : Cycle A) : Rel (x + y + z) (x + (y + z)) :=
  rel_symm (rel_reindex_eq _ _ (finSumAssoc x.size y.size z.size)
    (blockSum_assoc x.proj y.proj z.proj))

theorem add_zero_cycle (x : Cycle A) : x + 0 = x :=
  eq_of_proj_eq (blockSum_zero_right x.proj)

theorem rel_zero_add (x : Cycle A) : Rel (0 + x) x := by
  refine rel_trans (rel_add_comm 0 x) ?_
  rw [add_zero_cycle]
  exact rel_refl x

end Cycle

/-- **The monoid of stable isomorphism classes of projections over `A`.**

For `A = C(X, ℂ)` this is the monoid of stable isomorphism classes of complex
vector bundles on `X`, whose Grothendieck group is `K⁰(X)`. -/
def VMonoid (A : Type*) [NonUnitalSemiring A] [StarRing A] :=
  Quotient (Cycle.setoid (A := A))

namespace VMonoid

variable {A : Type*} [NonUnitalSemiring A] [StarRing A]

/-- The stable isomorphism class of a cycle. -/
def mk (x : Cycle A) : VMonoid A := Quotient.mk _ x

instance : Add (VMonoid A) :=
  ⟨Quotient.map₂ (· + ·) fun _ _ hx _ _ hy => Cycle.rel_add hx hy⟩

instance : Zero (VMonoid A) := ⟨mk 0⟩

@[simp] theorem mk_add (x y : Cycle A) : mk (x + y) = mk x + mk y := rfl

@[simp] theorem mk_zero : mk (0 : Cycle A) = 0 := rfl

theorem mk_eq_mk_of_rel {x y : Cycle A} (h : Cycle.Rel x y) : mk x = mk y :=
  Quotient.sound h

instance : AddCommMonoid (VMonoid A) where
  add_assoc a b c :=
    Quotient.inductionOn₃ a b c fun x y z => mk_eq_mk_of_rel (Cycle.rel_add_assoc x y z)
  zero_add a := Quotient.inductionOn a fun x => mk_eq_mk_of_rel (Cycle.rel_zero_add x)
  add_zero a := Quotient.inductionOn a fun x => congrArg mk (Cycle.add_zero_cycle x)
  add_comm a b := Quotient.inductionOn₂ a b fun x y => mk_eq_mk_of_rel (Cycle.rel_add_comm x y)
  nsmul := nsmulRec

end VMonoid

/-- **`K₀` in the projection picture**: the Grothendieck group of the monoid of
stable isomorphism classes of projections over `A`.

For `A = C(X, ℂ)` with `X` compact Hausdorff this is `K⁰(X)`. -/
def KZero (A : Type*) [NonUnitalSemiring A] [StarRing A] :=
  Algebra.GrothendieckAddGroup (VMonoid A)

namespace KZero

variable {A : Type*} [NonUnitalSemiring A] [StarRing A]

instance : AddCommGroup (KZero A) :=
  inferInstanceAs (AddCommGroup (Algebra.GrothendieckAddGroup (VMonoid A)))

/-- The class in `K₀` of a projection. -/
def mk (x : Cycle A) : KZero A := Algebra.GrothendieckAddGroup.of (VMonoid.mk x)

@[simp] theorem mk_add (x y : Cycle A) : mk (x + y) = mk x + mk y := by
  show Algebra.GrothendieckAddGroup.of (VMonoid.mk (x + y))
      = Algebra.GrothendieckAddGroup.of (VMonoid.mk x)
        + Algebra.GrothendieckAddGroup.of (VMonoid.mk y)
  rw [VMonoid.mk_add, map_add]

@[simp] theorem mk_zero : mk (0 : Cycle A) = 0 := by
  show Algebra.GrothendieckAddGroup.of (VMonoid.mk (0 : Cycle A)) = 0
  rw [VMonoid.mk_zero, map_zero]

end KZero

end KTheory
end GroupApproximation
