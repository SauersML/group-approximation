import GroupApproximation.Analysis.KasparovBimodule
import GroupApproximation.Analysis.CStarUnitary

/-!
# Unitary equivalence of Kasparov bimodules, and the commutative monoid laws

`KK(A,B)` is the set of Kasparov bimodules modulo two relations: unitary
equivalence and homotopy.  This file supplies the first, and proves that the
direct sum is a commutative, associative operation *up to it* --- which is
everything the monoid structure of `KK(A,B)` needs before the homotopy
relation enters.

## What is proved

* `swap` and `assocProd`, the two structural unitaries of the direct sum of
  Hilbert modules, together with `IsUnitaryAdj.prodMap`, the direct sum of two
  unitaries;
* `UnitaryEquiv`, and that it is reflexive, symmetric and transitive.  The
  symmetry is the only clause with content: intertwining by `U` gives
  intertwining by `U⋆` because `U⋆` is a two-sided inverse, so one substitutes
  `x := U⋆y` and cancels;
* `UnitaryEquiv.add` --- the direct sum respects unitary equivalence;
* `unitaryEquiv_add_comm` and `unitaryEquiv_add_assoc` --- `⊞` is commutative
  and associative up to unitary equivalence.

Each of the three intertwining clauses of the last two is `rfl`: the grading,
representation and operator of a direct sum are `⊞` of those of the summands,
and `⊞` commutes with the structural unitaries by construction.

## What is deliberately not claimed

That a degenerate bimodule is a *unit* for `⊞`.  It is a unit in `KK(A,B)`,
but only up to **homotopy** --- `M ⊞ (degenerate)` is not unitarily equivalent
to `M`, since its module is strictly bigger.  Asserting it here would be
false; it is one of the two places where the homotopy relation is doing real
work, the other being the inverse.
-/

namespace GroupApproximation
namespace HilbertModule

open OrderZero

universe u v w w' w''

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B]

namespace Adjointable

variable {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B}
variable {G : CStarModule.{v, w''} B}

/-! ## The structural unitaries of a direct sum -/

/-- The flip `E ⊞ F ≅ F ⊞ E`. -/
def swapProd (E : CStarModule.{v, w} B) (F : CStarModule.{v, w'} B) :
    Adjointable (prod E F) (prod F E) where
  toFun p := (p.2, p.1)
  adj q := (q.2, q.1)
  inner_adj p q := by
    show F.inner p.2 q.1 + E.inner p.1 q.2
        = E.inner p.1 q.2 + F.inner p.2 q.1
    rw [add_comm]

theorem isUnitaryAdj_swapProd (E : CStarModule.{v, w} B)
    (F : CStarModule.{v, w'} B) : (swapProd E F).IsUnitaryAdj where
  adj_toFun _ := rfl
  toFun_adj _ := rfl

/-- The associator `(E ⊞ F) ⊞ G ≅ E ⊞ (F ⊞ G)`. -/
def assocProd (E : CStarModule.{v, w} B) (F : CStarModule.{v, w'} B)
    (G : CStarModule.{v, w''} B) :
    Adjointable (prod (prod E F) G) (prod E (prod F G)) where
  toFun p := (p.1.1, (p.1.2, p.2))
  adj q := ((q.1, q.2.1), q.2.2)
  inner_adj p q := by
    show E.inner p.1.1 q.1 + (F.inner p.1.2 q.2.1 + G.inner p.2 q.2.2)
        = E.inner p.1.1 q.1 + F.inner p.1.2 q.2.1 + G.inner p.2 q.2.2
    rw [add_assoc]

theorem isUnitaryAdj_assocProd (E : CStarModule.{v, w} B)
    (F : CStarModule.{v, w'} B) (G : CStarModule.{v, w''} B) :
    (assocProd E F G).IsUnitaryAdj where
  adj_toFun _ := rfl
  toFun_adj _ := rfl

/-- The direct sum of two unitaries is a unitary. -/
theorem IsUnitaryAdj.prodMap {E' : CStarModule.{v, w} B}
    {F' : CStarModule.{v, w'} B} {U : Adjointable E E'}
    {V : Adjointable F F'} (hU : U.IsUnitaryAdj) (hV : V.IsUnitaryAdj) :
    (Adjointable.prodMap U V).IsUnitaryAdj where
  adj_toFun p := Prod.ext (hU.adj_toFun p.1) (hV.adj_toFun p.2)
  toFun_adj q := Prod.ext (hU.toFun_adj q.1) (hV.toFun_adj q.2)

end Adjointable

/-! ## Unitary equivalence of bimodules -/

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **Unitary equivalence of Kasparov bimodules**: a unitary of the underlying
Hilbert modules intertwining the grading, the representation and the
operator. -/
def UnitaryEquiv (M N : KasparovBimodule.{u, v, w} A B) : Prop :=
  ∃ U : Adjointable M.E N.E, U.IsUnitaryAdj
    ∧ (∀ x, U.toFun (M.grading.toFun x) = N.grading.toFun (U.toFun x))
    ∧ (∀ (a : A) (x), U.toFun ((M.pi a).toFun x) = (N.pi a).toFun (U.toFun x))
    ∧ (∀ x, U.toFun (M.op.toFun x) = N.op.toFun (U.toFun x))

namespace UnitaryEquiv

theorem refl (M : KasparovBimodule.{u, v, w} A B) : UnitaryEquiv M M :=
  ⟨Adjointable.id M.E, Adjointable.isUnitaryAdj_id M.E,
    fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- Symmetry.  The three intertwining clauses transport to `U⋆` by
substituting `x := U⋆y` and cancelling `UU⋆ = 1`. -/
theorem symm {M N : KasparovBimodule.{u, v, w} A B} (h : UnitaryEquiv M N) :
    UnitaryEquiv N M := by
  obtain ⟨U, hU, hg, hp, ho⟩ := h
  refine ⟨Adjointable.adjoint U, hU.adjoint, ?_, ?_, ?_⟩
  · intro y
    show U.adj (N.grading.toFun y) = M.grading.toFun (U.adj y)
    have hy : U.toFun (M.grading.toFun (U.adj y))
        = N.grading.toFun (U.toFun (U.adj y)) := hg (U.adj y)
    rw [hU.toFun_adj] at hy
    rw [← hy, hU.adj_toFun]
  · intro a y
    show U.adj ((N.pi a).toFun y) = (M.pi a).toFun (U.adj y)
    have hy : U.toFun ((M.pi a).toFun (U.adj y))
        = (N.pi a).toFun (U.toFun (U.adj y)) := hp a (U.adj y)
    rw [hU.toFun_adj] at hy
    rw [← hy, hU.adj_toFun]
  · intro y
    show U.adj (N.op.toFun y) = M.op.toFun (U.adj y)
    have hy : U.toFun (M.op.toFun (U.adj y))
        = N.op.toFun (U.toFun (U.adj y)) := ho (U.adj y)
    rw [hU.toFun_adj] at hy
    rw [← hy, hU.adj_toFun]

theorem trans {M N P : KasparovBimodule.{u, v, w} A B} (h : UnitaryEquiv M N)
    (h' : UnitaryEquiv N P) : UnitaryEquiv M P := by
  obtain ⟨U, hU, hg, hp, ho⟩ := h
  obtain ⟨V, hV, hg', hp', ho'⟩ := h'
  refine ⟨V.comp U, hV.comp hU, ?_, ?_, ?_⟩
  · intro x
    show V.toFun (U.toFun (M.grading.toFun x))
        = P.grading.toFun (V.toFun (U.toFun x))
    rw [hg x, hg' (U.toFun x)]
  · intro a x
    show V.toFun (U.toFun ((M.pi a).toFun x))
        = (P.pi a).toFun (V.toFun (U.toFun x))
    rw [hp a x, hp' a (U.toFun x)]
  · intro x
    show V.toFun (U.toFun (M.op.toFun x)) = P.op.toFun (V.toFun (U.toFun x))
    rw [ho x, ho' (U.toFun x)]

/-- The direct sum respects unitary equivalence. -/
theorem add {M M' N N' : KasparovBimodule.{u, v, w} A B}
    (h : UnitaryEquiv M M') (h' : UnitaryEquiv N N') :
    UnitaryEquiv (M.add N) (M'.add N') := by
  obtain ⟨U, hU, hg, hp, ho⟩ := h
  obtain ⟨V, hV, hg', hp', ho'⟩ := h'
  refine ⟨Adjointable.prodMap U V, hU.prodMap hV, ?_, ?_, ?_⟩
  · intro p
    exact Prod.ext (hg p.1) (hg' p.2)
  · intro a p
    exact Prod.ext (hp a p.1) (hp' a p.2)
  · intro p
    exact Prod.ext (ho p.1) (ho' p.2)

end UnitaryEquiv

/-- **`⊞` is commutative up to unitary equivalence.** -/
theorem unitaryEquiv_add_comm (M N : KasparovBimodule.{u, v, w} A B) :
    UnitaryEquiv (M.add N) (N.add M) :=
  ⟨Adjointable.swapProd M.E N.E,
    Adjointable.isUnitaryAdj_swapProd M.E N.E,
    fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- **`⊞` is associative up to unitary equivalence.** -/
theorem unitaryEquiv_add_assoc (M N P : KasparovBimodule.{u, v, w} A B) :
    UnitaryEquiv ((M.add N).add P) (M.add (N.add P)) :=
  ⟨Adjointable.assocProd M.E N.E P.E,
    Adjointable.isUnitaryAdj_assocProd M.E N.E P.E,
    fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

end HilbertModule
end GroupApproximation
