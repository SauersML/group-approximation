import GroupApproximation.KunThom.CountingEndgameLift

/-!
# The counting endgame on the selected objects

`CountingEndgame.exists_bisection_lift` takes a finite set `S` of source objects
together with, at every object of `S`, the target condition and the two counts.
In Kun and Thom's proof of Theorem 4.1 (arXiv:2608.06222v3, §4, tex lines
1218–1236) the good set `E_n` is exactly the set of objects where these hold,
and the rest of the argument only bounds the weight of its complement.

* `selected`: the source objects at which the target condition, the orbit count
  and the isotropy index hold.
* `exists_bisection_lift_selected`: the lift on `selected`, with no per-object
  hypothesis.
-/

namespace GroupApproximation
namespace CountingEndgame

open CategoryTheory

universe u v u' v' u'' v''

/-- The source objects at which the target condition, the orbit count and the
isotropy index of `exists_bisection_lift` hold. -/
noncomputable def selected {C' : Type u'} [Groupoid.{v'} C'] [Fintype C']
    [∀ X Y : C', Fintype (X ⟶ Y)] {D : Type u''} [Groupoid.{v''} D] [Fintype D]
    [DecidableEq D] [∀ X Y : D, Fintype (X ⟶ Y)] (F : C' ⥤ D)
    (a : FiniteGroupoid.Bisection D) (sel : C' → C') : Finset C' :=
  Finset.univ.filter fun X ↦ F.obj (sel X) = a.objEquiv (F.obj X) ∧
    (FiniteGroupoid.orbit (F.obj X)).card <
      (FiniteGroupoid.orbit X).card + (FiniteGroupoid.orbit (sel X)).card ∧
    Fintype.card (F.obj X ⟶ F.obj X) < 2 * Fintype.card (X ⟶ X)

theorem mem_selected {C' : Type u'} [Groupoid.{v'} C'] [Fintype C']
    [∀ X Y : C', Fintype (X ⟶ Y)] {D : Type u''} [Groupoid.{v''} D] [Fintype D]
    [DecidableEq D] [∀ X Y : D, Fintype (X ⟶ Y)] (F : C' ⥤ D)
    (a : FiniteGroupoid.Bisection D) (sel : C' → C') (X : C') :
    X ∈ selected F a sel ↔ F.obj (sel X) = a.objEquiv (F.obj X) ∧
      (FiniteGroupoid.orbit (F.obj X)).card <
        (FiniteGroupoid.orbit X).card + (FiniteGroupoid.orbit (sel X)).card ∧
      Fintype.card (F.obj X ⟶ F.obj X) < 2 * Fintype.card (X ⟶ X) := by
  rw [selected, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ X, h⟩⟩

/-- **The finite endgame on the selected objects.**  Let `F : C' ⥤ D` be faithful
and injective on objects, `J : C' ⥤ C` injective on objects, `a` a total
bisection of `D` and `sel` any choice of targets.  Every object of
`selected F a sel` has a preimage `g : X ⟶ sel X` of the transported arrow of
`a`, and some total bisection of `C` carries `J g` at every such `J X`. -/
theorem exists_bisection_lift_selected
    {C : Type u} [Groupoid.{v} C] [Fintype C] [DecidableEq C]
    {C' : Type u'} [Groupoid.{v'} C'] [Fintype C'] [DecidableEq C']
    [∀ X Y : C', Fintype (X ⟶ Y)]
    {D : Type u''} [Groupoid.{v''} D] [Fintype D] [DecidableEq D]
    [∀ X Y : D, Fintype (X ⟶ Y)]
    (J : C' ⥤ C) (hJ : Function.Injective J.obj)
    (F : C' ⥤ D) [F.Faithful] (hF : Function.Injective F.obj)
    (a : FiniteGroupoid.Bisection D) (sel : C' → C') :
    ∃ b : FiniteGroupoid.Bisection C, ∀ X (hX : X ∈ selected F a sel), ∃ g : X ⟶ sel X,
      F.map g = a.hom (F.obj X) ≫ eqToHom ((mem_selected F a sel X).mp hX).1.symm ∧
        ∃ e : b.objEquiv (J.obj X) = J.obj (sel X),
          b.hom (J.obj X) ≫ eqToHom e = J.map g :=
  exists_bisection_lift J hJ F hF a (selected F a sel) sel
    (fun X hX ↦ ((mem_selected F a sel X).mp hX).1)
    (fun X hX ↦ ((mem_selected F a sel X).mp hX).2.1)
    (fun X hX ↦ ((mem_selected F a sel X).mp hX).2.2)

end CountingEndgame
end GroupApproximation
