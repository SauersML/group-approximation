import GroupApproximation.Matching.FiniteGroupoidCounting

/-!
# Groupoids presented by finite representatives

Cluster arrows are equivalence classes of sufficiently equivariant partial
bijections.  Composition and inversion are performed on representatives and
then improved.  This file isolates the purely algebraic quotient step: any
representative system whose laws hold modulo its stated setoids produces an
actual Mathlib `Groupoid`.
-/

namespace GroupApproximation

universe u v

/-- A groupoid presentation in which all categorical laws need only hold
modulo the specified equivalence relations on representatives. -/
structure GroupoidPresentation (I : Type u) where
  Rep : I → I → Type v
  rel : ∀ X Y, Setoid (Rep X Y)
  one : ∀ X, Rep X X
  comp : ∀ {X Y Z}, Rep X Y → Rep Y Z → Rep X Z
  inv : ∀ {X Y}, Rep X Y → Rep Y X
  comp_respects : ∀ {X Y Z} {f f' : Rep X Y} {g g' : Rep Y Z},
    rel X Y f f' → rel Y Z g g' → rel X Z (comp f g) (comp f' g')
  inv_respects : ∀ {X Y} {f f' : Rep X Y},
    rel X Y f f' → rel Y X (inv f) (inv f')
  one_comp : ∀ {X Y} (f : Rep X Y), rel X Y (comp (one X) f) f
  comp_one : ∀ {X Y} (f : Rep X Y), rel X Y (comp f (one Y)) f
  assoc : ∀ {W X Y Z} (f : Rep W X) (g : Rep X Y) (h : Rep Y Z),
    rel W Z (comp (comp f g) h) (comp f (comp g h))
  inv_comp : ∀ {X Y} (f : Rep X Y), rel Y Y (comp (inv f) f) (one Y)
  comp_inv : ∀ {X Y} (f : Rep X Y), rel X X (comp f (inv f)) (one X)

/-- The one-object, one-arrow presentation.  Besides being the terminal
finite example, this records that the presentation axioms are jointly
satisfiable without importing any groupoid theorem. -/
def unitGroupoidPresentation : GroupoidPresentation Unit where
  Rep := fun _ _ ↦ Unit
  rel := fun _ _ ↦ ⟨Eq, Eq.refl, Eq.symm, Eq.trans⟩
  one := fun _ ↦ ()
  comp := fun _ _ ↦ ()
  inv := fun _ ↦ ()
  comp_respects := by intros; rfl
  inv_respects := by intros; rfl
  one_comp := by intros; rfl
  comp_one := by intros; rfl
  assoc := by intros; rfl
  inv_comp := by intros; rfl
  comp_inv := by intros; rfl

namespace GroupoidPresentation

/-- Objects of the quotient groupoid.  The wrapper keeps the category
instance attached to the particular presentation. -/
structure Obj {I : Type u} (P : GroupoidPresentation I) where
  val : I

variable {I : Type u} (P : GroupoidPresentation I)

instance [Fintype I] : Fintype P.Obj := Fintype.ofEquiv I
  { toFun := fun i ↦ ⟨i⟩
    invFun := Obj.val
    left_inv := fun _ ↦ rfl
    right_inv := fun x ↦ by cases x; rfl }

instance [DecidableEq I] : DecidableEq P.Obj := fun X Y ↦
  decidable_of_iff (X.val = Y.val) ⟨
    fun h ↦ by cases X; cases Y; simp_all,
    congrArg Obj.val⟩

instance : Quiver P.Obj where
  Hom X Y := Quotient (P.rel X.val Y.val)

/-- A quotient Hom-set is finite whenever its representative type is finite.
This is the bridge from a finite cluster presentation to the counting
theorems for finite groupoids. -/
instance homFinite {X Y : P.Obj} [Finite (P.Rep X.val Y.val)] :
    Finite (X ⟶ Y) :=
  Finite.of_surjective
    (@Quotient.mk _ (P.rel X.val Y.val)) Quotient.mk_surjective

noncomputable instance homFintype {X Y : P.Obj}
    [Finite (P.Rep X.val Y.val)] : Fintype (X ⟶ Y) :=
  Fintype.ofFinite _

instance : CategoryTheory.Category P.Obj where
  id X := @Quotient.mk _ (P.rel X.val X.val) (P.one X.val)
  comp {X Y Z} f g := Quotient.liftOn₂ f g
    (fun a b ↦ @Quotient.mk _ (P.rel X.val Z.val) (P.comp a b))
    (fun _ _ _ _ ha hb ↦ @Quotient.sound _ (P.rel X.val Z.val) _ _
      (P.comp_respects ha hb))
  id_comp {X Y} f := by
    induction f using Quotient.inductionOn with
    | _ f => exact @Quotient.sound _ (P.rel X.val Y.val) _ _ (P.one_comp f)
  comp_id {X Y} f := by
    induction f using Quotient.inductionOn with
    | _ f => exact @Quotient.sound _ (P.rel X.val Y.val) _ _ (P.comp_one f)
  assoc {W X Y Z} f g h := by
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g =>
        induction h using Quotient.inductionOn with
        | _ h => exact @Quotient.sound _ (P.rel W.val Z.val) _ _ (P.assoc f g h)

instance : CategoryTheory.Groupoid P.Obj where
  inv {X Y} f := Quotient.liftOn f
    (fun a ↦ @Quotient.mk _ (P.rel Y.val X.val) (P.inv a))
    (fun _ _ h ↦ @Quotient.sound _ (P.rel Y.val X.val) _ _ (P.inv_respects h))
  inv_comp {X Y} f := by
    induction f using Quotient.inductionOn with
    | _ f => exact @Quotient.sound _ (P.rel Y.val Y.val) _ _ (P.inv_comp f)
  comp_inv {X Y} f := by
    induction f using Quotient.inductionOn with
    | _ f => exact @Quotient.sound _ (P.rel X.val X.val) _ _ (P.comp_inv f)

/-- A representative determines an arrow in the presented groupoid. -/
def ofRep {X Y : P.Obj} (f : P.Rep X.val Y.val) : X ⟶ Y :=
  @Quotient.mk _ (P.rel X.val Y.val) f

theorem ofRep_eq_ofRep_iff {X Y : P.Obj} (f g : P.Rep X.val Y.val) :
    P.ofRep f = P.ofRep g ↔ P.rel X.val Y.val f g := by
  exact Quotient.eq

end GroupoidPresentation
end GroupApproximation
