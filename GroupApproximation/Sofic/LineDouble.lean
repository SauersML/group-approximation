import GroupApproximation.Sofic.SymmetricDoubleFlip
import GroupApproximation.Sofic.SoficTransfer

/-!
# From the symmetric double to the line double

The notation `*_Γ G` in Gao--Kunnawalkam Elayavalli--Mj denotes the
fundamental group of the graph of groups on the infinite line, with every
vertex group equal to `G`, every edge group equal to `Γ`, and all edge maps
the same inclusion.  Because the line is connected and all inclusions agree,
this colimit is the wide amalgam of copies of `G` indexed by `ℤ` over one copy
of `Γ`.

This file constructs that group as a `PushoutI` and proves directly from its
universal property that the two-vertex symmetric double `G *_Γ G` embeds in
it.  A retraction sends vertex `0` to the first factor and every other vertex
to the second factor.  Consequently, nonsoficity of the symmetric double
implies nonsoficity of the exact line-double group in Question 1.6.
-/

namespace GroupApproximation

open Monoid

variable (G : Type) [Group G] (Γ : Subgroup G)

/-- One copy of `G` at every integer vertex of the line. -/
abbrev LineDoubleFactor : ℤ → Type := fun _ ↦ G

instance lineDoubleFactorGroup : ∀ i, Group (LineDoubleFactor G i) :=
  fun _ ↦ inferInstanceAs (Group G)

/-- Every edge identification is the fixed inclusion `Γ ↪ G`. -/
def lineDoubleMap : ∀ i : ℤ, ↥Γ →* LineDoubleFactor G i :=
  fun _ ↦ Γ.subtype

theorem lineDoubleMap_injective :
    ∀ i, Function.Injective (lineDoubleMap G Γ i) :=
  fun _ ↦ Γ.subtype_injective

/-- The infinite line double `*_Γ G`. -/
abbrev LineDouble : Type := PushoutI (lineDoubleMap G Γ)

/-- A canonical vertex-group embedding into the line double. -/
def inLineDouble (i : ℤ) : G →* LineDouble G Γ :=
  PushoutI.of (φ := lineDoubleMap G Γ) i

theorem inLineDouble_injective (i : ℤ) :
    Function.Injective (inLineDouble G Γ i) :=
  PushoutI.of_injective (lineDoubleMap_injective G Γ) i

instance lineDoubleFactorCountable [Countable G] :
    ∀ i, Countable (LineDoubleFactor G i) :=
  fun _ ↦ inferInstanceAs (Countable G)

instance lineDoubleCountable [Countable G] : Countable (LineDouble G Γ) := by
  haveI hΓ : Countable ↥Γ := Subtype.countable
  haveI h0 : Countable (FreeMonoid (Σ i, LineDoubleFactor G i)) :=
    inferInstanceAs (Countable (List (Σ i, LineDoubleFactor G i)))
  haveI h1 : Countable (CoprodI (LineDoubleFactor G)) :=
    Con.mk'_surjective.countable
  haveI h2 : Countable
      (FreeMonoid (CoprodI (LineDoubleFactor G) ⊕ ↥Γ)) :=
    List.countable
  haveI h3 : Countable (Coprod (CoprodI (LineDoubleFactor G)) ↥Γ) :=
    Con.mk'_surjective.countable
  exact Con.mk'_surjective.countable

/-! ## The symmetric double is a retract of the line double -/

/-- The two chosen adjacent line vertices. -/
def doubleLineIndex : Bool → ℤ
  | false => 0
  | true => 1

/-- Send the two factors of the symmetric double to vertices `0` and `1`. -/
def doubleToLineMaps : ∀ b, DoubleFactor G b →* LineDouble G Γ :=
  fun b ↦ inLineDouble G Γ (doubleLineIndex b)

theorem doubleToLineMaps_comp :
    ∀ b, (doubleToLineMaps G Γ b).comp (doubleMap G Γ b) =
      PushoutI.base (lineDoubleMap G Γ) :=
  fun b ↦ PushoutI.of_comp_eq_base (doubleLineIndex b)

/-- The canonical homomorphism from the symmetric double into the line
double. -/
def doubleToLine : SymmetricDouble G Γ →* LineDouble G Γ :=
  PushoutI.lift (doubleToLineMaps G Γ)
    (PushoutI.base (lineDoubleMap G Γ)) (doubleToLineMaps_comp G Γ)

@[simp] theorem doubleToLine_inDouble (b : Bool) (g : G) :
    doubleToLine G Γ (inDouble G Γ b g) =
      inLineDouble G Γ (doubleLineIndex b) g := by
  exact PushoutI.lift_of _ _ _ _

/-- Collapse vertex `0` to the first factor and every other line vertex to
the second factor. -/
def lineToDoubleMaps : ∀ i : ℤ, LineDoubleFactor G i →* SymmetricDouble G Γ :=
  fun i ↦ if i = 0 then inDouble G Γ false else inDouble G Γ true

theorem lineToDoubleMaps_comp :
    ∀ i, (lineToDoubleMaps G Γ i).comp (lineDoubleMap G Γ i) =
      PushoutI.base (doubleMap G Γ) := by
  intro i
  by_cases hi : i = 0
  · simpa [lineToDoubleMaps, lineDoubleMap, inDouble, doubleMap, hi] using
      (PushoutI.of_comp_eq_base (φ := doubleMap G Γ) false)
  · simpa [lineToDoubleMaps, lineDoubleMap, inDouble, doubleMap, hi] using
      (PushoutI.of_comp_eq_base (φ := doubleMap G Γ) true)

/-- The retraction from the line double onto the selected symmetric double. -/
def lineToDouble : LineDouble G Γ →* SymmetricDouble G Γ :=
  PushoutI.lift (lineToDoubleMaps G Γ)
    (PushoutI.base (doubleMap G Γ)) (lineToDoubleMaps_comp G Γ)

@[simp] theorem lineToDouble_inLineDouble (i : ℤ) (g : G) :
    lineToDouble G Γ (inLineDouble G Γ i g) =
      if i = 0 then inDouble G Γ false g else inDouble G Γ true g := by
  unfold lineToDouble inLineDouble
  rw [PushoutI.lift_of]
  by_cases hi : i = 0 <;> simp [lineToDoubleMaps, hi]

/-- The collapse is a left inverse to the inclusion of the two selected
vertices. -/
theorem lineToDouble_comp_doubleToLine :
    (lineToDouble G Γ).comp (doubleToLine G Γ) = MonoidHom.id _ := by
  apply PushoutI.hom_ext_nonempty
  intro b
  ext g
  change lineToDouble G Γ (doubleToLine G Γ (inDouble G Γ b g)) =
    inDouble G Γ b g
  rw [doubleToLine_inDouble, lineToDouble_inLineDouble]
  cases b <;> norm_num [doubleLineIndex]

/-- The symmetric double embeds in the infinite line double. -/
theorem doubleToLine_injective : Function.Injective (doubleToLine G Γ) :=
  Function.LeftInverse.injective fun x ↦
    DFunLike.congr_fun (lineToDouble_comp_doubleToLine G Γ) x

/-! ## Transfer of nonsoficity -/

/-- A nonsofic symmetric double forces the line double to be nonsofic because
soficity passes to subgroups. -/
theorem lineDouble_not_isSofic_of_symmetricDouble_not_isSofic
    (hD : ¬ IsSofic (SymmetricDouble G Γ)) :
    ¬ IsSofic (LineDouble G Γ) := by
  intro hline
  exact hD (isSofic_of_injective (doubleToLine G Γ)
    (doubleToLine_injective G Γ) hline)

end GroupApproximation
