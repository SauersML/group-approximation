import GroupApproximation.Domination.Core
import GroupApproximation.Sofic.HyperlinearScalar

/-!
# Finite-dimensional unitary domination

This file instantiates `PowerDefectSystem` with honest finite-dimensional
unitary representations.  For a normalized character `χπ`, the defect is

`qπ(g) = 1 - |χπ(g)|²`.

Tensor powers give the exact law `q(π^[m],g)=1-(1-q(π,g))^m`.  Consequently
the abstract power-linearization theorem proves that qualitative collapse of
a marked word along a finite relator set is equivalent to a global linear
finite-dimensional character inequality.

The phase-removal construction `π ↦ π ⊗ conjugate(π)` is the standard
conjugate-doubling device.  We record its exact character formula and the
factor-two comparison needed to restrict the domination problem to real
nonnegative characters.  This separates the new domination formulation from
the established background: tensor amplification and conjugate doubling are
classical; their use here identifies the scalar constant attached to one
finite presentation and one marked word.
-/

namespace GroupApproximation

open Matrix

variable (G : Type*) [Group G]

/-- An exact finite-dimensional unitary representation with its nonempty
matrix index bundled so normalized trace is always defined on a positive
dimension. -/
structure FDUnitaryRepresentation where
  carrier : FiniteModel
  nonempty : 0 < Fintype.card carrier
  map : G → Matrix carrier carrier ℂ
  map_one : map 1 = 1
  map_mul : ∀ g h, map (g * h) = map g * map h
  isUnitary : ∀ g, map g ∈ Matrix.unitaryGroup carrier ℂ

namespace FDUnitaryRepresentation

variable {G : Type*} [Group G]

/-- The bundled exact multiplicative map underlying the representation. -/
noncomputable def toMonoidHom (π : FDUnitaryRepresentation G) :
    G →* Matrix π.carrier π.carrier ℂ where
  toFun := π.map
  map_one' := π.map_one
  map_mul' := π.map_mul

@[simp] theorem toMonoidHom_apply (π : FDUnitaryRepresentation G) (g : G) :
    π.toMonoidHom g = π.map g := rfl

/-- The same representation bundled with codomain the unitary group. -/
noncomputable def toUnitaryHom (π : FDUnitaryRepresentation G) :
    G →* Matrix.unitaryGroup π.carrier ℂ where
  toFun := fun g ↦ ⟨π.map g, π.isUnitary g⟩
  map_one' := by
    apply Subtype.ext
    exact π.map_one
  map_mul' := by
    intro g h
    apply Subtype.ext
    exact π.map_mul g h

@[simp] theorem toUnitaryHom_apply_coe
    (π : FDUnitaryRepresentation G) (g : G) :
    (π.toUnitaryHom g : Matrix π.carrier π.carrier ℂ) = π.map g := rfl

/-- Normalized character of an exact finite-dimensional unitary
representation. -/
noncomputable def character (π : FDUnitaryRepresentation G) (g : G) : ℂ :=
  normTrace π.carrier (π.map g)

/-- Phase-insensitive normalized-character displacement. -/
noncomputable def characterDefect (π : FDUnitaryRepresentation G) (g : G) : ℝ :=
  1 - Complex.normSq (π.character g)

theorem characterDefect_nonneg (π : FDUnitaryRepresentation G) (g : G) :
    0 ≤ π.characterDefect g := by
  unfold characterDefect character
  exact sub_nonneg.mpr
    (normSq_normTrace_le_one π.carrier (π.isUnitary g) π.nonempty)

theorem characterDefect_le_one (π : FDUnitaryRepresentation G) (g : G) :
    π.characterDefect g ≤ 1 := by
  unfold characterDefect
  linarith [Complex.normSq_nonneg (π.character g)]

/-- The `m`-fold tensor power of a finite-dimensional unitary
representation. -/
noncomputable def tensorPower (π : FDUnitaryRepresentation G) (m : ℕ) :
    FDUnitaryRepresentation G where
  carrier := tensorModel π.carrier m
  nonempty := by
    rw [card_tensorModel]
    exact pow_pos π.nonempty m
  map := fun g ↦ tensorPow (π.map g) m
  map_one := by rw [π.map_one, tensorPow_one]
  map_mul := by
    intro g h
    rw [π.map_mul, tensorPow_mul]
  isUnitary := fun g ↦ tensorPow_mem_unitaryGroup (π.isUnitary g) m

theorem character_tensorPower (π : FDUnitaryRepresentation G) (m : ℕ) (g : G) :
    (π.tensorPower m).character g = (π.character g) ^ m := by
  exact normTrace_tensorPow π.carrier (π.map g) m

theorem normSq_pow (z : ℂ) (m : ℕ) :
    Complex.normSq (z ^ m) = Complex.normSq z ^ m := by
  exact map_pow Complex.normSq z m

/-- Exact Bernoulli law for normalized-character displacement under tensor
powers. -/
theorem characterDefect_tensorPower (π : FDUnitaryRepresentation G)
    (m : ℕ) (g : G) :
    (π.tensorPower m).characterDefect g =
      1 - (1 - π.characterDefect g) ^ m := by
  unfold characterDefect
  rw [character_tensorPower, normSq_pow]
  ring

/-- The conjugate double `π ⊗ conjugate(π)`, which removes every scalar
phase from the normalized character. -/
noncomputable def conjugateDouble (π : FDUnitaryRepresentation G) :
    FDUnitaryRepresentation G where
  carrier := doubleModel π.carrier
  nonempty := by
    rw [card_doubleModel]
    exact Nat.mul_pos π.nonempty π.nonempty
  map := fun g ↦ conjDouble (π.map g)
  map_one := by rw [π.map_one, conjDouble_one]
  map_mul := by
    intro g h
    rw [π.map_mul, conjDouble_mul]
  isUnitary := fun g ↦ conjDouble_mem_unitaryGroup (π.isUnitary g)

/-- The conjugate-double character is the squared absolute value of the
original character, regarded as a nonnegative real complex number. -/
theorem character_conjugateDouble (π : FDUnitaryRepresentation G) (g : G) :
    π.conjugateDouble.character g =
      (Complex.normSq (π.character g) : ℂ) := by
  exact normTrace_conjDouble π.carrier (π.map g)

/-- Conjugate doubling changes `q` by a factor between one and two.  Hence
complex character phases cannot be responsible for finiteness or divergence
of a domination constant. -/
theorem characterDefect_le_conjugateDouble (π : FDUnitaryRepresentation G)
    (g : G) :
    π.characterDefect g ≤ π.conjugateDouble.characterDefect g := by
  let x : ℝ := Complex.normSq (π.character g)
  have hx0 : 0 ≤ x := Complex.normSq_nonneg _
  have hx1 : x ≤ 1 :=
    normSq_normTrace_le_one π.carrier (π.isUnitary g) π.nonempty
  change 1 - Complex.normSq (π.character g) ≤
    1 - Complex.normSq (π.conjugateDouble.character g)
  rw [character_conjugateDouble, Complex.normSq_ofReal]
  change 1 - x ≤ 1 - x * x
  nlinarith

theorem characterDefect_conjugateDouble_le_two
    (π : FDUnitaryRepresentation G) (g : G) :
    π.conjugateDouble.characterDefect g ≤ 2 * π.characterDefect g := by
  let x : ℝ := Complex.normSq (π.character g)
  have hx0 : 0 ≤ x := Complex.normSq_nonneg _
  have hx1 : x ≤ 1 :=
    normSq_normTrace_le_one π.carrier (π.isUnitary g) π.nonempty
  change 1 - Complex.normSq (π.conjugateDouble.character g) ≤
    2 * (1 - Complex.normSq (π.character g))
  rw [character_conjugateDouble, Complex.normSq_ofReal]
  change 1 - x * x ≤ 2 * (1 - x)
  nlinarith

end FDUnitaryRepresentation

/-- The power-defect system carried by all finite-dimensional unitary
representations of `G`. -/
noncomputable def fdUnitaryPowerDefectSystem :
    PowerDefectSystem G (FDUnitaryRepresentation G) where
  defect := FDUnitaryRepresentation.characterDefect
  power := FDUnitaryRepresentation.tensorPower
  defect_nonneg := FDUnitaryRepresentation.characterDefect_nonneg
  defect_le_one := FDUnitaryRepresentation.characterDefect_le_one
  defect_power := FDUnitaryRepresentation.characterDefect_tensorPower

/-- Qualitative finite-dimensional character collapse for one marked word. -/
def FDCharacterVanishesAtZero (R : Finset G) (w : G) : Prop :=
  (fdUnitaryPowerDefectSystem G).VanishesAtZero R w

/-- Existence of one finite-dimensional character domination constant. -/
def HasFDCharacterDomination (R : Finset G) (w : G) : Prop :=
  (fdUnitaryPowerDefectSystem G).HasLinearDomination R w

/-- **Finite-dimensional domination equivalence.**  Qualitative collapse is
equivalent to one global linear inequality

`qπ(w) ≤ C * ∑ r ∈ R, qπ(r)`

over all finite dimensions and all exact unitary representations. -/
theorem fdCharacterVanishesAtZero_iff_hasDomination
    (R : Finset G) (w : G) :
    FDCharacterVanishesAtZero G R w ↔ HasFDCharacterDomination G R w :=
  (fdUnitaryPowerDefectSystem G).vanishesAtZero_iff_hasLinearDomination R w

end GroupApproximation
