import GroupApproximation.Domination.Core
import GroupApproximation.Sofic.FiniteActionCharacter

/-!
# Finite-permutation domination

This file instantiates `PowerDefectSystem` with exact actions on nonempty
finite sets.  The normalized permutation character is the fixed-point
fraction `θ`, and the phase-compatible defect used for comparison with
unitary characters is

`q(g) = 1 - θ(g)²`.

Cartesian powers of actions are standard in sofic approximation.  Their
fixed-point fractions multiply, giving the same Bernoulli power law as tensor
powers of unitary characters.  The general power-linearization theorem then
identifies qualitative finite-action collapse with one global linear
permutation-character inequality.

The ordinary moved-point fraction `1-θ` differs from `q` by a factor in
`[1,2]`; thus this normalization preserves the established finite-action
radical criterion while putting the permutation and matrix constants in the
same units.
-/

namespace GroupApproximation

variable (G : Type*) [Group G]

/-- An exact action of a group on a nonempty finite set. -/
structure FinitePermutationRepresentation where
  carrier : FiniteModel
  nonempty : 0 < Fintype.card carrier
  map : G → Equiv.Perm carrier
  map_one : map 1 = 1
  map_mul : ∀ g h, map (g * h) = map g * map h

namespace FinitePermutationRepresentation

variable {G : Type*} [Group G]

/-- The bundled homomorphism underlying an exact finite action. -/
def toMonoidHom (ρ : FinitePermutationRepresentation G) :
    G →* Equiv.Perm ρ.carrier where
  toFun := ρ.map
  map_one' := ρ.map_one
  map_mul' := ρ.map_mul

@[simp] theorem toMonoidHom_apply
    (ρ : FinitePermutationRepresentation G) (g : G) :
    ρ.toMonoidHom g = ρ.map g := rfl

/-- Normalized finite-action character: the fixed-point fraction. -/
noncomputable def character (ρ : FinitePermutationRepresentation G) (g : G) : ℝ :=
  fixedPointFraction ρ.carrier (ρ.map g)

/-- The ordinary normalized Hamming displacement from the identity. -/
noncomputable def movedDefect (ρ : FinitePermutationRepresentation G) (g : G) : ℝ :=
  1 - ρ.character g

/-- Squared-character defect, in the same normalization as the unitary
domination problem. -/
noncomputable def characterDefect
    (ρ : FinitePermutationRepresentation G) (g : G) : ℝ :=
  1 - (ρ.character g) ^ 2

theorem character_eq_one_sub_hammingDistance
    (ρ : FinitePermutationRepresentation G) (g : G) :
    ρ.character g = 1 - hammingDistance ρ.carrier (ρ.map g) 1 := by
  have h := hammingDistance_one_eq_one_sub_fixedPointFraction
    ρ.carrier (ρ.map g) ρ.nonempty
  unfold character
  linarith

theorem character_nonneg (ρ : FinitePermutationRepresentation G) (g : G) :
    0 ≤ ρ.character g := by
  rw [character_eq_one_sub_hammingDistance]
  linarith [hammingDistance_le_one ρ.carrier (ρ.map g) 1]

theorem character_le_one (ρ : FinitePermutationRepresentation G) (g : G) :
    ρ.character g ≤ 1 := by
  rw [character_eq_one_sub_hammingDistance]
  linarith [hammingDistance_nonnegative ρ.carrier (ρ.map g) 1]

theorem characterDefect_nonneg
    (ρ : FinitePermutationRepresentation G) (g : G) :
    0 ≤ ρ.characterDefect g := by
  unfold characterDefect
  have h0 := ρ.character_nonneg g
  have h1 := ρ.character_le_one g
  nlinarith

theorem characterDefect_le_one
    (ρ : FinitePermutationRepresentation G) (g : G) :
    ρ.characterDefect g ≤ 1 := by
  unfold characterDefect
  nlinarith [sq_nonneg (ρ.character g)]

theorem movedDefect_le_characterDefect
    (ρ : FinitePermutationRepresentation G) (g : G) :
    ρ.movedDefect g ≤ ρ.characterDefect g := by
  unfold movedDefect characterDefect
  have h0 := ρ.character_nonneg g
  have h1 := ρ.character_le_one g
  nlinarith

theorem characterDefect_le_two_movedDefect
    (ρ : FinitePermutationRepresentation G) (g : G) :
    ρ.characterDefect g ≤ 2 * ρ.movedDefect g := by
  unfold movedDefect characterDefect
  have h0 := ρ.character_nonneg g
  have h1 := ρ.character_le_one g
  nlinarith

theorem powerPerm_one (Y : Type*) (m : ℕ) :
    powerPerm m (1 : Equiv.Perm Y) = 1 := by
  ext f i
  rfl

/-- Cartesian power of a finite action. -/
noncomputable def power (ρ : FinitePermutationRepresentation G) (m : ℕ) :
    FinitePermutationRepresentation G where
  carrier := powerModel ρ.carrier m
  nonempty := by
    rw [card_powerModel]
    exact pow_pos ρ.nonempty m
  map := fun g ↦ powerPerm m (ρ.map g)
  map_one := by
    rw [ρ.map_one, powerPerm_one]
    rfl
  map_mul := by
    intro g h
    rw [ρ.map_mul, powerPerm_mul]
    rfl

/-- Fixed-point fractions multiply under Cartesian powers. -/
theorem character_power (ρ : FinitePermutationRepresentation G)
    (m : ℕ) (g : G) :
    (ρ.power m).character g = (ρ.character g) ^ m := by
  letI : Fintype (Fin m → ρ.carrier) := (ρ.power m).carrier.fintype
  letI : DecidableEq (Fin m → ρ.carrier) := (ρ.power m).carrier.decidableEq
  have hp1 : powerPerm m (1 : Equiv.Perm ρ.carrier) = 1 :=
    powerPerm_one ρ.carrier m
  have hpower := hammingDistance_powerPerm ρ.carrier m ρ.nonempty
    (ρ.map g) 1
  rw [hp1] at hpower
  have hpower' :
      hammingDistance (ρ.power m).carrier ((ρ.power m).map g) 1 =
        1 - (1 - hammingDistance ρ.carrier (ρ.map g) 1) ^ m := by
    change hammingDistance (powerModel ρ.carrier m)
      (powerPerm m (ρ.map g)) 1 =
        1 - (1 - hammingDistance ρ.carrier (ρ.map g) 1) ^ m
    exact hpower
  have hup := (ρ.power m).character_eq_one_sub_hammingDistance g
  have hdown := ρ.character_eq_one_sub_hammingDistance g
  calc
    (ρ.power m).character g =
        1 - hammingDistance (ρ.power m).carrier ((ρ.power m).map g) 1 := hup
    _ = (1 - hammingDistance ρ.carrier (ρ.map g) 1) ^ m := by
      rw [hpower']
      ring
    _ = (ρ.character g) ^ m := by rw [hdown]

/-- Exact Bernoulli law for squared permutation-character displacement. -/
theorem characterDefect_power (ρ : FinitePermutationRepresentation G)
    (m : ℕ) (g : G) :
    (ρ.power m).characterDefect g =
      1 - (1 - ρ.characterDefect g) ^ m := by
  unfold characterDefect
  rw [character_power]
  ring

end FinitePermutationRepresentation

/-- The power-defect system carried by exact finite permutation actions. -/
noncomputable def permutationPowerDefectSystem :
    PowerDefectSystem G (FinitePermutationRepresentation G) where
  defect := FinitePermutationRepresentation.characterDefect
  power := FinitePermutationRepresentation.power
  defect_nonneg := FinitePermutationRepresentation.characterDefect_nonneg
  defect_le_one := FinitePermutationRepresentation.characterDefect_le_one
  defect_power := FinitePermutationRepresentation.characterDefect_power

/-- Qualitative finite-action character collapse for one marked word. -/
def PermutationCharacterVanishesAtZero (R : Finset G) (w : G) : Prop :=
  (permutationPowerDefectSystem G).VanishesAtZero R w

/-- Existence of one finite-permutation character domination constant. -/
def HasPermutationCharacterDomination (R : Finset G) (w : G) : Prop :=
  (permutationPowerDefectSystem G).HasLinearDomination R w

/-- **Finite-permutation domination equivalence.**  Qualitative collapse is
equivalent to one global linear inequality

`qρ(w) ≤ C * ∑ r ∈ R, qρ(r)`

over every nonempty exact finite action. -/
theorem permutationCharacterVanishesAtZero_iff_hasDomination
    (R : Finset G) (w : G) :
    PermutationCharacterVanishesAtZero G R w ↔
      HasPermutationCharacterDomination G R w :=
  (permutationPowerDefectSystem G).vanishesAtZero_iff_hasLinearDomination R w

end GroupApproximation
