import GroupApproximation.Sofic.LiteralBaseRotationRetract

/-!
# Finite relator replay for the literal rotation presentation

This module records explicit words used to compare the eight-relator rotation
presentation with standard integral presentations.  Every equality proved
here is internal to the presented group; no matrix equality is reflected back
through the canonical matrix quotient.
-/

namespace GroupApproximation
namespace LiteralBaseP13Replay

open LiteralBaseRotationRetract

noncomputable section

abbrev u : Rotation := Z
abbrev v : Rotation := X * Y

/-- Liversidge's explicit `u=z`, `v=xy` word for the generator `y`. -/
abbrev yFromUZXY : Rotation :=
  (u * v * u * v⁻¹ * u⁻¹ * v * u⁻¹ * v⁻¹ * u⁻¹ * v⁻¹ * u * v) ^ 2

example : yFromUZXY = Y := by
  simp [yFromUZXY, u, v, pow_succ]

end

end LiteralBaseP13Replay
end GroupApproximation
