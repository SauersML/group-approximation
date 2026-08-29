import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Vanishing sequences and negligible densities

Every asymptotic statement in the manuscript has the shape `= o(|Y_n|)`.  This
file provides the single bookkeeping API used for all of them, in the explicit
epsilon--eventually form used throughout this development (no filters).

`Vanishing a` is `a n → 0`; `Negligible N e` records that the normalized
quantity `e n / N n` vanishes. `AsymptoticScale` bundles the divergence needed
to interpret that quotient as a density and is used at the main certificate
boundaries.
-/
