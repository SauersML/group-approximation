import GroupApproximation.ThirdParty.FLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit
import GroupApproximation.Analysis.SequentialGroupColimit

/-!
# The tower colimit is a direct limit in the sense of the vendored `IsDirectLimit`

`Analysis/SequentialGroupColimit` builds the colimit `T.Colim` of a tower of groups by hand,
as the quotient of the disjoint union of the levels by eventual agreement, and proves only
the four facts `K_1` needs.  The vendored slice of the Fermat's Last Theorem repository
(`ThirdParty/FLT`, itself carrying Madison Crim's `FLT/Mathlib/Algebra/IsDirectLimit.lean`)
supplies the abstract predicate

    IsDirectLimit f g

on a directed system `f` with structure maps `g : M i → P`, together with its consequences:
`IsDirectLimit.lift`, `IsDirectLimit.lift_of`, the equivalence `IsDirectLimit.Equiv` between
any two direct limits of the same system, and the `Module` versions.

This file records that `T.Colim` with the level inclusions `T.iota n` is such a direct limit.
Nothing new is proved about the colimit: surjectivity is `GroupTower.exists_mk`, the
injectivity clause is `Quotient.exact` for the eventual-agreement setoid, and compatibility is
`GroupTower.mk_map`.  What it buys is the universal property, so that a homomorphism out of
`K_1(A) = colim_n U(M_n(A)) / U_0(M_n(A))` (see `Analysis/CStarKOne`) can be produced from a
compatible family on the levels through `IsDirectLimit.lift`, and two presentations of the
same colimit can be identified through `IsDirectLimit.Equiv`.

Not wired into the root import: it imports the vendored slice, which has not been compiled
against this repository's Mathlib pin.  See `ThirdParty/FLT/UPSTREAM.md`.
-/

namespace GroupApproximation

namespace GroupTower

universe u

variable {G : ℕ → Type u} [∀ n, Group (G n)] (T : GroupTower G)

/-- The transition maps of the tower as bare functions, indexed the way `DirectedSystem`
and `IsDirectLimit` index them. -/
def towerMap (n m : ℕ) (h : n ≤ m) : G n → G m := T.map h

/-- The level inclusions into the colimit as bare functions. -/
def towerIota (n : ℕ) : G n → T.Colim := T.iota n

@[simp] theorem towerMap_apply {n m : ℕ} (h : n ≤ m) (x : G n) :
    T.towerMap n m h x = T.map h x := rfl

@[simp] theorem towerIota_apply (n : ℕ) (x : G n) : T.towerIota n x = T.mk n x := rfl

/-- The transition maps form a directed system: `map_self` and `map_trans` of the tower. -/
instance directedSystem : DirectedSystem G T.towerMap where
  map_self x := T.map_self le_rfl x
  map_map hij hjk x := T.map_trans hij hjk x

/-- Two level elements have the same class in the colimit exactly when they agree at some
common later level. -/
theorem mk_eq_mk_iff {n m : ℕ} {x : G n} {y : G m} :
    T.mk n x = T.mk m y ↔ ∃ (k : ℕ) (hx : n ≤ k) (hy : m ≤ k), T.map hx x = T.map hy y :=
  ⟨fun h => Quotient.exact h, fun ⟨k, hx, hy, e⟩ => T.mk_eq_mk hx hy e⟩

/-- The tower colimit, with its level inclusions, is a direct limit of the tower. -/
instance isDirectLimit : IsDirectLimit T.towerMap T.towerIota where
  surj a := by
    obtain ⟨n, x, rfl⟩ := T.exists_mk a
    exact ⟨n, x, rfl⟩
  inj n m x y h := T.mk_eq_mk_iff.1 h
  compatibility n m h x := T.mk_map h x

end GroupTower

end GroupApproximation
