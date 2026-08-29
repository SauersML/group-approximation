import GroupApproximation.GroupTheory.PresentedGroupRelatorReplay

/-!
# The literal six-generator, thirteen-relator P13 presentation

This is the abstract presentation used by the exact degree-one Hodge
certificate.  Its order is part of the public data contract:

* generators `0,…,5` are `e12,e13,e21,e23,e31,e32`;
* relators `0,…,5` are the ordered Steinberg relations for
  `012,021,102,120,201,210`;
* relators `6,…,11` are the displayed commuting-root commutators
  `12_13,12_32,13_23,21_23,21_31,31_32`;
* relator `12` is `(e12 e21⁻¹ e12)⁴`.

No matrix model occurs in this module.  Equality in `P13` is only equality
modulo the thirteen displayed abstract relators.
-/

namespace GroupApproximation
namespace LiteralP13Presentation

open PresentedGroupRelatorReplay

noncomputable section

/-- The six elementary-root letters, in the exact certificate order. -/
abbrev P13Generator := Fin 6

/-- Literal signed words for the thirteen relators.  Keeping this data at the
list level lets the Fox identity be applied without re-parsing group
expressions. -/
def p13RelatorLetters : Fin 13 → SignedWord P13Generator
  | 0 => [(0, true), (3, true), (0, false), (3, false), (1, false)]
  | 1 => [(1, true), (5, true), (1, false), (5, false), (0, false)]
  | 2 => [(2, true), (1, true), (2, false), (1, false), (3, false)]
  | 3 => [(3, true), (4, true), (3, false), (4, false), (2, false)]
  | 4 => [(4, true), (0, true), (4, false), (0, false), (5, false)]
  | 5 => [(5, true), (2, true), (5, false), (2, false), (4, false)]
  | 6 => [(0, true), (1, true), (0, false), (1, false)]
  | 7 => [(0, true), (5, true), (0, false), (5, false)]
  | 8 => [(1, true), (3, true), (1, false), (3, false)]
  | 9 => [(2, true), (3, true), (2, false), (3, false)]
  | 10 => [(2, true), (4, true), (2, false), (4, false)]
  | 11 => [(4, true), (5, true), (4, false), (5, false)]
  | 12 =>
      [(0, true), (2, false), (0, true),
       (0, true), (2, false), (0, true),
       (0, true), (2, false), (0, true),
       (0, true), (2, false), (0, true)]

/-- The indexed relator interface used by proof-carrying certificate replay. -/
def p13Relator : Fin 13 → FreeGroup P13Generator
  | i => word (p13RelatorLetters i)

/-- Exactly the thirteen relators, with the indexed order above. -/
def p13Relators : Finset (FreeGroup P13Generator) :=
  Finset.univ.image p13Relator

@[simp] theorem p13Relator_mem (i : Fin 13) :
    p13Relator i ∈ p13Relators := by
  simp [p13Relators]

theorem mem_p13Relators_iff (r : FreeGroup P13Generator) :
    r ∈ p13Relators ↔ ∃ i : Fin 13, p13Relator i = r := by
  simp [p13Relators, eq_comm]

/-- The exact abstract group used by the rational Hodge certificate. -/
abbrev P13 : Type :=
  PresentedGroup (p13Relators : Set (FreeGroup P13Generator))

abbrev p13Word : FreeGroup P13Generator →* P13 :=
  PresentedGroup.mk (p13Relators : Set (FreeGroup P13Generator))

abbrev E12 : P13 := PresentedGroup.of 0
abbrev E13 : P13 := PresentedGroup.of 1
abbrev E21 : P13 := PresentedGroup.of 2
abbrev E23 : P13 := PresentedGroup.of 3
abbrev E31 : P13 := PresentedGroup.of 4
abbrev E32 : P13 := PresentedGroup.of 5

/-- The generator tuple in the exact certificate order. -/
def p13Generator : Fin 6 → P13 := PresentedGroup.of

/-- The six displayed letters generate the presented group. -/
theorem closure_range_p13Generator :
    Subgroup.closure (Set.range p13Generator) = ⊤ :=
  PresentedGroup.closure_range_of
    (p13Relators : Set (FreeGroup P13Generator))

end

end LiteralP13Presentation
end GroupApproximation
