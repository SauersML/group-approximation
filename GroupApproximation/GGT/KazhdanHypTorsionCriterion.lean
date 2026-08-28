import GroupApproximation.GGT.KazhdanHypQuadrangleBridge

/-!
# The torsion criterion for triangle tables, and why it needs no extra hypothesis

`GGT/KazhdanHypTable.lean` states torsion-freeness of a checked table as
`TableTorsionFree extra`, carrying an unspecified extra condition on the table,
and its docstring explains the choice like this: Kangaslampi and Vdovina
classify the one-vertex triangle tables whose link is `GQ(2,2)` and find `23`
torsion-free and `168` torsion groups with the same link, so "no condition on
the link alone separates them"; and the obvious candidate --- no relator a
proper power, that is, not all three letters of a triangle equal --- is
dismissed there as vacuous, because such a relator would make a link edge have
multiplicity three.

**That dismissal is the wrong conclusion, and the criterion it dismisses is the
right one.**  Carbone, Kangaslampi and Vdovina, *Groups acting simply
transitively on hyperbolic buildings* (arXiv:1107.3690), say in §2, just before
their Theorem 2.4, that the earlier classification listed the presentations
over the smallest thick generalized quadrangle "when at least two labels in
each triangle are different", and that this "corresponds to the case of torsion
free groups acting simply transitively on the building"; their Theorem 2.5 then
counts the presentations that are *not* of that form and gets the `168` groups
with torsion.  So the separating condition is exactly

```
    no triangle has all three of its letters equal ,
```

which is `TableChecks`' fifth clause, already present and already checked.

The two accounts are reconciled by the two ways of counting a link edge.
Vdovina's polygonal presentations impose a *set* condition --- an ordered pair
of letters is completed to a triangle by at most one third letter --- which the
triple `(x,x,x)` satisfies.  `TriangularHodgeLayer.directedAdjacencyCount`
counts *corners*, and `(x,x,x)` has three corners carrying the same ordered
pair, so it fails the simplicity clause.  Both statements are correct; what
does not follow is that the criterion is vacuous.  It is not vacuous, it is
*implied*: `no_cube_of_linkSimple` derives it from simplicity alone, by
`corner_unique_of_linkSimple`.

## What this module proves

* `no_cube_of_linkSimple`, `TableChecks.noCube` --- a checked table has no
  triangle with three equal letters, so it satisfies the
  Kangaslampi--Vdovina criterion.
* `cornerValue_cube_eq_one`, `cornerValue_eq_one_of_torsionFree` --- the
  converse direction, machine-checked: a triangle with three equal letters is a
  cube relator, so a torsion-free table group kills that letter.  This is why
  the criterion is the right shape: violating it produces the torsion.
* `CheckedTableTorsionFree` --- torsion-freeness of a checked table with **no
  extra hypothesis**, and `tableTorsionFree_of_checkedTableTorsionFree`
  deriving the parametrised form from it.
* `sharpExistence_of_checkedTable_noExtra` --- the route's assembly with the
  extra condition gone: what remains is hyperbolicity, infiniteness,
  torsion-freeness, and a table.

## What it does not prove

Torsion-freeness itself.  The criterion is necessary and, by the cited
classification, sufficient over `GQ(2,2)`; the proof that it is sufficient runs
through the simply transitive action on the building, which is the geometry
this repository does not have.  `CheckedTableTorsionFree` is therefore a
statement and not a theorem here --- but it is now a statement with no
undetermined parameter in it.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GroupApproximation
namespace KazhdanHyp

section Criterion

variable {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-! ## The criterion is implied by simplicity of the link -/

/-- **A simple link forbids a triangle with three equal letters.**  Two of its
three corners would carry the same ordered pair of consecutive letters, and
`corner_unique_of_linkSimple` says distinct corners cannot do that. -/
theorem no_cube_of_linkSimple
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hsimple : ∀ u v, TriangularHodgeLayer.adjacencyCount T u v ≤ 1)
    (j : TriangleIndex) : ¬ (T j 0 = T j 1 ∧ T j 1 = T j 2) := by
  rintro ⟨h01, h12⟩
  have hnext0 : TriangularHodgeLayer.nextCorner (0 : Fin 3) = 1 := by decide
  have hnext1 : TriangularHodgeLayer.nextCorner (1 : Fin 3) = 2 := by decide
  have h2 : T ((j, (0 : Fin 3)) : TriangleIndex × Fin 3).1
        (TriangularHodgeLayer.nextCorner ((j, (0 : Fin 3)) : TriangleIndex × Fin 3).2)
      = T ((j, (1 : Fin 3)) : TriangleIndex × Fin 3).1
        (TriangularHodgeLayer.nextCorner ((j, (1 : Fin 3)) : TriangleIndex × Fin 3).2) := by
    show T j (TriangularHodgeLayer.nextCorner (0 : Fin 3))
        = T j (TriangularHodgeLayer.nextCorner (1 : Fin 3))
    rw [hnext0, hnext1]
    exact h12
  have h1 : T ((j, (0 : Fin 3)) : TriangleIndex × Fin 3).1
        ((j, (0 : Fin 3)) : TriangleIndex × Fin 3).2
      = T ((j, (1 : Fin 3)) : TriangleIndex × Fin 3).1
        ((j, (1 : Fin 3)) : TriangleIndex × Fin 3).2 := h01
  have heq := corner_unique_of_linkSimple T hsimple h1 h2
  have hsnd : (0 : Fin 3) = 1 := congrArg Prod.snd heq
  exact absurd hsnd (by decide)

/-- **A checked table satisfies the Kangaslampi--Vdovina criterion.**  It is
the fifth clause of `TableChecks`, and it is also a consequence of the fourth:
`TableChecks.simple` alone gives it. -/
theorem TableChecks.noCube
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {q : ℕ}
    (h : TableChecks T q) (j : TriangleIndex) :
    ¬ (T j 0 = T j 1 ∧ T j 1 = T j 2) :=
  no_cube_of_linkSimple T h.simple j

/-! ## Violating the criterion produces the torsion -/

/-- **A triangle with three equal letters is a cube relator.**  The three
corner values of a triangle multiply to one, and here they are the same
element. -/
theorem cornerValue_cube_eq_one
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (j : TriangleIndex)
    (h01 : T j 0 = T j 1) (h12 : T j 1 = T j 2) :
    (TriangularHodgeLayer.cornerValue T j 0) ^ 3 = 1 := by
  have e1 : TriangularHodgeLayer.cornerValue T j 1
      = TriangularHodgeLayer.cornerValue T j 0 := by
    simp only [TriangularHodgeLayer.cornerValue, h01]
  have e2 : TriangularHodgeLayer.cornerValue T j 2
      = TriangularHodgeLayer.cornerValue T j 0 := by
    simp only [TriangularHodgeLayer.cornerValue, h01, h12]
  have h := TriangularHodgeLayer.cornerValue_mul_cornerValue_mul_cornerValue T j
  rw [e1, e2] at h
  have hthree : (3 : ℕ) = 2 + 1 := rfl
  rw [hthree, pow_succ, pow_two]
  exact h

/-- **The criterion is necessary.**  If a table has a triangle with three equal
letters and its group is torsion-free, that letter is trivial in the group ---
so a table violating the criterion cannot present a torsion-free group on a
nondegenerate alphabet. -/
theorem cornerValue_eq_one_of_torsionFree
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (j : TriangleIndex)
    (h01 : T j 0 = T j 1) (h12 : T j 1 = T j 2)
    (htf : IsPowerTorsionFree (TriangularHodgeLayer.Presented T)) :
    TriangularHodgeLayer.cornerValue T j 0 = 1 :=
  htf _ 3 (by norm_num) (cornerValue_cube_eq_one T j h01 h12)

end Criterion

/-! ## Torsion-freeness of a checked table, with no extra hypothesis -/

/-- **Torsion-freeness of a checked table.**  `TableTorsionFree` carries an
unspecified extra condition `extra` on the table; by the Carbone--Kangaslampi--
Vdovina classification the condition that separates the torsion-free tables
from the others is "no triangle has three equal letters", and `TableChecks.noCube`
says every checked table already satisfies it.  So the extra parameter can go,
and this is the statement that remains.

Not proved here: the sufficiency runs through the simply transitive action on
the building.  Nothing in this repository assumes it. -/
def CheckedTableTorsionFree : Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ),
    TableChecks T q → IsPowerTorsionFree (TriangularHodgeLayer.Presented T)

/-- The parametrised form follows from the extra-free one, at the trivial
extra condition: nothing is lost by dropping the parameter. -/
theorem tableTorsionFree_of_checkedTableTorsionFree (h : CheckedTableTorsionFree) :
    TableTorsionFree (fun _ _ _ => True) := by
  intro Generator TriangleIndex fg dg ng ft dt T q hchecks _
  exact h Generator TriangleIndex fg dg ng ft dt T q hchecks

/-- **`SharpExistence` from a checked table, with the extra condition gone.**
Three hypotheses and one table: hyperbolicity, infiniteness and
torsion-freeness of a `C(3)`-`T(8)` table group.  The spectral bridge was
discharged in `GGT/KazhdanHypQuadrangleBridge.lean` and the extra table
condition is discharged here. -/
theorem sharpExistence_of_checkedTable_noExtra
    (hhyp : CThreeTEightHyperbolicity)
    (hinf : CThreeTEightInfinite)
    (htf : CheckedTableTorsionFree)
    {Generator TriangleIndex : Type} [fg : Fintype Generator]
    [dg : DecidableEq Generator] [ng : Nonempty Generator]
    [ft : Fintype TriangleIndex] [dt : DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ)
    (h : TableChecks T q) :
    Hyperbolic.SharpExistence :=
  ⟨TriangularHodgeLayer.Presented T, inferInstance,
    hinf Generator TriangleIndex fg dg ng ft dt T q h, inferInstance,
    htf Generator TriangleIndex fg dg ng ft dt T q h,
    hhyp Generator TriangleIndex fg dg ng ft dt T q h,
    hasKazhdanPropertyT_of_checkedTable T q h⟩

end KazhdanHyp
end GroupApproximation
