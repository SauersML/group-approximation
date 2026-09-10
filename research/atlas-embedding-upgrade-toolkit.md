---
rg: 2
id: atlas-embedding-upgrade-toolkit
kind: claim
title: Which group properties can be bolted onto an arbitrary group by embedding, and which cannot
---

Fix a property `P` that is **subgroup-closed** — soficity, hyperlinearity, MF,
LEF, LEA, amenability, the Haagerup property, linearity, torsion-freeness,
left-orderability, bi-orderability, local indicability, unique products, finite
cohomological dimension, being torsion, bounded exponent, local finiteness.
Failure of `P` then passes **upward**: if `H <= G` and `H` fails `P`, so does
`G`.

This splits the question "is there a group that fails `P` and has property `Q`?"
into two regimes, and the split is what governs which cells of the group
property atlas are cheap and which are research problems.

**Regime 1: `Q` is attainable by embedding.**  There is a construction taking an
arbitrary countable `H` to a group with property `Q` containing `H`.  Then the
cell is free the moment any `P`-failing group exists at all.  Known upgrades:

| `Q` | construction | cost |
|---|---|---|
| finitely generated (2-generated) | Higman--Neumann--Neumann embedding | none |
| simple | embed in a 2-generated simple group | none |
| acyclic | Baumslag--Dyer--Heller / Kan--Thurston | none |
| divisible | iterated adjunction of roots along amalgams | none |
| C\*-simple, unique trace, trivial amenable radical | free product with `F_2` (`free-product-with-f2-upgrade`) | none |
| nontrivial centre, nontrivial amenable radical | direct product with `Z` | none |
| not finitely generated | direct product with a countable direct sum of `Z` | none |
| not Hopfian, not co-Hopfian | countable direct sum of copies of `H`, shift down and shift up | none |
| contains `F_2`, exponential growth, not property (T) | free product with `F_2` | none |

**Regime 2: `Q` is itself subgroup-closed.**  Then no embedding can help: a
subgroup of a `Q`-group is a `Q`-group, so the `P`-failing subgroup would have
to have `Q` already.  The cell is equivalent to *constructing a new example*
that fails `P` and satisfies `Q` at the same time.  Every such cell is a
research problem, not a bookkeeping exercise.

The practical consequence for the atlas: for `P` = soficity, the cells
`!sofic + Q` with `Q` in {left-orderable, bi-orderable, locally indicable,
unique product, torsion, bounded exponent, Haagerup, finite cohomological
dimension, linear} are all in Regime 2 and all open, while `!sofic + Q` for `Q`
in {C\*-simple, acyclic, divisible, simple, not Hopfian, not finitely
generated} were all settled by Regime 1 moves off a single non-sofic input.

**A third regime worth naming.**  `Q` neither subgroup-closed nor known
attainable — type `F_infinity`, hyperbolicity, CAT(0), automaticity,
biautomaticity, decidable conjugacy problem, co-Hopfian.  These are not
excluded by the closure argument, but no upgrade construction is known either.
They are where a new embedding theorem would immediately pay off across many
cells at once: an "every finitely presented group embeds in a finitely
presented group of type `F_infinity`" statement, if true, would settle
`!sofic + finfty` and `!mf + finfty` for free.
