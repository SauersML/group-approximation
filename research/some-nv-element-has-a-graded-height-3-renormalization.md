---
rg: 2
id: some-nv-element-has-a-graded-height-3-renormalization
kind: claim
title: Some element of some Brin–Thompson group nV has an invariant clopen set with a height-3 self-renormalization that cycles a clopen 3-colouring
distinct_from:
  smart-induced-map-has-brick-local-height-3-renormalization: that is an ungraded height-3 renormalization of SMART's induced map; this asks for a graded one, which SMART and all its finite decorations lack (`smart-renormalization-admits-no-graded-basins`).
  graded-renormalization-gives-ternary-toeplitz-factor: that proves the consequences (a ternary Toeplitz factor and a periodic subgroup of nV); this is the existence of the input.
---

**OPEN.** There are `n ≥ 2`, `g ∈ nV`, a `g`-invariant clopen `A ⊆ C^n`, clopen sets `D` and
`A = L_0 ⊔ L_1 ⊔ L_2`, and a homeomorphism `Ψ : A → D` satisfying (R1)–(R4) of
`graded-renormalization-gives-ternary-toeplitz-factor`.

By that node, a positive answer puts Nekrashevych's ternary fragmentation, an infinite finitely generated
periodic group, inside `nV`. That separates `nV` from `V`, which is torsion locally finite (Röver).

## What any witness must do

- By Lemma A there, the odometer factor of `(A, g)` must be non-open at every hole point.
- By `smart-renormalization-admits-no-graded-basins`, no finite skew product of SMART's induced map works
  through its landed renormalization.
- `Ψ` need not be brick-local or lie in `nV`. Only `g` must be an element of `nV`.

## Attempts

1. **Attempt 1 (2026-09-18, bh-free-01).**
   - SMART and its register decorations fail, as above.
   - Idea not carried out: a two-counter design in which a second, 3-adic counter records carry lengths.
     This gives an odometer (no fixed points) on the long-carry locus. But that counter's own carries need
     the same treatment, so the construction regresses.
   - A SMART-like recursive machine whose zero-block recursion carries a period-3 grading is the natural
     next design.
   - Handed to lane bh-free-50, which owns `nV` torsion from 2026-09-18.
