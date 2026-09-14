---
rg: 2
id: rado-type-a-action-from-v-tuple-sort
kind: route
title: A V-invariant Rado graph on a clopen tuple sort makes V a type (A) actor on the Rado graph
target: some-fp-group-acts-on-the-rado-graph-with-type-a
requires:
  - some-v-invariant-graph-on-clopen-tuples-is-rado
  - fp-full-binary-cantor-groups-have-type-a-actions
artifacts:
  - research/artifacts/hl-bh-fraisse-thompson-2026-09-14.md
---

Let `Γ` be a `V`-invariant graph on a tuple sort `X_P` with `Γ ≅ R`. Then `V` acts on the
vertices of `R` by automorphisms. The four type (A) conditions hold.

1. **Finitely presented.** `V` is finitely presented.
2. **Faithful.**
   - In the pattern `P` the first coordinate is nonempty and proper. Since the Boolean algebra
     of clopen sets is atomless, every nonempty proper clopen `U` occurs as the first coordinate
     of some tuple in `X_P`.
   - So an element fixing every tuple fixes every clopen set setwise, hence is the identity, as
     in `fp-full-binary-cantor-groups-have-type-a-actions`.
3. **Finitely generated stabilizers.** The stabilizer of a tuple is the stabilizer of a finite
   family of clopen sets, each fixed setwise. By `fp-full-binary-cantor-groups-have-type-a-actions`
   (applied to `D = V`), such stabilizers are finitely presented.
4. **Finitely many orbits on two-element subsets.** An unordered pair of tuples is a `2k`-tuple
   up to swapping the halves. `V`-orbits of `2k`-tuples are classified by nonempty atom patterns,
   of which there are finitely many.

So the action is of type (A) and it preserves `Γ ≅ R`.
