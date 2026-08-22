---
rg: 2
id: edgeful-or3-coefficient-link-compiler
kind: claim
title: Normalize the root skeleton and give every OR3 overlap term a private eliminable pivot
distinct_from:
  first-cycle-signed-hecke-chord: that asks for one arbitrary balanced BCS chord after a join-tree placement; this restricts to the explicit symmetric OR3 packet and specifies the remaining coefficient-link certificate.
  relative-c-sixth-pauli-incidence-labeling: that seeks long relative C-prime one-sixth contours for a growing Pauli occurrence family; this is a fixed ten-coordinate clause packet and targets triangular or C(4)-T(4) coefficient relations.
---

**OPEN.**  Start from a signed-3SAT BCS written with `R_edge` clauses and the
ten-coordinate packet of
`edgeful-or3-balanced-private-plane-packet`.  Construct a finite coherent
coefficient presentation with these properties.

1. Every clause context uses `(OBP4)`.  Thus its predicate, star,
   idempotence, and partition identities are exact before any overlap
   relator is added.
2. For every logical-variable occurrence, align the root-diagonal part of
   its sparse marginal with one common variable skeleton without imposing a
   new equality between nonidentical elements of the finite packet group.
3. Pair the one private off-diagonal plane with the common variable plane.
   After expanding its matrix unit in the finite packet group, all support
   equations for that plane must be consequences of one equation

   ```text
   h_(c,r) h_(c,s)^(-1)=z_v                              (OCL1)
   ```

   up to already valid packet conjugacies.  One of `h_(c,r),h_(c,s)` must be
   an occurrence-private pivot appearing in no other defining equation.
4. The pivots can then be Tietze-eliminated.  Equivalently, if a graphical
   presentation is retained, verify `C(4)-T(4)` on the actual coefficient
   link.  In either proof the finite packet embeds and its corner projection
   remains nonzero.
5. At least one common phase `z_v` remains outside the finite root group, so
   a genuine assignment projection in `(OBP4)` remains block-escaping after
   all overlaps close.

The local link audit is already complete.  A private endpoint word occurs in
only one shared marginal; choosing one equation per adjoint pair avoids the
inverse duplicate.  Context projection identities add no relators.  Hence a
relation satisfying `(OCL1)` has a unique source pivot and is directly
Tietze-safe; no `C(4)` theorem is needed for that relation.

The remaining obstruction is the **root skeleton/slot holonomy**.  The three
sparse marginal involutions have equal `5+5` ranks and are conjugate by the
finite symmetry of the packet, but they are not literally equal.  A clause
can place its three variables in three different slot types, while a global
variable can occur in different slots in different clauses.  Incidencewise
finite permutations align each sign separately, but their return around a
cycle is the original finite-sheet holonomy.  Pairing unmatched diagonal
packet terms would impose relations directly on the finite packet and has no
private pivot.  Also, one matrix unit has several finite-group support terms;
unless their matchings differ only by the same valid packet conjugacy, they
reuse the pivot in inconsistent equations rather than reduce to `(OCL1)`.

Thus the smallest live certificate is finite: choose the clause slot frames
and the packet-term bijections so every root-diagonal term matches literally
and every off-diagonal support family collapses to one private-pivot equation,
while some `z_v` survives.  External macro girth by itself does not provide
that certificate.

## Attempts

- **Occurrencewise slot permutations.**  For each incidence separately, a
  finite packet permutation carries the relevant `5+5` sign to the common
  variable skeleton.  Around a cycle the product of these permutations need
  not be trivial.  Correcting that return by equating unmatched diagonal
  packet coefficients imposes a relation inside the finite packet, where
  there is no private pivot to eliminate.
- **Pair every finite-support coefficient independently.**  The off-diagonal
  matrix unit expands into several packet terms.  Giving every term its own
  equation generally reuses the same endpoint phase in several equations;
  eliminating it leaves relations among packet terms.  This works only if a
  packet-term bijection proves that all equations are conjugates of the one
  pivot equation `(OCL1)`.
- **Raise the overlap girth.**  Equality subdivision preserves exact
  semantics and strict finite-dimensional soundness, but
  `overlap-subdivision-preserves-coherent-piece-obstruction` proves that it
  does not change this coefficient link.  It therefore cannot supply either
  the literal diagonal matching or the required `C(4)-T(4)` link condition.
- **Keep a retraction by sending every private pivot and common phase to
  one.**  This makes packet survival immediate, but
  `packet-retraction-evaluates-hecke-collision-atlas` applies that retraction
  coefficientwise to the `U(M_2(H))` collision blocks.  Any completed atlas
  then descends to the finite root packet, contradicting the strict source
  gap.  Thus the private-pivot equations cannot all be Tietze-safe in a way
  that retains the packet retraction.  A successful relative presentation
  must destroy that finite evaluation while proving packet injectivity by a
  genuine Freiheitssatz.

The attack is not deferred: the finite slot-frame and packet-term matching
problem in the preceding paragraph is the next explicit computation.
