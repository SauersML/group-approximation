---
rg: 2
id: effective-minimal-free-subshifts-via-tower-class-basis
kind: route
title: Non-effective minimal free subshift with computably bounded moduli, then a computable path in the resulting Pi01 tower class
target: decidable-fp-groups-have-effective-minimal-free-subshifts
requires:
  - tower-classes-are-computably-bounded-pi01-classes
  - free-minimal-subshifts-with-computable-moduli-exist
  - nonempty-tower-classes-yield-computable-towers
---

**Route. OPEN.** The route rests on three prerequisites.
- `tower-classes-are-computably-bounded-pi01-classes` is ESTABLISHED.
- `free-minimal-subshifts-with-computable-moduli-exist`, statement (N), is OPEN.
- `nonempty-tower-classes-yield-computable-towers`, path selection, is OPEN.

**Argument.** Let `Λ` be an infinite finitely presented group with solvable
word problem.
1. (N) gives a minimal free subshift on `Λ` whose modulus and freeness radius
   are computably bounded.
2. By part 4 of the first prerequisite, `T_D ≠ ∅` for a computable datum `D`.
3. Path selection gives a computable member of some `T_{D'}`.
4. By part 4 of the first prerequisite, `Λ` carries a nonempty effectively
   closed minimal free subshift. That is (M2).

**How it can fail.**
- *(N) fails for some `Λ`.* Then (M2) itself fails for `Λ`, since (M2) implies
  (N) by part 4. This is a pure-dynamics refutation target.
- *Path selection fails while (N) holds.* Then (M2) fails too, since the route
  is an equivalence given the first prerequisite. The failure is then of a
  computability-theoretic kind: the modulus bounds exist, but no computable
  tower realizes them.
- The two premises separate the dynamical content of (M2) from its effective
  content.
