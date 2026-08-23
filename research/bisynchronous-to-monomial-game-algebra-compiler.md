---
rg: 2
id: bisynchronous-to-monomial-game-algebra-compiler
kind: claim
title: Compile the fixed non-CE bisynchronous game into one finite-phase monomial matrix pair
distinct_from:
  perfect-completeness-constant-soundness-lcs-compiler: that compiles a machine family into linear-constraint games with quantitative soundness; this asks only for an exact algebraic encoding of one fixed bisynchronous non-CE game in finite-phase monomial-isomorphism syntax.
  bcs-to-lcs-exact-support-gap: that seeks an exact robust affine/LCS submenu inside a tracial BCS; this permits a general gain matrix pair and targets preservation of the whole game algebra up to a full corner.
  harris-circulant-one-matrix-compiler-forces-affine-support: that rules out the direct color encoding of Harris's canonical circulant completion; this open claim permits auxiliary incidence blocks and nontrivial full-corner encodings beyond that boundary.
  monomial-game-pair-compatibility-is-projective-color-rigid: that proves the identical-or-disjoint projective-color boundary for every direct one-matrix or common-phase multi-matrix encoding; this permits genuine auxiliary/full-corner gadgets beyond that boundary.
artifacts:
  - research/artifacts/harris-monomial-compiler-first-pass-2026-08-22.md
---

**OPEN.**  Let `G_H` be the equal-size bisynchronous game obtained by applying
`harris-bisynchronous-game-algebra-preservation` to the fixed synchronous
non-CE game.  Construct a finite `s` and finite matrices `A,B`, preferably
Butson or finite-gain matrices, such that the `s`-monomial quantum-isomorphism
algebra `A_s(A,B)` and `A(G_H)` are either

1. *-isomorphic; or
2. full-corner/Morita equivalent by explicit maps which preserve both
   nonzero tracial representations and nonzero homomorphisms into `R^omega`.

This would transfer the already known `qc=1>qa` separation without any new
finite-dimensional HS stability theorem.  The output must preserve the
particular non-CE game algebra, not merely map it onto a quotient which may
acquire unrelated `R^omega` representations.

## Attempts

- Harris supplies the square magic unitary exactly, but a general magic
  unitary relation is not visibly one matrix intertwining equation `uA=Bu`.
- Universality of graph-homomorphism games and known LCS-to-graph-isomorphism
  reductions show that rigid graph syntax can encode broad game classes, but
  they do not prove preservation by the finite-phase monomial linking algebra.
- Encoding each forbidden quadratic product by a private gain entry is the
  active finite gadget attack.  The unresolved check is that all auxiliary
  rows and columns form a full corner rather than enlarging the tracial state
  space.
- Directly taking Harris's block-circulant magic unitary as the fundamental
  matrix and encoding its pair supports by scalar source/target colors is
  closed by `harris-circulant-one-matrix-compiler-forces-affine-support`:
  the color relation is a bipartite Cayley graph, and color equality makes it
  a union of bicliques, forcing every supported answer relation to be an
  affine coset.  The fixed non-CE BCS has nonlinear predicate support.  Any
  surviving monomial compiler must therefore use genuine incidence
  auxiliaries, a phase-resolved full corner, or a non-circulant completion.
- More generally, `monomial-game-pair-compatibility-is-projective-color-rigid`
  shows that one or finitely many direct common-phase intertwiner equations
  still factor compatibility through a projective color partition.  Merely
  stacking weighted matrices does not supply the missing universality.
- `elementary-abelian-harris-lift-compiles-bcs-consistency` now handles all
  shared-variable consistency relations exactly: overlap agreement is
  equality of source and target difference labels.  The residual gadget is
  only local nonlinear predicate validity.  Without it, every globally
  consistent but predicate-violating assignment survives as a classical
  translation permutation.
- A naive incidence expansion which declares the pair entry to be
  `e_(a,x)e_(b,y)` is valid as a magic or monomial block only when those two
  projections commute, by
  `quadratic-pair-incidence-monomial-entry-forces-commutation`.  The
  oracular source safely permits the sampled commutators:
  `oracular-commutation-quotient-preserves-tracial-nonru` shows that their
  quotient retains the perfect trace and absence of `R^omega` models.  The
  remaining incidence problem is therefore narrower: realize the
  pair-dependent forbidden zero pattern by one finite matrix intertwiner
  without forcing nonsampled commutation or enlarging the tracial state
  space.
