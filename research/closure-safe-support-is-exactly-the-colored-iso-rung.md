---
rg: 2
id: closure-safe-support-is-exactly-the-colored-iso-rung
kind: claim
title: A bisynchronous qc/qa gap with linking-closed perfect support is exactly a colored-digraph isomorphism gap, and gives a non-embeddable quantum automorphism group
artifacts:
  - research/artifacts/ex-nh-mipstar-quantum-symmetry-rung-2026-09-12.md
distinct_from:
  locally-affine-support-bcs-is-exactly-the-lcs-boundary: that decides which non-CE constraint traces survive passage to a linear system, through the affine hull of each context support; this decides which non-CE bisynchronous traces survive passage to a colored isomorphism game, through the linking closure of the pair support.
  qc-qa-graph-gap-gives-non-ce-quantum-automorphism-group: that treats plain graphs and uses connectivity and complements; this treats colored digraphs, adds a cross colour instead, and characterizes the games that feed the rung.
  harris-bisynchronous-game-algebra-preservation: that converts any synchronous game into a bisynchronous game with the same algebra; this asks when the perfect trace of a bisynchronous game is carried by an isomorphism game.
---

**ESTABLISHED** by `closure-safe-support-is-exactly-the-colored-iso-rung-proof`.
It has not been reviewed by an ex-verify lane.

**Definitions.**

- **Colored digraph.**  A finite set `V_X` with a colouring
  `c_X: V_X x V_X -> C`, whose diagonal colours `c_X(x,x)` are never
  off-diagonal colours.
- **Isomorphism algebra.**  `A(Iso(X,Y))` is the universal unital *-algebra of
  a magic unitary `V=(v_(xa))` with `v_(xa) v_(x'a') = 0` whenever
  `c_X(x,x') != c_Y(a,a')`.
  - `X ≅_qc Y` means that it has a tracial state.
  - `X ≅_qa Y` means that it has a unital *-homomorphism into `R^U`.
- **Bisynchronous game.**  A synchronous game `H=(I,O,lambda)` with
  `|I| = |O|` and `lambda(i,i',j,j) = 0` for `i != i'`.
- **Support graph.**  For a tracial state `tau` on `A(H)`, `S_tau` is the
  bipartite graph on `(I x I)` and `(O x O)` joining `(i,i')` to `(j,j')` when
  `tau(e_(ij) e_(i'j')) > 0`.
- **Closure-safe.**  `tau` is closure-safe when every connected component of
  `S_tau` satisfies `lambda(i,i',j,j') = 1` for all question pairs `(i,i')`
  and answer pairs `(j,j')` in it.

**Theorem.**  The following are equivalent.

- **(CS1)** There is a bisynchronous game `H` with a closure-safe tracial state
  and no unital *-homomorphism `A(H) -> R^U`.
- **(CS2)** There are colored digraphs `X, Y` with `X ≅_qc Y` and `X` not
  `qa`-isomorphic to `Y`.

Moreover, (CS2) gives a colored digraph `Z` whose quantum automorphism group
has non-Connes-embeddable Haar von Neumann algebra.  Take `Z = X ⊔ Y`, keep the
colours of `X` and of `Y`, and give a new cross colour to the pairs between
the parts.

**Why this is the right boundary.**  Closure safety plays the role that affine
safety plays for linear systems.  A colour is forced to be constant on each
linked component of the perfect support.

**Independent-set sources.**  An independent-set game has rule
`lambda(i,i',v,v') = [v != v', v not adjacent to v']` for `i != i'`, which does
not depend on the question pair.  So every perfect tracial state of such a game
is closure-safe.  These games are not square, however: `t` questions and `|V|`
answers.  For the independent-set sources of
`perfect-qc-separation-yields-finite-bcs-with-no-matrix-model`, the rung
therefore fails at squareness, not at support.  Completing a quantum injection
`[t] -> V` to a quantum bijection is the step where independent set
(NP-complete) and graph isomorphism (quasipolynomial) separate classically.

Plain graphs are the case of three colours (equal, adjacent, non-adjacent).
A reduction from colored digraphs to plain graphs that preserves both `qc` and
`qa` is not claimed here.
