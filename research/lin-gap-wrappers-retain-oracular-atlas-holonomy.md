---
rg: 2
id: lin-gap-wrappers-retain-oracular-atlas-holonomy
kind: claim
title: Lin's synchronous gap wrappers retain the same oracular projection-atlas holonomy
distinct_from:
  oracularizable-tracial-nonru-game-exists: that constructs one finite incidence-oracularizable source from a BCS; this audits Lin's static-gap promise and identifies the exact common projection diagram whenever its preserved perfect strategy is oracularizable.
  three-label-affine-lowering-no-go: that destroys a black-box affine-support lowering while preserving a source gap; this treats signed-Hecke and central-character groupification and the concrete anchoring/repetition wrappers.
  finite-sheet-transport-networks-are-exactly-matricial: that classifies an already chosen sheet network; this derives the network and its shared marginals directly from an oracular synchronous game.
---

Lin, arXiv:2510.07162v1, Theorem 6.15 is an RE-completeness theorem for the
`1/2` Bell-separation **promise problem**.  It does not single out one
canonical presentation with an answer-transitive symmetry.  Its no-instances
are guaranteed to be finite synchronous twelfth-level conditionally-linear
samplable games with

```text
omega_co(G)=1,                 omega_*(G)<=1/2.            (LSH1)
```

The syntactic guarantees are synchrony, one common answer alphabet, and a
conditionally-linear **question sampler**.  Theorem 6.15 does not state that
the output is a graph-homomorphism or imitation game, and the PCP decider is
allowed to distinguish arbitrary answer strings.  Thus neither answer
transitivity nor a finite homogeneous inclusion diagram follows from the
theorem.

There is nevertheless an exact projection diagram when the perfect strategy
is the oracularizable strategy preserved by Lin's compression pipeline.  Let
`P_x^a` be its one-player PVMs.  For each sampled pair `e=(x,y)`, put

```text
R_e={(a,b):D(x,y,a,b)=1},
p_(e,a,b)=P_x^a P_y^b,              (a,b) in R_e.          (LSH2)
```

Oracularizability says the two PVMs commute.  Perfectness kills every losing
product.  Consequently the `p_(e,a,b)` are an allowed-pair PVM and

```text
sum_b p_(e,a,b)=P_x^a,       sum_a p_(e,a,b)=P_y^b.        (LSH3)
```

Conversely, compatible edge PVMs satisfying `(LSH3)` recover a perfect
oracularizable strategy.  Therefore groupifying this special source is
exactly a multi-answer compatible projection atlas: local allowed-pair
blocks are finite, and the only global equations are equality of the same
question marginal across all incident edge contexts.

The visible wrappers do not remove that equality problem.

1. **Synchrony and balance.** Synchrony supplies the shared names in
   `(LSH3)`.  Balance changes the weights of tests and is used for analytic
   rounding; it adds no algebraic relation among the projections.
2. **Conditional linearity.** The linearity is in the random seed-to-question
   map.  It gives no affine law for the answer PVMs.  Answer reduction uses a
   general PCPP decider and low-degree consistency tests, not a fixed affine
   predicate on the answer labels.
3. **Anchoring.** The anchor question has one deterministic answer in every
   perfect strategy.  The old sampled-pair diagram remains a subdiagram, and
   the new anchor contexts are deterministic leaves.  Restriction therefore
   recovers the old holonomy unchanged.
4. **Parallel repetition.** Fixing `r-1` question coordinates to the anchor
   and their answers to the deterministic anchor answer recovers one copy of
   the previous diagram.  Coordinate permutations are external finite game
   automorphisms; the game relations do not supply internal conjugating
   words implementing them.
5. **Pauli/low-degree tests.** Their finite local character packets are useful
   local signed-Hecke blocks, but the global PCP consistency is precisely the
   repeated marginal equality `(LSH3)`.  The finite-dimensional gap cannot be
   contained in a finite packet or a coherent finite sheet transport, since
   either would give a perfect finite-dimensional strategy.

It follows that the generic signed-Hecke holonomy obstruction applies
verbatim to the potentially helpful oracular form of Lin's source.  A finite
central-character packet can realize every local `R_e`, and uniform answer
padding can equalize their sizes, but coherifying all occurrences of
`P_x^a` would be a forbidden finite-dimensional perfect strategy.  Retaining
the edge transports gives only covariance and an exact finite monomial
model.  A successful source-specific compiler must still introduce a
nontransport, block-escaping chord in an infinite group-algebra corner.

This result does not rule out exploiting the full Pauli-PCP incidence by a
new nontransport relation.  It rules out the claimed shortcut from the
properties actually furnished by Theorem 6.15: synchrony, uniform answer
syntax, conditional-linear sampling, anchoring, parallel-coordinate
symmetry, or oracular joint contexts do not themselves close the group
compiler.
