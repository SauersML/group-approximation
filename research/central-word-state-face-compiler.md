---
rg: 2
id: central-word-state-face-compiler
kind: claim
title: Compile the fixed tracial non-RU BCS face into a phase-safe central-word clause face
distinct_from:
  phase-safe-toric-gap-game-exists: that asks only for the final game; this is the surviving state-dependent reversible route with the normal-quotient structure exposed
  bcs-projective-kernel-phase-compilation: that seeks a distinguished finite-gadget phase word in a tracial projective kernel; this permits any centralizable one-player word system and formulates soundness directly as separation of state faces
  perfect-lcs-gap-implies-nonhyperlinear: an LCS instance would satisfy this through its solution-group relations; this does not require the compiler output to have LCS syntax
---

**OPEN.**  Start with the fixed finite synchronous BCS whose algebra has a
tracial state but no `R^U` state.  Construct one finite torically determined
two-player game with phase group `B`, player groups `G_A,G_B`, and clause
words

```text
beta_i a_i b_i,
a_i in G_A,
b_i in G_B,
```

such that all three properties hold:

1. the full target universal group algebra has a tracial state fixing every
   clause and representing `B` by its faithful scalar character;
2. the entire target clause-character face is disjoint from the weak-star
   closure of finite-dimensional vector states, quantitatively by decoding a
   near-perfect finite target strategy to a forbidden near-perfect finite BCS
   strategy; and
3. the source nonlinear predicates are encoded after the forced
   centralizations of all `a_i,b_i`, rather than only on one selected finite
   packet type.

Property 1 certifies phase-safe normal closure.  Property 2 is exactly the
relative-FD criterion in `toric-gap-is-a-relative-fd-central-word-face`.
Property 3 is load-bearing: the exact normal quotient is a central quotient
of the two one-player centralization quotients, so a noncentral reversible
circuit that works only in an intended packet representation does not prove
the target theorem.

Local finite controlled-reflection gadgets remain possible, but finite-group
induction recreates forbidden selector types.  The missing actuator must
therefore be global/state-dependent or genuinely finite-dimensional-only.
The categorical finite-Morita obstruction, including matrix amplification
and full corners, is proved in
`finite-morita-toricization-cannot-encode-nonaffine-support`.

Two finite-packet shortcuts are now excluded before quantitative soundness.
`spherical-root-type-selection-is-phase-unsafe` shows that a transitive
`H/K` root can isolate the desired answer type on the cyclic vector, but its
moving inducing character kills the scalar phase under normal closure.
`extraspecial-spin-predicate-centralization-kills-phase` shows that a
noncentral Pauli predicate word, even behind a private conjugator, has a
commutator equal to the common phase and is therefore killed when the toric
clause centralizes that word.  Thus Properties 1 and 3 cannot be obtained by
simply anchoring one finite selected type or one conjugated spin word.
