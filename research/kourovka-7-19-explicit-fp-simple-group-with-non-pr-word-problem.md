---
rg: 2
id: kourovka-7-19-explicit-fp-simple-group-with-non-pr-word-problem
kind: claim
title: Kourovka 7.19 (Cannonito) — an explicit finitely presented simple group whose word problem is not solvable by a primitive recursive function
distinct_from:
  fp-simple-groups-with-arbitrarily-complex-word-problem: that asks, for every recursive bound, for some finitely presented simple group beyond it; this is the printed Kourovka question asking for ONE explicit group beyond every primitive recursive bound at once. The existence part of this follows from that root at a single bound (Ackermann), while explicitness is not addressed there.
  type-a-actors-with-arbitrarily-hard-word-problem: that is the hard-actor claim for all recursive bounds; this needs one explicit actor whose orbit problem is not primitive recursive, recorded as the premise `explicit-type-a-actor-with-non-pr-orbit-problem`.
---

**OPEN.**

**The printed question.** Kourovka Notebook, 21st issue (2026), Problem 7.19, read from the TeX source
(`21tkt.tex`, lines 1759–1762), verbatim: "Construct an explicit example of a finitely presented simple group
with word problem not solvable by a primitive recursive function." Attributed to F. B. Cannonito. The 2026
issue lists it among unsolved problems.

**Reading.** We want an explicitly described finitely presented simple group `S` whose word problem, over a
finite generating set, has a characteristic function that is not primitive recursive. This is invariant under
change of finite generating set, because substitutions are linear-time. Equivalently, for every primitive
recursive `g`, the word problem is not in `F(g)` in the notation of
`uniform-wp-bound-excludes-bh-universal-targets`, since primitive recursive functions are exactly those
computable within primitive recursive time.

## How it sits in the graph

- **Existence (non-explicit) from the complexity root.** Let `A(n) = Ack(n,n)`, which eventually dominates every
  primitive recursive function. An `S` given by `fp-simple-groups-with-arbitrarily-complex-word-problem` for the
  single bound `T = A` has no word-problem algorithm in any primitive recursive time. So the root implies the
  existence form of 7.19. The root is OPEN, and 7.19 additionally asks for an explicit example.
- **Every known explicit finitely presented simple group is primitive recursive.**
  - `nV` is coNP (Birget, as recorded on the root).
  - Rational homeomorphism groups are exponential (`rational-homeomorphism-subgroups-have-exponential-wp`).
  - Towers of twisted Brin–Thompson constructions over a bounded actor stay elementary (iteration clause of
    `twisted-brin-thompson-wp-equals-actor-orbit-problem`).
  - So an answer must come from an actor, or a germ datum, that is not primitive recursive.

## Routes

1. `kourovka-7-19-via-hard-type-a-actor`. An explicit faithful type (A) action whose orbit problem (word problem
   plus point-stabilizer membership) is not primitive recursive gives the explicit answer `SV_G`. It is simple
   and finitely presented by `twisted-brin-thompson-finite-presentation-criterion`, and not primitive recursive
   by (a) of `twisted-brin-thompson-wp-equals-actor-orbit-problem`. The premise is OPEN.
2. `kourovka-7-19-via-small-cancellation-bh`. Boone–Higman for one explicit two-generator `C'(1/6)` group `G_A`,
   with `A` an explicit decidable set that is not primitive recursive, by a constructive proof.

## What is excluded

- **Hard points in prefix-replacement hosts.** `aperiodic-point-stabilizers-in-germ-extensions-of-v-are-not-fg`.
  A Thompson-like group acting on the orbit of a hard-to-compute point is never of type (A) at a nonsingular
  aperiodic point, and eventually periodic points are polynomial.
- **Bounded-displacement half-finite generators.** `fp-bounded-displacement-e2-envelopes-are-eventually-periodic`
  (on `hard-half-finite-permutations-have-fp-shift-envelopes`).
- **Mihailova stabilizers.** They need a finitely presented `Q` with finitely many conjugacy classes (Attempt 4 on
  `type-a-actors-with-arbitrarily-hard-word-problem`).

## Attempts

1. **Rigidity from property (T) (2026-09-18, lane bh-free-34).** No mechanism.
   - The Houghton-like route's gate concerns the chosen overgroup, not the input
     (`fg-simple-subgroups-of-houghton-like-groups-embed-in-germs`).
2. **Hard base points (2026-09-18, lane bh-free-34).** Dies inside prefix-replacement hosts, by the node above.
   - The only half-finite route left needs a finite cross-scale rule whose unique solution is hard. Uniqueness makes
     evaluation computable by exhaustion, but a solution pinned only by constraints at far larger scales would have
     no primitive recursive evaluation bound. That is the shape a 7.19 witness on this route must have.
     (Hand remark; no construction.)
