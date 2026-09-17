---
rg: 2
id: surjunctivity-failure-descends-to-binary-alphabet
kind: claim
title: A group carrying a strict automaton over some finite alphabet carries one over two symbols
distinct_from:
  strict-rule-pairs-pass-to-product-alphabets: that moves strictness up along multiples of the alphabet size with the tables fixed; this asks for strictness to move down to two symbols, with the tables allowed to change.
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
---

**OPEN.** If a group `K` is not `A`-surjunctive for some finite alphabet `A`, then `K` is not
`{0,1}`-surjunctive. The memories and tables may change.

Together with `every-group-is-binary-surjunctive`, this would reduce Gottschalk's conjecture to
two symbols (`gottschalk-via-binary-alphabet-descent`).

## Attempts

- **Fixed tables, via products.** `strict-rule-pairs-pass-to-product-alphabets` moves strictness
  only from `k` to multiples `kl`, never down.
- **Fixed tables do not descend at all.** `equal-label-table-is-strict-at-three-symbols-not-two`
  shows that the table `x_a = x_b` with a discrete reverse table admits strict rules over every
  alphabet with at least three symbols and over none with two. Any group-level descent must
  therefore change the tables, e.g. by enlarging the memories.
- **Retraction onto a sub-alphabet.** Using `mu o r` and `nu o r` loses the fiber position of the
  demanded cell. When the class of `(1,1)` meets only relay `1`, that relay must carry both the
  code's symbol and the fiber position. So the extension fails unless the fibers have equal size,
  and equal fibers are exactly products. Artifact Section 5.
- **Erasure symbol.** The sink loses the values of relays reading a starred cell, and the forward
  identity uses every relay.
- **Block codes over a finite subgroup `H` with `2^|H| >= |A|`.**
  - Decoding `x -> (d((x(g h))_h))_g` is equivariant.
  - Encoding needs an equivariant choice of positions inside each coset `gH`, which a group does not
    supply without markers.
  - So an `A`-configuration cannot be written equivariantly in binary, and no binary strict
    automaton results.
- No literature source was checked for this statement.
- **Reformulation and the marker obstruction** (w3-alphabet). Descent is equivalent to an equivariant
  continuous binary coding with a one-sided inverse: an equivariant continuous injection
  `e : A^K -> {0,1}^K` with equivariant continuous retraction `r`, `r o e = id`, `e(A^K)` clopen; then
  `e o tau o r` (identity off the image) is a strict automaton on `{0,1}^K`. The only known binary coding
  is block coding over a finite subgroup `H <= K` with `2^{|H|} >= |A|`, whose encoding step needs an
  equivariant marking of `K/H` (an equivariant transversal), a coloring/SFT datum a group need not admit.
  On a finitely generated infinite simple group — the hosts the conjecture reduces to — there is no proper
  finite-index subgroup and no nontrivial finite quotient, and a finite `H` has infinite-index normalizer,
  so no equivariant marking of `K/H` exists and block-code descent is unavailable on exactly those hosts.
  Any descent proof for the target hosts must give a markerless equivariant binary coding; none is known.
  This marker argument is a structural sketch, not a formalized theorem. Artifact
  `research/artifacts/alphabet-ascent-and-binary-descent-2026-09-12.md`, Section 3.
- **Reserved-site extensions are dead** (gk3-alphabet-descent, 2026-09-14).
  `passive-fixing-injective-automata-are-surjective` proves, over every group, that an injective automaton
  which leaves a reserved set of symbols in place and writes no reserved symbol at an unreserved site is
  surjective. So a coding that keeps its invalid symbols fixed can never carry strictness. Any descent must
  write on reserved sites, or write reserved symbols at unreserved ones.
- **Weaker universal form** (gk3-alphabet-descent, 2026-09-14). `some-nonsurjunctive-group-gives-a-binary-one`
  lets the binary witness live on any group.
  - This claim implies it (`universal-binary-descent-from-groupwise-descent`).
  - With `every-group-is-binary-surjunctive` it already gives the goal (`gottschalk-via-universal-binary-descent`).
  - By `ec-groups-share-the-nonsurjunctive-alphabet-sizes` it is exactly this claim for existentially closed
    groups.

  Artifact `research/artifacts/gk3-alphabet-descent-2026-09-14.md`.
- **Correction: codings cannot carry descent** (swarm, 2026-09-16).
  - For `|A| >= 3` there is no equivariant injection `A^K -> {0,1}^K` at all, continuous or not. It would
    map the `|A|` constant configurations injectively into the two binary ones
    (`full-shifts-with-different-alphabets-are-not-conjugate`).
  - So the coding `e` of the "Reformulation" bullet never exists. "Equivalent" there is wrong: descent
    holds vacuously over every surjunctive group, where no coding exists either. The marker discussion is
    moot, since block coding fails at the constants even where markers exist.
  - The compression lemma of `research/artifacts/gk3-binary-descent-2-2026-09-14.md`, Section 2, is
    vacuous for the same reason: its hypothesis is never met.
  - Strictness does transfer through a factor map `r: {0,1}^K -> A^K` with an injective automaton `Phi`,
    `r o Phi = tau o r`. Over `F_2` with the Ornstein–Weiss map, the automata with injective lifts are
    exactly those induced by injective flip-commuting binary automata, and the coordinate swap has no lift by any
    automaton. Notes `notes/surjunctivity-failure-descends-to-binary-swarm-2026-09-16.md`, Sections 1-2.
- **Label-level phase transport; the obstruction is the rest alphabet** (a-gs-binary-descent, 2026-09-17).
  Split the alphabet into rest symbols `Z` and active symbols `B`. Call a strict automaton *donor-covering* if
  every active output site reads a designated active input site in its memory window, and every active input
  site is read by some active output site.
  - Such an automaton of type `(|Z|, |B|) = (2, (2^p - 2)/p)`, or `(1, (2^(q-1) - 1)/q)`, gives a binary strict
    automaton over `G × C_p`, resp. `G × C_q`. Label the free orbits of `{0,1}^(C_p)`, resp. of `I_(C_q)`, by `B`,
    and let each output phase copy the phase of its donor
    (`donor-covering-strict-automata-descend-to-two-symbols`, ESTABLISHED).
  - `|B|` can be multiplied freely, so the types that work are `(1, odd)` and `(2, b)` with `4 ∤ b`.
  - Every strict `β` gives type `(|A|, |A|)` as `β × id` with an activity bit. So universal descent is exactly
    reducing the rest alphabet to two symbols (`strict-automata-reduce-to-two-rest-donor-covering-ones`, OPEN).
    Orbit counting, where Section 4.3 of `research/artifacts/gk3-alphabet-descent-2026-09-14.md` died, is not the
    obstruction.
  - With one rest symbol the witness must raise the active count on some finite configuration
    (`one-rest-donor-covering-strict-automata-raise-the-count`, via the charge theorem).
  - For the same-group statement this changes the group to `G × C_p`. By
    `ec-groups-share-the-nonsurjunctive-alphabet-sizes` that is harmless for existentially closed `G`, and not
    otherwise.
  - Where it stops: no construction lowers the number of rest symbols. The naive reclassification dies at the
    relay condition.
