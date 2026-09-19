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
- **Self-relaying witnesses: the 2-adic condition drops out** (swarm-0917-w4-gs-binary-descent, 2026-09-17).
  - Established `self-relaying-donor-covering-automata-reach-admissible-types` (route
    `self-relaying-product-with-a-binary-identity`, check `experiments/self-relaying-parity-2026-09-17/check.py`).
    Call a donor-covering automaton *self-relaying* if every active input site stays active and is its own donor.
    For such a witness of type `(z, b)`, `τ × id_{0,1}` with rest symbols `Z × {0}` is self-relaying of type
    `(z, 2b + z)`. So `z = 1` gives an odd active count, and `z = 2` gives `4 ∤ b'`.
  - Every `β × id` witness of item 5 is self-relaying. So for the universal problem the open node
    `donor-covering-few-rest-automata-reach-admissible-types` is not needed. The rest-symbol reduction becomes
    `strict-automata-reduce-to-few-rest-self-relaying-ones` (OPEN, any active count), with route
    `universal-binary-descent-via-death-free-rest-reduction`. The only remaining demand is geometric: merge rest
    symbols while no active input site ever dies.
  - Where it stops: the product fails for witnesses that are not self-relaying, because a birth site whose flag layer
    is active must relay both itself and its old donor. Value-layer designs die at the per-site count of "was active"
    against "is active" (heuristic record on the new node). Births marked by patterns outside the image of a coding
    are untried.
  - Literature check (web, 2026-09-17): no source relating surjunctivity over two symbols to other alphabet sizes was
    found. arXiv 1312.7682 (surjunctive-by-locally-finite groups) says nothing about alphabet size.
- **Every label lift needs a Hilbert hotel; affine relays replace donor matchings** (swarm-0917-w5-gs-binary-descent,
  2026-09-17). Family: group-rings.
  - Literature correction. The statement is printed as an open question: V. G. Pestov, *Hyperlinear and sofic groups:
    a brief guide*, Bull. Symbolic Logic 14 (2008), arXiv 0804.3968, Section 6, verbatim: "It seems to be unclear
    whether it suffices to set A = {0, 1}. Open question 6.2. Is the Gottschalk Surjunctivity Conjecture equivalent to
    its particular case where A = {0, 1}?" This supersedes the "no source found" note above.
  - Kill, ESTABLISHED: `free-orbit-label-lifts-need-count-raising-label-automata`. Consider any strict automaton on
    `C^G` that commutes with a free fibre action with one fixed symbol and lifts a label automaton `τ`. This covers
    every phase rule, and `τ` need not be injective. Then `τ` fixes `0^G`, never lowers the finite active count and
    raises it somewhere. The invariant is the fibre size `|F|^|ℓ|` together with the charge theorem. Every phase
    transport design dies at the first finite label configuration whose count drops, whatever it does at single sites.
  - Transfer, ESTABLISHED: `affine-relay-label-lifts-descend-to-two-symbols`. Let the output phase be an integral
    affine combination of the window phases (coefficients summing to `1`), with the sparse linear maps injective mod
    every prime. Then a strict one-rest automaton of odd type descends to binary strict automata over `G × C_q` for
    infinitely many `q`. This proof is self-contained and uses only the odd-fibre split. Donors are the unit relays.
    Relays need no locally defined matching, only algebraic invertibility.
  - Decomposition: route `universal-binary-descent-via-affine-relay-hotels`, with OPEN prerequisites
    `strict-automata-yield-odd-one-rest-hilbert-hotels` (necessary for every label lift) and
    `odd-one-rest-hilbert-hotels-carry-affine-relays`.
  - Where it stops: no reduction from a strict `β` to an automaton whose count never drops is known. A power of `β`
    gives a quiescent rest symbol, but deaths may outnumber births on finite configurations, and the parity fix
    `τ × id_{0,1}` does not preserve monotonicity. What always holds is a weak relay. If `β` fixes `a0^G`
    and `ν` is its inverse rule on the image with window `N`, every active input site `h` has an active output in
    `hN`, since `ν(a0^N) = a0`. Upgrading this to (R3) needs multiplicities and control of infinite configurations.
  - Checked: `experiments/affine-relay-lifts-2026-09-17/check.py`, exhaustive over `C_n`. Lifts commute with both
    actions, and `θ` is injective exactly when every `A_ℓ` is injective mod `q`.
- **Same-table descent along upsets; it stops at primitive transition digraphs** (swarm-0917-w18-w18-gs-last1,
  2026-09-19). Family: symbolic-dynamics.
  - ESTABLISHED `strict-automaton-upsets-give-smaller-nonsurjunctive-sizes` (route
    `upset-restriction-pinned-particle-count`, no imports). If `τ` is injective and `U` is a nonempty upset of
    its transition digraph `R(τ)` (`x(g) ∈ U` implies `τ(x)(g) ∈ U`), and `τ|_(U^G)` is onto, then `τ` is onto.
    Proof: sites outside `U` are never created, so configurations with finitely many of them form compact
    invariant pieces `D_F`; bijectivity on `U^G` fixes the fibre sizes of the far output map, and a count shows
    `τ(D_F) = D_F`.
  - So a strict `τ` restricts to a strict automaton on every proper upset, with the same group, memory and table.
    This is the first descent that keeps the table. Applied to powers `τ^p`, the same holds for every set closed
    under `R(τ)^p`, e.g. each cyclic class of a periodic sink class.
  - Where it stops (precise): at `n0 = min NS(G)` every strict automaton has `R(τ^p)` strongly connected for all
    `p`, hence `R(τ)` primitive. So descent by sitewise-closed sub-alphabets reaches two symbols only if
    `min NS(G) = 2` already. It cannot move below a primitive digraph. Sub-alphabets closed only on configurations
    carry nothing: every strict automaton has a strict power fixing each constant `a^G`, and `{a}` is then invariant.
  - Remaining freedom for this claim: codes that are not sub-alphabet restrictions. The factor-map lifts
    and label lifts recorded above are such codes.
