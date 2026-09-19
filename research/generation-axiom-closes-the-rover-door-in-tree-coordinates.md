---
rg: 2
id: generation-axiom-closes-the-rover-door-in-tree-coordinates
kind: claim
title: Farley–Hughes's generation axiom (S5) forces Röver-type certificates, whose chosen structure is not closed under restriction, to be finite-state when the chosen structure groups are finite and to have geometrically bounded sections when they are finitely generated; so in tree coordinates such certificates cap orbit evaluation too, and the last door for a hard seed via FH closes there
distinct_from:
  farley-hughes-complexity-caps-review: that leaves open door (b), non-restriction-closed structures such as FH's Röver certificate; this closes door (b) in tree coordinates, using the generation axiom FH themselves verify by contraction.
  rover-nekrashevych-engines-cap-orbit-evaluation-exponentially: that caps restriction-closed, finitely generated structures; this covers the chosen, non-restriction-closed ones through (S5).
  finitary-permutations-force-singleton-domains: that closes door (a), the seed address; this closes door (b) in tree coordinates.
---

**ESTABLISHED in tree coordinates; OPEN for abstract certificates** (lane bh-invent-03, 2026-09-19; elementary; not
reviewed). Read at source: Farley–Hughes arXiv:2010.08035, Def. 4.2 (P1)–(P5), (S1)–(S6), Ex. 4.4, and Ex. 4.35
(Röver, p. 32).

## What Röver's certificate actually uses (FH Ex. 4.35, Prop. 6.24, Ex. 8.4)

- **The chosen structure.** It is `𝕊(B_(ω1), B_(ω2)) = {σ, b, c, d}_(ω1,ω2)`, which is finite and not closed under
  restriction (`b_(ε,ε)|_(B_0) = a_(0,0)`). The maximal structure groups contain all of Grigorchuk's `G`.
- **The expansions.** The patterns are maximal, and there are exactly two simple expansions per domain, the standard
  one and a nonstandard one. The scheme is `n`-connected and rich in contractions (`C_1 = 2`).
- **Where contraction enters.** The self-similarity and **contraction** of `G` are used only to verify that `(𝕊, ℙ)`
  is an S-structure, i.e. for the generation axiom **(S5)**. That axiom says every locally determined map becomes,
  on a pattern, a union of chosen structure maps.
- **The finiteness argument itself** (Thm. 8.2) never looks at sections.

## Statement

**Tree coordinates.** The domains are the cones `B_ω` of a regular tree over a finite alphabet, together with
singletons if vertices are included. `S` consists of the maps `g_(ω1,ω2)` (prefix swap, then `g`), for `g` in a
self-similar group `G`. The chosen structure is `𝕊(B_(ω1), B_(ω2)) = {h_(ω1,ω2) : h ∈ H}` for a subset `H ⊆ G`, and
the certificate satisfies FH's axioms, in particular (S5).

1. **`H` finite.** Then every element of `Γ_S` acts on addresses by bounded prefix swaps and finitely many states.
   So orbits are decidable in quadratic time, and word problems in `2^(O(n))`, as in
   `finite-type-farley-hughes-groups-are-exponentially-capped`.
2. **`H` a finitely generated group.** This is what FH's Thm. 8.2 needs, `𝕊(D, D)` of type `F_n`. Then every
   generator of `H` has, at bounded depth `δ`, all its sections equal to `H`-words of bounded length `c`. So section
   lengths grow at most geometrically, and orbits are decidable in `2^(O(n))`, as in
   `rover-nekrashevych-engines-cap-orbit-evaluation-exponentially`.
3. **Consequence.** Together with `finitary-permutations-force-singleton-domains` (door (a)), no seed whose
   evaluation beats `2^(O(n))` can be certified by an FH certificate in tree coordinates, restriction-closed or
   not.

## Proof

1. **(S5) applied to `h ∈ H`.** Each `h` has a pattern of the root on whose pieces it acts as a chosen map
   `h'_(ω,ω')` with `h' ∈ H`, i.e. prefix swap followed by `h'`. So the sections of `h` at the pattern depth
   `δ_h` lie in `H`. Iterating, every section of `h` at any depth is either one of its finitely many sections above
   depth `δ_h`, or a section of an element of `H` at its own shallower depths. Since `H` is finite, the set of all
   sections of all elements of `H` is finite.
   - **Every `g ∈ G` then has finitely many sections.** Apply (S5) to `g`: its sections at depth `δ_g` lie in `H`.
     So `G` is finite-state.
   - **Every element of `Γ_S`** is a finite union of maps `g_(ω1,ω2)`, and the finite-type argument applies.
2. **Fix a finite generating set `A` of `H`.** By (S5), for each `a ∈ A` there is a depth `δ_a` at which all
   sections of `a` lie in `H`, hence are `A`-words. Let `δ = max δ_a`, and let `c` bound the lengths of these words.
   - **Sections of words.** A word of length `m` has its sections at depth `kδ` given by `A`-words of length
     `≤ c^k m`.
   - **Evaluation.** Applying it to a tail of length `ℓ` costs `2^(O(ℓ))`. With the bounded prefix changes of the
     generators of `Γ_S`, which (S5) also reduces to `H`-maps, the orbit test costs `2^(O(n))`, as in
     `rover-nekrashevych-engines-cap-orbit-evaluation-exponentially`.
3. Combine 1 and 2 with the finite address of the seed. ∎

## What is left open

- **Abstract certificates.** These are certificates whose domains are not cones of a tree with prefix coordinates.
  The argument above needs **coherent coordinates**: canonical maps `κ_N` for all nodes whose restrictions are, after
  bounded refinement, chosen maps with bounded words.
  - **Tree coordinates** give this, through the prefix structure.
  - **Seed full groups,** with their natural `S` of partial translations, have a restriction-closed maximal
    structure. When its groups are finite, as for free actions whose translations fix no domain (T0), the
    finite-type cap applies directly.
  - **The remaining case** is abstract certificates with infinite, finitely generated structure groups and no
    coherent coordinates. It is **open**.
- **Hardness through the word problem.** This is not affected. `WP(Γ_S)` contains `WP(H)`, which can be hard. So FH
  certificates can still carry hard **word problems** imported from a hard `F_∞` structure group `H`.

## Lesson for general BH

**Gate 1 via Farley–Hughes, in its hard-seed form, is dead in tree coordinates.** All three doors are shut:
- restriction-closed structures, by the self-similar cap;
- infinite seed addresses, by finitary permutations;
- chosen structures that are not closed under restriction, by the generation axiom.

**Why FH engines cannot create evaluation hardness.** They certify finiteness only when (S5) makes every map
eventually a bounded word in the chosen structure. That is exactly geometric section growth, so every such engine
evaluates orbits in exponential time.

**What remains of HARD-(A) via FH.** The word problem of an `F_∞` structure group, which is the Röver–Nekrashevych
branch. For abstract certificates it also needs a coherent-coordinates lemma.
