---
rg: 2
id: substitution-tiles-hold-bounded-information
kind: claim
title: In a finite substitution every generator and every clopen mark is a finite lookup on bounded-depth addresses, so a mortal machine cannot sit on tiles or points and must run in the reconciliation of words; seeds, whose single point carries unbounded forced data, are the natural home of the tower's machine, and the operadic rung reduces to an Ore condition on words
distinct_from:
  arithmetic-frames-are-capped-machines-live-in-orbits-not-words: that caps hosts built from sized frame classes; this shows that even with arbitrary frames a single generator of a finite substitution carries bounded information, so all unbounded computation happens when words are reconciled.
  seed-evaluation-is-bounded-by-the-forcing-radius: that bounds evaluation of a seed by its forcing radius, which can be unbounded because one seed point is an infinite configuration; this shows substitution tiles have no analogue of that, since every clopen mark is decided at bounded depth.
  halting-pair-seeds-need-a-two-sided-core-mark: that asks the core mark of the halting pair for a two-sided certificate on the seed; this records that in substitution form the mark cannot be a union of tiles unless the decider's run is bounded on the whole space, so the negative certificate can only be an Ore computation on words.
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `symmetric-ore-operads-containing-their-carrier-are-full-groups`, `arithmetic-frames-are-capped-machines-live-in-orbits-not-words`, `branching-squares-are-the-only-operadic-escape-from-the-cap`.

**Parts 1–2 ESTABLISHED** (lane bh-typeA-universal, 2026-09-18). They are elementary, with the
proof below; not independently reviewed. **Part 3 is a design statement for the seed tower
(OPEN)**. No priority claimed.

## Setting

- **The substitution.** A finite substitution is a symmetric Ore refinement operad on a Cantor
  space `Y`, with finitely many colors and generators, finite `ℐ`, and pieces forming a basis.
  Its pieces are identified with model tiles by frames, which may be arbitrary homeomorphisms.
- **The carrier.** A group `Λ` acts faithfully on `Y` by fractions. So its host is `[[Λ]]`, by
  `symmetric-ore-operads-containing-their-carrier-are-full-groups`.
- **Addresses.** The depth-`D` address of `y ∈ Y` is the sequence of pieces containing `y` in a
  fixed cofinal chain of expansions `E_0 < E_1 < …`, up to `E_D`.

## Statement

1. **Bounded information.**
   - Each element of `[[Λ]]`, in particular each generator of `Λ`, is one fraction `e∘d^{-1}`: a
     bijection between the pieces of two expansions, plus the frames of those pieces. That is
     finite data.
   - Every clopen `U ⊆ Y` is a union of pieces of one expansion. Hence `[y ∈ U]` is a finite
     lookup on the depth-`D(U)` address of `y`.
2. **No machine on tiles or points.** Let `τ : Y → N` be a continuous running-time function, for
   instance the halting time of a mortal decider on the configuration encoded by `y`, when every
   point encodes a configuration and every run halts.
   - Then `τ` is bounded, by compactness, and every mark computed from the halted run is clopen
     and decided at bounded depth.
   - If some points (infinite configurations) never halt, the halting set `{τ < ∞}` is open but
     not closed. It is then not a union of tiles, and no fraction has it as a piece.
   - Either way, a single generator of `Λ` cannot carry an unbounded computation.
   - All unbounded computation in the word problem of `[[Λ]]` happens when fractions are
     composed. That is, it happens in reconciling expansions of products of generators: the
     common multiples of `branching-squares-are-the-only-operadic-escape-from-the-cap`,
     Statement 2. So the machine runs on **words**. Its input is built from the word being
     tested, and Ore is the statement that every such run terminates.
3. **Interface with the seed tower (design, OPEN).**
   - **The seed side.** One seed point `y_*` is an infinite configuration, and its values at
     distant sites can be forced by unboundedly long computations. That is the non-local forcing
     `seed-evaluation-is-bounded-by-the-forcing-radius` asks for. The halting-pair core mark can
     live on the seed, with a two-sided certificate (`halting-pair-seeds-need-a-two-sided-core-mark`).
   - **The substitution side.** By 2, a finite substitution for a tower group has no such
     object. The same core mark, as a subset of `Y`, is either:
     - a union of tiles, and then decided by a bounded run on all of `Y`, so it carries no
       hardness; or
     - not clopen, the analogue of the seed side's free bit at infinity (gate RR). Then it is
       not available to fractions at all.
   - **Consequence.** The operadic version of the rung must realize the certificate as an Ore
     computation. For the halting stable letter `k` of an HNN step over the machine subgroup
     `T`, reconciling `k`'s fraction with the expansion of a `T`-word must run the mortal
     membership decider for `T` on that word, and Ore must hold for all pairs.
   - **Constraint.** The frames must lie outside every sized class
     (`arithmetic-frames-are-capped-machines-live-in-orbits-not-words`). The natural
     digit-shift actions of the tower's scaling groups are arithmetic, so they cannot supply this
     step.

## Proof of 1–2

1. **Bounded information.**
   - Under Ore, every element of the operad group is a single fraction. Both expansions are
     finite, so the element is determined by finitely many pieces, a bijection and the frames.
   - Pieces form a basis, and `U` is compact and open. So `U` is a finite union of pieces, and
     by Ore a union of pieces of one expansion. That expansion is refined by some `E_D` in the
     cofinal chain.
2. **Compactness.**
   - `τ` is continuous into the discrete space `N` and `Y` is compact, so `τ` takes finitely
     many values. The set `{τ ≤ t}` is clopen for each `t`.
   - If `τ` is only defined, continuously, on the open halting set `H ⊊ Y`: were `H` clopen, it
     would be compact and `τ` bounded on it. Since `H` is open, `H` is clopen iff it is closed.
     So an unbounded `τ` forces `H` to be non-closed, and by 1 then no fraction has `H` as a
     union of pieces.
   - The last bullet is the growth recursion of the branching-squares node. The words' fractions
     are finite data, and only their common multiples grow. ∎

## Lesson for general BH

**Tiles hold bounded information; seeds do not.**
- **Substitutions.** Every generator and every clopen mark of a finite substitution is a lookup
  on bounded-depth addresses, by compactness. A machine can therefore never sit on the tiles:
  either it is bounded, or its halting set is not clopen. It can only run while words are
  reconciled, with Ore as its mortality theorem.
- **Seeds.** A seed point is one infinite configuration whose far values are forced by unbounded
  computation.

So the seed tower is the natural carrier of the machine. An operadic host can join the tower
only by turning the tower's two-sided core-mark certificate into an Ore computation on words
between the halting stable letter and the machine subgroup. This is a strictly different
design, with frames outside every arithmetic class.
