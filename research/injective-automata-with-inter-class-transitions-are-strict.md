---
rg: 2
id: injective-automata-with-inter-class-transitions-are-strict
kind: claim
title: An injective automaton whose letter-transition digraph has an arc between two classes is strict, so a never-created letter that is sometimes destroyed makes NS(G) cofinite
distinct_from:
  every-injective-ca-has-uniform-single-site-output-law: that asks every injective automaton for a uniform one-site law and is equivalent to surjunctivity; this is its unconditional sitewise shadow, where a non-exact upset forces a non-uniform law, turned into a strictness certificate readable from the local rule.
  transition-digraph-capacity-lifts-give-nonsurjunctive-sizes: that assumes a strict automaton and reads sizes off its digraph; this derives strictness from injectivity plus one inter-class arc, so its singleton-class target needs no separate strictness proof.
  passive-fixing-injective-automata-are-surjective: that kills injective extensions whose added letters stay fixed in place; this shows every injective extension in which the added letters are never created is strict, whether or not they move.
  reversible-automata-that-never-lower-rest-counts-preserve-them: that is a count statement on finitely supported configurations; this is a sitewise statement on all configurations, from the invariant measure.
  nonsurjunctive-alphabet-sizes-are-upward-closed: that asks for every size above a failing one; this shows that an ascent by never-created letters needs only injectivity, not a separate strictness proof.
  some-nonsurjunctive-group-gives-a-binary-power-one: that asks for a binary-power failing size; this gives a digraph certificate for all large sizes, whose existence from a strict automaton is left open.
  finite-injective-charge-noncreation-forces-surjectivity: that forbids charge creation on finitely supported configurations with a quiescent symbol; this forbids one-way letter transitions for bijective automata on the full shift.
---

**ESTABLISHED** by `inter-class-arc-strictness-bernoulli-proof`, over every group.

**Setting.** `G` is any group, `B` a finite alphabet and `Ψ` a cellular automaton on `B^G`. As in
`transition-digraph-capacity-lifts-give-nonsurjunctive-sizes`:
- the transition digraph is `R(Ψ) = {(x(g), Ψ(x)(g))}`;
- an *upset* is `U ⊆ B` with `x(g) ∈ U ⇒ Ψ(x)(g) ∈ U`;
- the *classes* are the strongly connected components of `R(Ψ)`.

`R(Ψ)` is read off the local rule: it is `{(u(1), μ(u)) : u ∈ B^M}`.

**Theorem.**
1. **Upset rigidity.** If `Ψ` is bijective and `U` is an upset, then `x(g) ∈ U ⇔ Ψ(x)(g) ∈ U` for all `x`
   and `g`, and `Ψ(U^G) = U^G`.
2. **No one-way arcs.** A bijective `Ψ` has no arc of `R(Ψ)` between two different classes. So every weakly
   connected component of `R(Ψ)` is strongly connected.
3. **Strictness certificate.** An injective `Ψ` whose digraph `R(Ψ)` has an arc between two classes is strict.
   It is then subject to every item of the capacity-lift theorem. In particular, if also some class of
   `R(Ψ)` has size `1`, then `g(Ψ) = 1` and `NS(G)` is cofinite.
4. **Never-created letters.** Let `Ψ` be injective, and let `c` be a letter that `Ψ` never writes at a site that
   did not already hold `c`. Then exactly one of the following holds:
   - `c` is inert (`x(g) = c ⇔ Ψ(x)(g) = c`), and `Ψ` is bijective;
   - `c` is sometimes destroyed. Then `Ψ` is strict, `{c}` is a class, `g(Ψ) = 1`, and `NS(G)` is cofinite.
5. **Restriction to upsets.** Let `Ψ` be injective and `U` a nonempty upset. If `Ψ|_(U^G)` is not onto `U^G`,
   then `Ψ` is strict.
6. **Ascent without a strictness proof.** Let `τ` be strict on `A^G` and `Φ` an injective automaton on
   `(A ⊔ D)^G` extending `τ`, in which no `D`-letter is ever written at an `A`-site. Then `Φ` is strict, so
   `|A| + |D| ∈ NS(G)`.

**Why it matters.**
- *Strictness is decided by the digraph.* To certify a strict automaton, it is enough to give a local rule, a
  left-inverse rule, and one arc of `R(Ψ)` that returns to no earlier class. No orphan pattern and no
  counting over the group is needed.
- *The singleton-class target becomes an injectivity problem.* The target of
  `transition-digraph-capacity-lifts-give-nonsurjunctive-sizes` (a strict automaton with a class `{c}`) is now
  the same as an injective automaton with a class of size `1` and one arc between two classes. The simplest
  instance is a letter that is never created but sometimes destroyed. Such an automaton over `G` gives all
  large alphabet sizes, so it gives `some-nonsurjunctive-group-gives-a-binary-power-one` with `G` itself and
  refutes the conjecture at every large size.
- *Ascent.* Item 6 answers a caution recorded in wave 19 ("strictness is not automatic there") in the
  negative. Once an injective extension of a strict `τ` exists that never writes a new letter at an old site,
  strictness is automatic. So such an ascent `k -> k + |D|` is exactly a question about injectivity.
- *Conditional forms.* Call an upset `U` *exact* if also `Ψ(x)(g) ∈ U ⇒ x(g) ∈ U`. A non-exact upset
  carries an arc from outside `U` into `U`, and such an arc joins two classes, since `U` contains everything
  reachable from its members.
  - If the conjecture holds, every injective automaton over every group has only exact upsets.
  - If `every-group-is-surjunctive-over-binary-power-alphabets` holds, every never-created letter of every
    injective automaton is inert, because item 4 would otherwise put every large power of two in `NS(G)`.
    Non-exact upsets are then still allowed when the odd part of `g(Ψ)` exceeds `1`.

**Where it stops.**
- The theorem does not construct any injective automaton with an inter-class arc. It says nothing when
  `R(Ψ)` is a disjoint union of strongly connected pieces. Two examples: a robustly primitive digraph, and
  every letter-permuting rule.
- There is no converse for the cofinite conclusion. It is not known whether a strict `τ` over `G` yields an
  injective automaton over `G` with a never-created letter that is sometimes destroyed, or, more weakly, with
  a class of size `1`.
  - Identity layers `τ × id_c` and capacity lifts do not give one. Their class sizes stay in `g(τ)Z`, as
    recorded under "Where it stops" in `transition-digraph-capacity-lifts-give-nonsurjunctive-sizes`.
  - A strict `τ` whose own `R(τ)` is a disjoint union of strongly connected pieces is not excluded. For it,
    items 3 to 6 are silent.

## Attempts

- **Sitewise measure rigidity** (swarm-0917-w20-w20-gs-follow, 2026-09-20). Established, route
  `inter-class-arc-strictness-bernoulli-proof`.
  - Invariant: the clopen set `{x : x(1) ∈ U}` for an upset `U`.
  - The kill: for bijective `Ψ`, invariance of the uniform product measure turns the inclusion of this set in
    its preimage into equality.
