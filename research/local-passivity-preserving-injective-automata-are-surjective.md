---
rg: 2
id: local-passivity-preserving-injective-automata-are-surjective
kind: claim
title: An injective automaton that fixes every locally passive site and creates no active site is surjective, over every group
distinct_from:
  passive-fixing-injective-automata-are-surjective: that defines passivity by the symbol at a site and also assumes active sites stay active; this defines passivity by the pattern on a finite neighbourhood and needs only that the automaton fixes passive sites and creates no new active site.
  nonamenable-groups-carry-arrow-shift-strict-automata: that builds strict maps fibred over an arrow shift and shows no full shift maps into the base; this shows that full-shift designs which leave locally passive regions untouched and never activate them cannot be strict.
  amenable-groups-satisfy-the-garden-of-eden-theorem: that derives surjectivity from pre-injectivity on amenable groups; this derives surjectivity from injectivity on every group, under conditions on where the automaton writes.
artifacts:
  - research/artifacts/ideas-gottschalk-3-2026-09-14.md
---

**ESTABLISHED** by `local-passivity-surjectivity-proof` (elementary; no novelty claimed).

**Setting.**
- `G` is a group, `A` a finite alphabet, and `W ⊆ G` a finite set containing `1`.
- `P ⊆ A^W` is a set of *passive patterns* that contains a constant pattern `a^W` for some `a ∈ A`.
- For `x ∈ A^G` and `g ∈ G` write `(g⁻¹x)(w) = x(gw)`. The *active set* of `x` is
  `Act(x) = { g ∈ G : (g⁻¹x)|_W ∉ P }`. The other sites are *passive* in `x`.
- `Φ` is a cellular automaton on `A^G`.

**Theorem.** Suppose `Φ` is injective and, for every configuration `x`:
1. **(fixes passive sites)** `Φ(x)(g) = x(g)` for every `g ∉ Act(x)`;
2. **(creates no active site)** `Act(Φ(x)) ⊆ Act(x)`.

Then `Φ` is surjective.

**Corollaries.**
1. **Sitewise passivity needs only (1).** For `W = {1}`, a passive symbol that is left in place is still
   passive, so (2) follows from (1). An injective automaton that leaves every site carrying a passive symbol
   unchanged is surjective (`injective-automata-fixing-passive-sites-are-surjective`). The second hypothesis
   of `passive-fixing-injective-automata-are-surjective` ("active sites stay active") is not needed.
2. **Reserved symbols.** A strict automaton on `(A ⊔ D)^G`, obtained by ascent or through a coding, must on
   some configuration rewrite a site carrying a `D`-symbol. Writing `D`-symbols at `A`-sites does not help.
3. **Locally constant patches.** Take `P` to be the constant patterns on `W`. A strict automaton that is the
   identity at every site whose `W`-neighbourhood is constant must, on some configuration `x` and some site `g`
   with `x` constant on `gW`, produce `Φ(x)` non-constant on `gW`. It has to push non-constancy into constant
   regions. By (1) alone that creep is bounded in one step: `Act(Φ(x)) ⊆ Act(x) W⁻¹`.
4. **Hotel designs.** By item 4 of `nonamenable-groups-carry-arrow-shift-strict-automata`, an arrow field
   computed equivariantly from the data is undefined on the constant configurations, so a hotel pullback has to
   act as the identity on constant patches or bring in some other rule there. Corollary 3 says the first
   choice is strict only if it activates constant patches from their boundaries. That is the necessary shape of
   such a design.

**Model tests.**
- The left shift on `{0,1,*}^Z` violates (1): it moves active symbols into passive sites. It is bijective, so
  it is no counterexample, but (1) is not automatic.
- The rule "output `*` at a site that carries `*` or has a neighbour carrying `*`, and the input symbol otherwise" on
  `{0,1,*}^Z` satisfies (1) for `P = {*}` and is not injective (`0*0` and `1*0` both become `***`), consistent with
  the theorem.
- The strict maps landed on main are not on full shifts with fixed passive regions: arrow-shift hotels live over
  `X_S × A^G`, compressed coset shifts over `A^(G/H)`. Neither contradicts the theorem.

**Open.** Whether (2) can be dropped when `|W| > 1` is not known. The proof uses (2) exactly once, in the
invariance of the finite pieces.
