---
rg: 2
id: separated-omitted-patterns-make-nonsurjunctive-sizes-cofinite
kind: claim
title: A strict automaton that omits a letter, or omits a pattern whose support some finite-index subgroup separates, makes NS cofinite, so the binary-power bridge can fail only through profinitely invisible defects
distinct_from:
  transition-digraph-capacity-lifts-give-nonsurjunctive-sizes: that reads NS(G) from the class sizes of the letter-transition digraph and gives only multiples of g(τ); this adds the restriction k-1 ∈ NS(G), shows an omitted letter forces g(τ) = 1, and regroups over a separating finite-index subgroup to manufacture omitted letters from omitted patterns.
  some-nonsurjunctive-group-gives-a-binary-power-one: that is the open bridge for all strict data; this settles it for every strict datum having an omitted pattern that is separated in some group sharing a large enough ball, and names what a counterexample world must look like.
  surjunctivity-is-a-commensurability-invariant: that transfers surjunctivity across finite index with the product alphabet A^n; this uses the same regrouping only to turn a pattern defect into a letter defect and does not by itself change NS.
  nonsurjunctive-alphabet-sizes-are-upward-closed: that asks for every size above a failing one for every strict datum; this gives cofiniteness only under an omitted letter or a separated omitted pattern.
  constant-background-kills-unit-linear-defect-rules: that concerns a patch pattern of a rule omitting a symbol and proves non-injectivity; here the image of an injective rule omits a letter, and the output is a size statement.
---

**ESTABLISHED** by `separated-omitted-patterns-cofinite-proof`. Elementary given the imports.

**Setting.** `τ` is a cellular automaton over a group `G` with finite alphabet `A`, `|A| = k`. It is *strict* if it
is injective and not surjective. `NS(G)` is the set of alphabet sizes carrying a strict automaton over `G`, and
`NS_all` is the union over all groups. Since `τ(A^G)` is a closed, shift-invariant, proper subset, it omits some
pattern `w ∈ A^F` for a finite `F ⊂ G`: no translate of any image configuration restricts to `w` on `F`. The
*finite residual* `K(G)` is the intersection of all finite-index subgroups of `G`. It is normal.

**Theorem.** Let `τ` be strict over `G`.
1. **Omitted letter.** Suppose the image omits a letter `b`, that is, `F` can be a single point.
   - Then `k - 1 ∈ NS(G)`: `τ` restricts to a strict automaton on `(A \ {b})^G`.
   - Also `A \ {b}` is an upset with `z = 1`, so `g(τ) = 1`, and `NS(G)` contains every `n >= (k-1)^2 + 1`. In
     particular `2^j ∈ NS(G)` for every large `j`.
2. **Separated omitted pattern.** Suppose the image omits `w ∈ A^F`, and some finite-index `H <= G` puts the
   points of `F` in distinct right cosets, i.e. `f f'^(-1) ∉ H` for `f ≠ f'` in `F`. Then `NS(H)` is cofinite and
   `NS(H) ⊆ NS(G)`. So `NS(G)` is cofinite. The mechanism is to regroup over `H` with a transversal containing
   `F`. Every letter of `A^T` that extends `w` is then omitted, and item 1 applies.
3. **Criterion.** Such an `H` exists iff `F F^(-1) ∩ K(G) = {1}`. In particular a single-point `F` always works,
   which is item 1.
4. **Ball form.** Let `M` be the memory. Replace `G` by `⟨M ∪ F⟩`; the restricted rule is still strict and still
   omits `w`. Fix a finite generating set `S ⊇ M ∪ F`, and let `G_L = ⟨S | words of length <= L trivial in G⟩` be
   the finitely presented covers.
   - For large `L`, the same local rule is strict over `G_L` and omits the same `w` on the lifted `F`.
   - Hence the bridge `some-nonsurjunctive-group-gives-a-binary-power-one` holds as soon as one strict datum, over
     any group, has an omitted pattern with `F F^(-1) ∩ K(G_L) = {1}` for some `L`.
   - Contrapositive: if the bridge fails, then for every strict datum, every omitted pattern of it, and every `L`,
     the support `F` meets some coset of `K(G_L)` at least twice.
5. **No compression under binary-power surjunctivity.** If
   `every-group-is-surjunctive-over-binary-power-alphabets` holds, then:
   - no group has an injective cellular automaton `A^G -> B^G` with `|B| < |A|`;
   - the image of every strict automaton contains every letter;
   - after regrouping over any finite-index subgroup, the image contains every letter of the product alphabet.
   Conversely, such a compression would give a strict automaton that omits a letter, and hence a binary-power
   non-surjunctive size.

**Why it matters.**
- It gives a precise obstruction for the bridge. A counterexample world, where some strict automaton exists but no
  binary-power one does, needs every defect of every strict datum to be *profinitely invisible*. That means the
  omitted-pattern supports collide modulo the finite residual in every finitely presented cover. Omitted letters
  are ruled out outright.
- It turns a search target into a single test. A strict automaton, or a regrouping of one, whose image misses one
  symbol already proves the bridge.

**Where it stops.**
- The criterion is vacuous for patterns with `|F| >= 2` when `K = G`. Examples are finitely generated infinite
  simple groups, which include the Kazhdan simple groups where other reductions of the conjecture live. It is also
  vacuous in every `G_L` whose finite residual contains `F F^(-1)`.
- Overgroups cannot help: if `H' <= G'` has finite index and separates `F ⊂ G <= G'`, then so does `H' ∩ G <= G`.
- Every `G_L` carrying a strict datum is non-surjunctive, so it is not sofic and not residually finite. The
  separation must therefore come from a proper, nontrivial finite residual.
