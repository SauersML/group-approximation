# Alphabet descent for Gottschalk: a passive-site barrier and the per-size existentially closed transfer

Lane gk3-alphabet-descent, 2026-09-14. The target was to reduce Gottschalk's conjecture to two symbols:
a strict automaton (injective, not surjective) over some finite alphabet should give one over two symbols,
over the same group or a related one. **Not decided.** Landed: one barrier theorem, one elementary
transfer, one weaker descent claim and two routes. Nothing here is independently reviewed.

## 1. Sources and what is already on main

Facts at a fixed alphabet already ESTABLISHED on main, all used below:
- `surjunctivity-passes-to-subgroups`. The induced automaton over an overgroup keeps the alphabet, the
  memory and the rule, so failure of surjunctivity at a fixed size passes to overgroups.
- `strict-rule-pairs-pass-to-product-alphabets`. Strictness passes from `k` symbols to every multiple `kl`.
- `surjunctivity-is-axiomatized-by-rectangle-clauses`. Its Theorem 1 works at a fixed alphabet: a group is
  not `A`-surjunctive exactly when strict data over `A` are realized in it.
- `existentially-closed-groups-contain-every-finite-table`.
- `equal-label-table-is-strict-at-three-symbols-not-two`. Fixed tables do not descend.

Literature. A web search for a published statement that surjunctivity at one alphabet size implies it at
another found none. The monograph *Cellular Automata and Groups* (Ceccherini-Silberstein and Coornaert) was
not read; it is paywalled. No literature statement is load-bearing in this artifact. The standard
restriction fact (an automaton over `K` at size `n`, restricted to a subgroup of index `j`, is an automaton
at size `n^j`) is recalled, not source-checked, and no landed node of this lane uses it.

## 2. Barrier: passive-fixing injective automata are surjective

`passive-fixing-injective-automata-are-surjective`, route `passive-fixing-injective-automata-surjective-proof`.

**Statement.** Let `P ⊆ C` be a nonempty set of passive symbols. An injective automaton on `C^G` that leaves
every passive site unchanged and writes no passive symbol at an active site is surjective, over every group.

**Idea.** Configurations with finitely many active sites split into finite pieces `X(E, ω)` (active set
`E`, passive values `ω` outside). The automaton maps each piece into itself, so it is a bijection there.
The pieces are dense and the image is closed.

**Model tests.**
- **Shift on `{0,1,*}^Z`.** `x -> x(. + 1)` is bijective. It writes an active symbol at a passive site
  whenever `x(n) = *` and `x(n+1) != *`, so the first hypothesis fails and nothing is contradicted.
- **Spreading stars.** "Output `*` if some neighbour is `*`" writes passive symbols at active sites, so
  the second hypothesis fails. That automaton is not injective either.
- **Landed strict transfers.** The product rules `mu'((a_m, b_m)_m) = (mu(a), b_1)` use no reserved symbol.
  The passive-block involution codes of `passive-block-involution-codes-ascend` act on tables, not on full
  shifts with fixed sites. So the theorem contradicts neither.

**What it kills.**
- **Walls at group level** (`strict-rule-pairs-ascend-to-larger-alphabets`, Attempts; artifact
  `formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md`, Section 7). The construction outputs
  `*` at starred sites, raw symbols within radius `R` of a star, and `tau`-values elsewhere. Stars stay
  stars and active sites stay active, so once injective it is surjective. The annulus was not bad
  bookkeeping: no radius and no rule near the stars can work.
- **Every sitewise "identity on reserved symbols" design,** for ascent to `A ⊔ D` and for descent through
  a coding alike.

**What it does not kill.**
- Designs defined as the identity off the image of a coding, since that condition is not sitewise.
- Designs in which relays reading a reserved symbol output it (the erasure design).
- Designs that rewrite reserved sites.

## 3. The transfer to existentially closed groups, size by size

`ec-groups-share-the-nonsurjunctive-alphabet-sizes`, route `ec-groups-share-nonsurjunctive-alphabet-sizes-proof`.

Write `NS(K)` for the sizes `n >= 2` at which `K` carries a strict automaton, and `NS_all` for their union
over all groups.
- `NS(H) ⊆ NS(G)` for `H <= G`.
- `NS(G)` is closed under multiples.
- For every existentially closed `K`, `NS(K) = NS_all`. A strict datum over `A` is realized by finitely
  many elements. The finite table they span embeds in `K` injectively on products, so the realized
  forward and reverse tables are the same in `K`.

**Consequence.** Binary descent to some group (`some-nonsurjunctive-group-gives-a-binary-one`, OPEN) is
equivalent to binary descent for one existentially closed group, and to binary descent for all of them. It
follows from the groupwise claim `surjunctivity-failure-descends-to-binary-alphabet`. Together with
`every-group-is-binary-surjunctive` it gives the conjecture (route `gottschalk-via-universal-binary-descent`).
So the goal can now be reached through a descent statement no stronger than the old one: the binary
witness may live on a different group.

This is elementary. The rectangle-clause proof already notes that existential failures pass to existentially
closed groups; the lane records it per size and reads off the descent equivalence.

## 4. Descent through `G × F`

### 4.1 Fibers

For a finite group `F`, `{0,1}^(G×F)` is `B^G` with `B = {0,1}^F`. Binary automata over `G × F` are exactly
the automata on `B^G` that commute with translating every fiber by the same element of `F`. Injectivity and
surjectivity are properties of the same map. The two constant fibers `0^F`, `1^F` are fixed by the
translation.

### 4.2 Equivariance is not the obstruction

Let `|F| = p` be prime. A tuple in `B^M` with a non-constant coordinate has trivial stabilizer in `F`. So an
`F`-equivariant rule is any rule on orbit representatives of such tuples, extended by translation, plus a
rule on all-constant tuples with constant values. A concrete choice is to normalize on the first
non-constant input, in a fixed order of `M` with the label `1` first. Local phase normalization is always
available.

### 4.3 A natural design and where it stops

Write non-constant fibers as (free orbit, phase). There are `N = (2^p - 2)/p` free orbits. Let `k` of them
carry the symbols of a strict pair `(mu, nu)` over `[k]`, and call every other fiber invalid.

1. **Default symbol.** Replace invalid cells by a default symbol `a_0`. The replacement depends only on the
   cell, so the replaced pattern is still constant on the forward table, and `Dec` holds for the relay
   values `mu(p'(s, .))`.
2. **Phase.** The demanded cell's phase travels on relay `1`: normalize on the first non-constant input,
   with label `1` first. The decoder computes the value of a fully invalid relay itself, as
   `mu(a_0, ..., a_0)`.
3. **What is lost.** An invalid demanded cell must be identified by a tag on relay `1`. The same rule runs
   at every relay, so each relay output must hold a `mu`-value and a tag.
   - The tags are: valid, two constant fibers, and the `N - k` invalid free orbits. That needs
     `k (N - k + 3)` output orbits, and only `N` exist.
   - Since `k (N - k + 3) - N = (k - 1) N - k^2 + 3k >= 2k` whenever `N >= k`, no prime `p` fits.
   - Filling every free orbit with valid symbols (product closure, `k | N`) still leaves three tags, so
     `3N` orbits are needed where `N` exist.
4. **Relation to Section 2.** A relay whose label-`1` cell is constant but which reads a free cell outputs
   a tagged free fiber. So the design does rewrite constant fibers, which Section 2 shows is necessary. It
   dies by the count, not by the barrier.

The count is about this design only. It is not a theorem about `G × F`.

## 5. Exact gap

- `some-nonsurjunctive-group-gives-a-binary-one` stays OPEN.
  - By Section 2, any construction must write on reserved sites or write reserved symbols at active sites.
  - By Section 4.3, sitewise tagging in orbit indices over `G × F` runs out of orbits.
- Directions not tried here:
  1. Store the reserved value of the demanded cell in the phases of neighbouring relays. Relative phases
     are translation-invariant data.
  2. Overgroups `K ⊇ G` of finite index where `K/G` acts by outer automorphisms. The fiber symmetry then
     moves sites, and constant fibers are no longer invariant site by site.
  3. Group change beyond finite index. The universal claim allows any group, for instance an existentially
     closed one.
