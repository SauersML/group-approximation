---
rg: 2
id: strict-automata-below-twice-the-minimum-have-one-sink-class
kind: claim
title: Below twice the least failing size a strict automaton has one primitive sink class, so one letter above the minimum every strict automaton is robustly primitive unless NS(G) is cofinite
distinct_from:
  transition-digraph-capacity-lifts-give-nonsurjunctive-sizes: that turns class sizes of one strict automaton into sizes in NS(G) going up, and notes that a singleton class makes NS(G) cofinite; this proves that below 2 min NS(G) the class structure is forced (one primitive sink class, upsets of sizes in NS(G)), and that at min NS(G) + 1 every digraph that is not strongly connected, for any power, has a singleton class.
  separated-omitted-patterns-make-nonsurjunctive-sizes-cofinite: that gets cofiniteness from an omitted letter or a separated omitted pattern, both of which strict automata never have; this gets cofiniteness from one non-strongly-connected power of one strict automaton at size min NS(G) + 1, a condition that is not known to be empty.
  passive-fixing-injective-automata-are-surjective: that kills ascents in which the added letters are held in place; this also kills ascents in which the added letter is never destroyed, and shows that ascents in which it is never created are strict only if they already make NS(G) cofinite.
  nonsurjunctive-alphabet-sizes-are-upward-closed: that asks for every size above a failing one; this classifies what a witness of the first missing step n0 + 1 can look like, and does not produce one.
  block-permutation-transitions-force-divisible-classes: that is an invariant of letter-level moves that stops the odd part of g(τ) from dropping; this is a constraint on the digraph of any strict automaton near the least failing size, obtained by descent along upsets, which that claim lists as a surviving move.
  finite-injective-charge-noncreation-forces-surjectivity: that forces surjectivity from one zero-charge symbol that is never created; here the never-created letter is the unique letter outside a strict sink class, and the conclusion is a size statement, not surjectivity.
artifacts:
  - experiments/sink-class-structure-2026-09-17/check_sink_structure.py
---

**ESTABLISHED** by `one-sink-class-below-twice-the-minimum-proof`. Elementary. The only import is the two-level and gcd
forms of `transition-digraph-capacity-lifts-give-nonsurjunctive-sizes`. The descent lemma used (Step 1 of the route) is
proved in full there. It is the upset descent of the wave-18 branch `strict-automaton-upsets-give-smaller-nonsurjunctive-sizes`,
which is not in this tree, so it is reproved rather than imported.

**Setting.**
- `G` is any group and `NS(G)` is the set of alphabet sizes that carry a strict automaton over `G`. A strict
  automaton is an injective cellular automaton that is not surjective. Assume `NS(G) ≠ ∅` and put `n0 = min NS(G)`.
  Then `n0 >= 2`, since the only automaton on one letter is the identity of a point.
- `Ψ(x)(g) = μ((g^(-1)x)|_M)` with `1 ∈ M` finite. The transition digraph is `R(Ψ) = {(x(g), Ψ(x)(g))}` on `A`.
- An *upset* is `U ⊆ A` closed under `R(Ψ)`, i.e. `x(g) ∈ U` implies `Ψ(x)(g) ∈ U`. A *sink class* is a strongly
  connected component with no arc leaving it.
- A letter `*` is *never created* by `Ψ` if `Ψ(x)(g) = *` implies `x(g) = *`, i.e. `A \ {*}` is an upset.
- `Ψ` is *robustly primitive* if `R(Ψ^p)` is strongly connected for every `p >= 1`. This forces every `R(Ψ^p)` to be
  primitive (item 1).

**Theorem.** Let `Ψ` be strict on `A^G`, `|A| = m`.
0. **Descent.** If `Φ` is injective, `U` a nonempty upset of `R(Φ)`, and `Φ|_(U^G)` is onto `U^G`, then `Φ` is onto.
   So every nonempty proper upset of every `R(Ψ^p)` has size in `NS(G)`, hence at least `n0`.
1. **Sinks.** For every `p`, the sink classes of `R(Ψ^p)` are disjoint, and either there is exactly one or each has
   size in `NS(G)`, so there are at most `m / n0` of them. Every sink class `C` of period `d` has `d n0 <= |C|`.
   If all powers are strongly connected, all are primitive.
2. **Below twice the minimum.** Let `m < 2 n0`. For every `p >= 1`:
   - `R(Ψ^p)` has exactly one sink class `C_p`, and it is primitive;
   - every nonempty upset of `R(Ψ^p)` contains `C_p`;
   - if `C_p ≠ A`, then `|C_p| ∈ NS(G) ∩ [n0, m)`, fewer than `n0` letters are transient, and `Ψ^p` restricted to
     `C_p^G` is strict;
   - there is no *exact* proper sub-alphabet `V`, meaning one with both `V` and `A \ V` upsets. In general an exact
     `V` has both `|V|` and `m - |V|` in `NS(G)`.
3. **The second failing size.** Let `m < 2 n0` and `NS(G) ∩ (n0, m) = ∅`, e.g. `m` the second element of `NS(G)`.
   Then for every `p`, `R(Ψ^p)` is either strongly connected or has exactly two classes: the sink `C` with `|C| = n0`,
   and a strongly connected transient class `T` with `|T| = m - n0`. In the second case `n0 a + (m - n0) s ∈ NS(G)` for
   `1 <= s <= a`. Also `NS(G)` contains every large multiple of `gcd(n0, m)`, and is cofinite if `gcd(n0, m) = 1`.
4. **One letter above the minimum.** Let `m = n0 + 1`. Either `Ψ` is robustly primitive, or there is a single letter `*`
   and some `p` with all of the following:
   - `*` is never created by `Ψ^p`, and `{*}` is a singleton class of `R(Ψ^p)`;
   - `Ψ^p` restricted to `(A \ {*})^G` is strict at the minimal size `n0`, so it is itself robustly primitive;
   - `Ψ^p(*^G) = *^G`, and `*` is destroyed in some context.
   In the second case `g(Ψ^p) = 1`, and `NS(G)` contains every `n >= n0^2 + 1` and every `n0 a + s` with `1 <= s <= a`.
   In particular it contains every large power of two.
5. **Consequences.**
   - **(a) Bridge from one digraph.** If some group has `n0(G) + 1 ∈ NS(G)` witnessed by a strict automaton that is not
     robustly primitive, then `some-nonsurjunctive-group-gives-a-binary-power-one` holds with that group.
   - **(b) Under the binary-power prerequisite.** If `every-group-is-surjunctive-over-binary-power-alphabets` holds, no
     `NS(G)` is cofinite. So over every group, every strict automaton on `n0(G) + 1` letters is robustly primitive. More
     generally the same holds at the second failing size `m2 < 2 n0` whenever `gcd(n0, m2)` is a power of two.
   - **(c) Ascent designs at the minimum.** Let `τ` be strict on `n0` letters and `Ψ` injective on `A ⊔ {*}` extending it.
     - If `*` is never destroyed, `Ψ` is onto (item 0 with `U = {*}`).
     - If the old letters are never turned into `*` (`A` is an upset), then either `Ψ` is not strict, or `NS(G)` is
       already cofinite by item 4.
     - So the first step `n0 → n0 + 1` of `nonsurjunctive-alphabet-sizes-are-upward-closed` can be taken only by a
       robustly primitive automaton, or by one that proves the binary-power bridge on its own.

**Why it matters.**
- It extends the wave-18 normal form, which covers only `m = n0`, to the whole window `n0 <= m < 2 n0`. For the
  upward-closure hole it turns the first missing step, `n0 + 1 ∈ NS_all` at an existentially
  closed group, into a dichotomy. Either the witness is robustly primitive (every power strongly connected), or the
  witness by itself proves the binary-power bridge.
- **Precise obstruction.** Every ascent design `n0 → n0 + 1` whose added letter is sitewise distinguishable dies or
  collapses. This covers a never-destroyed letter, a never-created letter, an exact letter, and a transient letter of
  any power. It dies at item 0, or collapses into the singleton class of item 4.
  - The invariant is the upset lattice of `R(Ψ^p)`: all its proper members have sizes in `NS(G)`, hence size `n0`.
  - Under the flagship route's second prerequisite, only robustly primitive designs remain. This is the same normal
    form the minimal size already has, now one letter higher.
- **Redirect.** A search for a binary-power witness can start at size `n0 + 1` and ask only for a strict automaton with
  one never-created letter over a strict `n0`-core, which is a sitewise-local condition. Strictness is not automatic
  there. A bijective `Ψ` with `A` an upset and `Ψ|_(A^G)` strict is not excluded, and would then make `{*}` an upset of
  `Ψ^(-1)`, which item 0 allows.

**Where it stops.**
- Nothing here produces `n0 + 1 ∈ NS(G)`. The robustly primitive case is untouched and carries the whole of the
  upward-closure hole at its first step, in every world where binary powers are surjunctive.
- Above `2 n0`, several sink classes and exact splittings are allowed, and item 2 says nothing.
- Item 3 needs the gap `NS(G) ∩ (n0, m) = ∅`. Without it the transient part can split into classes whose sizes the
  argument does not control.
