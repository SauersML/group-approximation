# Gottschalk surjunctivity conjecture: frontier swarm notes (2026-09-16)

Agent `hi-fron-gottschalk-surjunctivity-conje`, FRONTIER angle. Root: `gottschalk-surjunctivity-conjecture`.
Hole worked: `nonsurjunctive-alphabet-sizes-are-upward-closed` (locked 2026-09-16, unlocked at the end).
Nothing here is committed or independently reviewed.

## 1. Frontier map (dated 2026-09-16)

Read off `bin/cairn why gottschalk-surjunctivity-conjecture` on 2026-09-16. Live routes into the root and their open
prerequisites (locks as shown at that time):

- **Alphabet bridges.**
  - `gottschalk-via-upward-closed-nonsurjunctive-sizes`: `nonsurjunctive-alphabet-sizes-are-upward-closed` (this lane,
    locked) and `every-group-is-surjunctive-over-binary-power-alphabets`.
  - `gottschalk-via-binary-alphabet-descent`: `surjunctivity-failure-descends-to-binary-alphabet` and
    `every-group-is-binary-surjunctive` (locked by another agent).
  - `gottschalk-via-universal-binary-descent`: `some-nonsurjunctive-group-gives-a-binary-one` and
    `every-group-is-binary-surjunctive`.
  - Dead: `gottschalk-via-alphabet-ascent` (table-level ascent refuted by the 2 x 3 composite-size table).
- **Hosts.** `gottschalk-via-fg-simple-kazhdan-hosts` (`fg-simple-kazhdan-groups-are-surjunctive`),
  `gottschalk-via-finitely-generated-simple-groups`, `gottschalk-via-surjunctive-fixed-host`
  (`fixed-gottschalk-test-group-is-surjunctive`).
- **Rokhlin entropy.** `gottschalk-via-maximal-bernoulli-rokhlin-entropy`, `gottschalk-via-positive-rokhlin-entropy-for-every-group`,
  `gottschalk-via-positive-rokhlin-entropy-host`; all end in positivity or maximality of Rokhlin entropy for the tester
  host or for every group.
- **Duality and decoders.** `gottschalk-via-dual-surjunctivity-and-decoder-transfer`
  (`every-group-is-dual-surjunctive`, `strict-pairs-admit-post-surjective-decoders`),
  `gottschalk-via-countable-transitive-decoder-fiber`.
- **Measure and site laws.** `gottschalk-via-universal-bernoulli-preservation`,
  `gottschalk-via-uniform-single-site-output-law`, `gottschalk-via-unbalanced-table-memory-collisions`,
  `gottschalk-via-matrix-observable-extension`.
- **Other.** `gottschalk-via-quotient-closure`, `stable-three-factor-reduction-proves-gottschalk`.

Several of these routes are circular in the tree (their open prerequisite is proved only from the root), for example
`countable-transitive-decoder-fiber-from-gottschalk` and `matrix-observable-extension-from-surjunctivity`.

## 2. Choice of hole

`nonsurjunctive-alphabet-sizes-are-upward-closed`, in the notation `NS(G)` = sizes `n >= 2` carrying an injective,
non-surjective automaton over `G`, and `NS_all` = union over all groups.

- **Leverage.** It is one of the two bridges that turn a Kaplansky-type statement over binary-power alphabets into
  the full conjecture, and it would rebuild the invalidated `linear-sofic-surjunctivity-via-formalizability-and-ascent`.
- **Tractability, as judged at the start.** Its table-level form had just been refuted by a composite-size example
  that is realized in no group, the passive-fixing theorem had just landed, and the per-group closure under multiples
  was established. The smallest uncovered case `2 ∈ NS(G) ⇒ 3 ∈ NS(G)` looked like a concrete coding problem.
- **Rejected alternatives.** `every-group-is-binary-surjunctive` was locked by another agent; the Rokhlin holes need
  positivity of Rokhlin entropy for a nonsofic host, which no current method gives; the duality and site-law holes
  are circular in the tree.

## 3. State of the art and literature checked

**Known theorems used as background** (standard, not re-verified here): Gottschalk's question (1973); surjunctivity
of residually finite groups (Lawton, recorded in Gottschalk 1973); of amenable groups (Ceccherini-Silberstein,
Machì, Scarabotti 1999, via the Garden of Eden theorem); of sofic groups (Gromov 1999, Weiss 2000). Every candidate
counterexample is therefore nonsofic, and `NS(G)` is empty for every sofic `G`, so ascent is vacuous on every group
where anything is known.

**Sources fetched this session** (abstract pages through `export.arxiv.org`, since `arxiv.org` was blocked for the
fetcher):
- Doucha, Gismatullin, "On dual surjunctivity and applications", arXiv:2008.10565 (v1 24 Aug 2020, v2 26 Oct 2020).
  Abstract: dual surjunctive groups satisfy Kaplansky's direct finiteness conjecture over all fields of positive
  characteristic; closure of dual surjunctivity under ultraproducts, elementary equivalence and some semidirect
  products. It does not state an alphabet-size ascent, nor that dual surjunctivity implies surjunctivity.
- Phung, "Weakly surjunctive groups and symbolic group varieties", arXiv:2111.13607 (v1 26 Nov 2021, v2 5 Dec 2021).
  Abstract: weakly and linearly surjunctive groups, a reversibility theorem for injective endomorphisms of symbolic
  group varieties, evidence on Kaplansky's stable finiteness. No ascent between alphabet sizes in the abstract.
- Titles and abstracts listed in `research/artifacts/composite-size-strict-table-2026-09-16.md` (arXiv:2503.23435,
  2410.17688, 2403.05998, 2405.18287, 2511.06586, 1608.01738) were not re-fetched here; I treat their content as
  unverified by me.

**Search outcome.** The session's web-search budget ran out (tool reported 200 of 200 calls used). In what was
searched, I found no source that proves or disproves that the set of alphabet sizes at which a group fails
surjunctivity is upward closed, and no source on removing an odd prime from a failing size. The graph's own
records (`strict-rule-pairs-ascend-to-larger-alphabets`, the formalizability alphabet-bridge artifact
`research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md`, Section 7) agree that ascent is
open. This is a search result, not a proof of absence.

**What the graph already has on the hole** (2026-09-16):
- `ec-groups-share-the-nonsurjunctive-alphabet-sizes` (established): `NS(G)` is closed under multiples, and
  `NS(K) = NS_all` for existentially closed `K`.
- `passive-fixing-injective-automata-are-surjective` (established): padding with reserved symbols that stay in place
  and are never written at original sites gives only surjective automata.
- `table-pair-strict-exactly-at-composite-alphabet-sizes` (established): table-level ascent fails, with an
  unrealizable example.
- Linear witnesses in characteristic two descend to two symbols over `G × P`, `|P|` odd
  (`modular-matrix-failures-descend-to-scalars-over-g-times-p`).
- Rokhlin entropy: by Seward's per-group formula the sizes with a Rokhlin deficit are upward closed, and a strict
  automaton creates a deficit at an amplified size (`strict-automaton-lowers-bernoulli-rokhlin-entropy`). No converse
  from a deficit back to an automaton is known, so this gives nothing on `NS(G)`.

## 4. What was proved

No proof of ascent, and no counterexample. What is proved is small and elementary:

**4.1 A weaker bridge, with routes (research nodes, checker exit 0).**
- Claim `some-nonsurjunctive-group-gives-a-binary-power-one`: if `NS_all` is nonempty then `2^j ∈ NS_all` for some
  `j >= 1`.
- Route `gottschalk-via-binary-power-nonsurjunctive-witness`: this claim plus
  `every-group-is-surjunctive-over-binary-power-alphabets` gives the root. The conjecture is equivalent to the
  conjunction, since the conjecture makes `NS_all` empty.
- Routes into the claim from both recorded bridges: `binary-power-witness-from-upward-closed-sizes` (upward closure
  in one group) and `binary-power-witness-from-binary-witness` (universal binary descent).
- Why it is worth a node: it is implied by both bridges and by neither known to be equivalent to it. So a proof may
  mix ascent, descent and change of group. Its content is the removal of an odd prime from a failing size (4.2).

**4.2 Odd-part form.** `NS_all` is closed under multiples, so if `2^i m ∈ NS_all` with `m` odd then
`2^(i') m ∈ NS_all` for all `i' >= i`. The claim asks that the odd part can be removed for some `i'`.

**4.3 Lemma (regrouping moves keep the radical).** For groups `G <= H`:
1. `NS(G) ⊆ NS(H)` (extend the rule by the same memory; `surjunctivity-passes-to-subgroups`).
2. If `[H:G] = m` is finite and `n ∈ NS(H)`, then `n^m ∈ NS(G)`.
3. `n ∈ NS(G)` implies `n l ∈ NS(G)` for every `l >= 1` (`ec-groups-share-the-nonsurjunctive-alphabet-sizes`).

*Proof of 2.* Pick a right transversal `T`, so `H = ⊔_{t ∈ T} G t`, and send `x ∈ B^H` to `X ∈ (B^T)^G`,
`X(g)(t) = x(g t)`. For `g_0 ∈ G`, `(g_0 x)(g t) = x(g_0^(-1) g t)`, so this homeomorphism is `G`-equivariant. A
cellular automaton over `H` is continuous and `G`-equivariant on `(B^T)^G`, hence a cellular automaton over `G` by
Curtis–Hedlund–Lyndon; injectivity and non-surjectivity are unchanged. `|B^T| = n^m`. ∎

Each move sends `n` to a size divisible by every prime dividing `n`. So the closure of an odd failing size under
these moves contains no power of two. Any proof of 4.1 from an odd witness needs an alphabet change that is not a
regrouping, necessarily nonlinear (linear constructions over `F_p` produce only sizes `p^d`).

**4.4 Lemma (starred shears are reversible).** Let `A` be a finite abelian group, `R` a finite set of reserved
symbols, and `f` an automaton on `A^G` with memory `S_f`. On `((A × A) ⊔ R)^G` define `E_f` by: keep every
`R`-site; at a site `g` holding `(u(g), v(g))`, replace `v(g)` by `v(g) + f(u)(g)` if `g S_f` contains no `R`-site,
and otherwise keep it. `E_f` does not change the `R`-sites or the first track, and the condition reads only those,
so `E_(-f) ∘ E_f = id`. The mirror shear, writing the first track from the second, is reversible in the same way.
The track swap at non-reserved sites is an involution. So every word in starred shears and
swaps is a bijective automaton.

*Where it dies.* The swindle `Θ(x, y) = (y + τ(x), x − σ(y + τ(x)))` for a strict pair `σ τ = id` maps
`A^G × {0}` onto `τ(A^G) × {0}`, which gives strictness on a sub-alphabet. Its starred version, applied to
configurations with second track `0` off `R`, leaves second track `u − σ(y)` at sites whose `σ`-window avoids `R`,
and `u` at the other non-reserved sites, where `y` is `τ(u)` at sites whose `τ`-window avoids `R` and `0` at the
other non-reserved sites. This vanishes where the `σ ∘ τ` window avoids `R`, but not on the annulus around the
reserved sites. So `(A × {0}) ⊔ R` is not invariant, and the residue carries information on the annulus.

## 5. Approaches tried and where each dies

Throughout, `τ` on `A^G` is injective and not surjective, `|A| = k`, and `σ` is a decoder with `σ τ = id`. The target
is a strict automaton on `(A ⊔ D)^G`, most often `D = {*}`.

1. **Compressing embeddings.** An injective automaton from a larger full shift into a smaller one would let one
   compose with `τ`. Impossible: constant configurations are the `G`-fixed points and go to fixed points, so
   `|B| <= |A|`. For finite-index `H`, counting `Fix_H` gives the same bound.
2. **Product splittings over `G × P`.** A splitting `B^(G×P) ≅ W × V` with a strict automaton on `V` at a multiple of
   `k` would do, with `V = C^G` and `k | |C|`. A `G`-conjugacy preserves `G`-fixed points:
   `|Fix_G B^(G×P)| = (k+1)^|P|` on the left, `|Fix W| · |C|`, a multiple of `k`, on the right. Since
   `gcd(k, k+1) = 1` and `k >= 2`, no such conjugacy exists. The linear
   Maschke splittings (`binary-shifts-over-odd-fibers-split-off-the-augmentation-shift`) have no nonlinear analogue
   at coprime sizes.
3. **Direct-sum trick.** Linear ascent is trivial (`τ ⊕ id`). Nonlinearly `A ⊔ D` is not a product, and the corner
   monoid has no complement. Every design must mix the two sets of symbols.
4. **Reversible ∘ passive-fixing composites.** Surjective by `passive-fixing-injective-automata-are-surjective`, since
   composing with a bijective automaton does not change surjectivity.
5. **Walls and bands** (recorded in the formalizability artifact, Section 7, item 3). Raw output in a band around
   stars, `τ`-values far away. The decoder window at the inner edge of the far region reads band values that were
   output raw, not as `τ`-values. Enlarging the band moves the annulus without closing it; outputting both needs a
   product alphabet in the band.
6. **Filling with a default symbol.** `x ↦ (τ(F(x)) off Z, * on Z)`, `F` fills stars by `a_0`. The values `τ(F(x))`
   on `Z` are lost; they are exactly one `A`-track per star, and the star symbol has room for none.
7. **Post-surjective decoder with a correction track.** `R(u, v) = (τ(σ(u) + v 1_(N(u))), v 1_(G∖N(u)))`: again one
   track short. Conjugating by reversible automata never changes post-surjectivity, so it cannot supply the track.
8. **Garden-of-Eden markers.** Write `*` at a site where the would-be output together with a missing pattern forces a
   symbol. Translates of the pattern overlap, the saved symbol has `k - 1` values while `*` records one bit, and
   there is no global room. It dies at overlaps.
9. **Retraction-intertwined designs** `φ Φ = ψ φ` with `φ` a factor onto a smaller shift. They force `ψ` to fix the
   image of the constant star configuration and `{z_0, *}^G` to be invariant. No contradiction, no construction.
10. **Swindle as sub-alphabet invariance.** `NS(G)` is the set of `|D|` such that some bijective `Θ` on some `C^G`
    maps `D^G` strictly into itself. With `D = (A × {0}) ⊔ R` the starred swindle (4.4) leaves a residue on the
    annulus. This restates the problem; it does not solve it.
11. **Polymorphism and product closure.** Reach only `k^j` and multiples; with 4.3, nothing coprime.
12. **Additive closure, primality, reaching a power of two.** `k, l ∈ NS ⇒ k + l ∈ NS`, `k l ∈ NS ⇒ k ∈ NS or
    l ∈ NS`, and the claim of 4.1 each meet the same one-extra-symbol mixing step as `k ⇒ k + 1`.
13. **Table census.** On realizable tables whose table group is small it is vacuous. Small table groups are sofic,
    and sofic groups have no strict automaton, so the admissible set is empty.
14. **Rokhlin entropy.** Deficit sizes are upward closed per group, but no deficit-to-automaton converse is known.
    A strict automaton on any group forces every free ergodic action of the tester host to have zero Rokhlin
    entropy (contrapositive of the established `positive-rokhlin-entropy-on-one-host-proves-gottschalk`). That is a
    statement about measurable actions, not about automata at other alphabet sizes.
15. **Autonomous star dynamics.** Designs whose output star set is `ψ(Z)` for a bijective automaton `ψ` on
    `{0, 1}^G` fixing all-stars. Injectivity on configurations with finitely many non-star sites forces
    `|ψ(Z)^c| >= |Z^c|`. Over nonamenable `G` I could not rule out a bijective `ψ` that never lowers and sometimes
    raises this count, so this class is neither excluded nor realized. The case `ψ = id` is the passive-fixing theorem.

## 6. What to try next

1. **Smallest honest test: `2 ∈ NS_all ⇒ 3 ∈ NS_all`, over any group.** The universal form is enough for the route, so
   the group may change. Look for a group `H ⊇ G` and a strict automaton on `{0, 1, *}^H` whose stars move. The
   passive-fixing theorem and item 15 of Section 5 say the star set must change, and not by a count-preserving
   bijection.
2. **Settle item 15.** Is there a bijective automaton `ψ` on `{0,1}^G`, fixing the all-ones configuration, that never
   decreases and sometimes increases the number of zeros of finitely supported configurations? If no such `ψ`
   exists over any group, the whole class of autonomous-star designs is dead, which is a clean obstruction worth a
   node. If one exists over a nonamenable group, it is the room the annulus needs.
3. **Closing the annulus with a spare track.** 4.4 gives reversible starred shears on `((A × A) ⊔ R)^G`. Over the
   larger alphabet `(A × A) ⊔ R`, the annulus residue fits in the second track. The question is whether some word in
   starred shears, swaps and star-moving gates keeps `(A × {0}) ⊔ R` invariant and strict. A positive answer gives
   `k ∈ NS ⇒ k + |R| ∈ NS` for every `|R|`, hence upward closure, through the sub-alphabet characterization of item 10.
4. **Odd-part removal for linear odd-characteristic witnesses.** Test 4.1 on the first case not covered: a strict
   automaton linear over `F_3`. Any construction reaching a power of two changes characteristic nonlinearly. Even a
   conditional version, from `F_3`-linear failure plus a structural hypothesis on the group, would be new.
5. **Deficit-to-automaton converse at large sizes.** An eventual version of ascent (every sufficiently large size, or
   every large power of two) already suffices for 4.1. Per group, Rokhlin deficit sizes are upward closed. A converse
   that builds a strict automaton from a Rokhlin deficit at a large size, even on the tester host only, would give 4.1.
