# strict-rule-pairs-ascend-to-larger-alphabets --- swarm pass, 2026-09-16

Agent: `swarm-strict-rule-pairs-ascend-to-la`.

Target (was OPEN): if a forward and a reverse product table `(T_f, T_r)` admit strict rules over some alphabet of size
`k`, then they admit strict rules over every alphabet of size `n >= k`.

Outcome: **solved negative.**
- One 2 x 3 table pair admits strict rules exactly at the composite sizes. In particular it admits them at 4 symbols and
  not at 5.
- The target now carries `refuted_by`.
- The group-level consequence, which is all that the downstream routes used, stays open and is recorded as a new claim.

## 1. Setup and orientation

**Read or consulted this pass.**
- The target and its Attempts.
- `strict-rule-pairs-pass-to-product-alphabets`, `equal-label-table-is-strict-at-three-symbols-not-two`,
  `copy-codes-make-one-sided-table-identities-strict`, `passive-block-involution-codes-ascend`,
  `passive-fixing-injective-automata-are-surjective`, `ec-groups-share-the-nonsurjunctive-alphabet-sizes`,
  `surjunctivity-failure-descends-to-binary-alphabet`, `gottschalk-via-alphabet-ascent`,
  `linear-sofic-surjunctivity-via-formalizability-and-ascent`, `every-group-is-surjunctive-over-binary-power-alphabets`.
- Artifacts `research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md` (Sections 0, 5, 6),
  `research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md` (Section 7) and
  `research/artifacts/alphabet-ascent-and-binary-descent-2026-09-12.md`.

**Conventions** (boolean artifact, Section 0).
- There are label sets `S` and `M`, each containing `1`. A *table* is an arbitrary equivalence relation on the cells
  `S x M`; it need not be realized in a group.
- A rule pair `(mu, nu)` over an alphabet `A` consists of `mu : A^M -> A` and `nu : A^S -> A`.
- `Dec(T_f)`: `nu((mu(p(s,.)))_s) = p(1,1)` for every source assignment `p` constant on the classes of `T_f`.
- `Enc(T_r)`: `mu((nu(q(m,.)))_m) = q(1,1)` for every `q` constant on the classes of `T_r`.
- The pair is *strict* when `Dec(T_f)` holds and `Enc(T_r)` fails. `Adm(T_f, T_r)` is the set of `n >= 2` with a strict
  pair.

The target asks whether `Adm` is always upward closed. What was known before this pass:
- `Adm` is closed under multiples (product alphabets).
- Every classified 2 x 2 table has upward-closed `Adm`.
- Passive-block involution codes ascend.

**Duplicate search.** `bin/cairn search` and `bin/cairn search --similar` found no node with a non-monotone `Adm`. The
nearest hits were three nodes whose `Adm` is upward closed:
- `equal-label-table-is-strict-at-three-symbols-not-two`;
- `smallest-boolean-strict-core-is-a-one-sided-inverse`;
- `copy-codes-make-one-sided-table-identities-strict`.

## 2. What was proven

New claim `research/table-pair-strict-exactly-at-composite-alphabet-sizes.md`, with direct route
`research/table-pair-strict-exactly-at-composite-sizes-proof.md` (`requires: []`). The long version is in artifact
`research/artifacts/composite-size-strict-table-2026-09-16.md`.

**The pair.**
- `S = {1, a}` and `M = {1, b, c}`.
- `T_f` has the single nontrivial class `{(1,1), (1,b), (a,c)}`, and `T_r` is its transpose `{(1,1), (b,1), (c,a)}`.
- In network form:
  - `Dec`: `nu(mu(o,o,e), mu(f,g,o)) = o`;
  - `Enc`: `mu(nu(o,u), nu(o,v), nu(w,o)) = o`.

**Theorem.** `Adm(T_f, T_r)` is the set of composite numbers. The same holds for every reverse table with
`(b,1) ~ (1,1) ~ (c,a)` in which `(1,a)` and `(b,a)` are not equivalent; there are 10 such tables.

**Composite `n = |B| |C|`, with `|B|, |C| >= 2`.**
- The two-digit code: `mu(x_1,x_b,x_c) = (beta(x_c), gamma(x_1))` if `x_1 = x_b`, and `(beta(x_c), pi(gamma(x_1)))`
  otherwise, with `pi` fixed-point free; `nu(y_1, y_a) = (beta(y_a), gamma(y_1))`.
- `Dec` holds because relay `1` carries `gamma(o)` and relay `a` carries `beta(o)`.
- `Enc` fails: choose `q(1,a)` and `q(b,a)` with different `beta`-digits, so the sink sees `x_1 != x_b` and applies `pi`.

**Prime `n`: the rectangle lemma.**
- Put `D(x,z) = mu(x,x,z)`. `Dec` with `f = g` says `o` is a function of `(D(o,e), D(f,o))`.
- Take independent uniform variables and entropies in base `n`. Then
  `1 = I(O;UV) <= I(O;U) + I(O;V) = H(W) - I(X;Z|W) <= 1`, so both inequalities are equalities.
- So `D` has `n` elements in every fiber, and each fiber is the product of its projections: a rectangle of area `n`.
- At prime `n`, every fiber is a full row or a full column, so `D = h(x)` or `D = k(z)` with a bijection.
- In the first case `Dec` forces `nu = h^{-1} o pi_1`, and `Enc` holds on any reverse table with `(b,1) ~ (1,1)`. In the
  second case `Dec` forces `mu = k o pi_c` and `nu = k^{-1} o pi_a`, and `Enc` holds whenever `(c,a) ~ (1,1)`.
- So at a prime size every `Dec` solution agrees with a relabelled copy code on every input `Enc` reads, and none is
  strict for these reverse tables.

**Verification.** Script `experiments/composite-size-strict-table-2026-09-16/verify_composite_table.py --sat`, output
in artifact Section 5; all checks passed.
- Direct evaluation of the code at `n = 4, 6, 8, 9`, and the reverse-table family at `n = 4`.
- Exhaustive search at `n = 2`, and the rectangle lemma exhaustively at `n = 2, 3`.
- CaDiCaL: UNSAT at `n = 3, 5`, SAT at `n = 4`. `n = 7` was not decided within 10 minutes and rests on the proof.

**Graph edits.**
- **Target.** Essential edit to `research/strict-rule-pairs-ascend-to-larger-alphabets.md`: `refuted_by`, a REFUTED
  header keeping the original statement as history, and an Attempts bullet.
- **Invalidated routes.** This makes `gottschalk-via-alphabet-ascent` and
  `linear-sofic-surjunctivity-via-formalizability-and-ascent` INVALIDATED. Neither file was edited.
- **New open claim** `research/nonsurjunctive-alphabet-sizes-are-upward-closed.md`: `NS(G)` is upward closed for every
  group `G`. This is the group-level statement both invalidated routes actually used. It has an Attempts section.
- **New route** `research/gottschalk-via-upward-closed-nonsurjunctive-sizes.md` to `gottschalk-surjunctivity-conjecture`.
  It requires the new claim and `every-group-is-surjunctive-over-binary-power-alphabets`.

## 3. Approaches and where each dies

1. **Search for a positive proof by adding one symbol.** Every recorded extension is dead:
   - retraction;
   - the erasure symbol;
   - walls;
   - passive blocks. These ascend, but only for their own code class.

   This pass did not find a new one. The reason is now clear: at a prime size the forward identity can be rigid
   (only copy codes), while a composite size has room for a second digit. No one-symbol extension can exist in general.
2. **Census before theory.**
   - Enumerate table pairs up to label symmetry.
   - Discard two kinds of pairs whose `Adm` is already known:
     - abelian-realizable pairs, with `Adm = ∅`;
     - copy-code pairs, with `Adm` equal to every `n >= 2`.
   - SAT the rest at `n = 2..4`, then follow up the `NNY` pairs at `n = 5`.

   Results (log `experiments/composite-size-strict-table-2026-09-16/census-summary.txt`):

   | Tables | Sizes | Result |
   |---|---|---|
   | 2 x 2 | `n = 2..5` | 29 `NYYY`, 39 `NNNN`, no gaps |
   | 2 x 3 | `n = 2..4` | 121 `NNY` |
   | 2 x 3 `NNY` pairs | `n = 5` | 36 `N`, from four forward tables; 85 `Y` |
   | 3 x 2 | `n = 2..4` | 132 `NNY` |
   | 3 x 2 `NNY` pairs | `n = 5` | partial run, capped at 600 s: at least 109 processed, 19 `N`, 6 budget-exceeded, rest `Y` |

   The theorem's pair is among the 36 pairs with a gap at 5. The theorem does not depend on the census.
3. **Why the prime sizes die: rectangle rigidity.**
   - What is needed is the shape of the fibers of `D`, not only their sizes.
   - The Shannon chain gives the shape: equality forces conditional independence on each fiber, and that means product
     fibers.
   - Primality enters only in the last step, where a rectangle of prime area must be a full row or a full column.
   - This is the only step that is not a direct computation. It is a standard entropy argument, and it was checked
     exhaustively at `n = 2, 3`.
4. **Can the example say anything at group level?** No.
   - Any labelling in a group with `x_1 = 1` whose forward table contains `T_f` has `x_b = 1`.
   - Then its reverse table identifies `(1,a)` with `(b,a)`, which is exactly the coincidence the two-digit code avoids.
   - More fundamentally, a realized table pair with nonempty `Adm` would refute Gottschalk's conjecture (Theorem 1 of
     the boolean artifact). So realized-table ascent cannot be refuted by any cheaper example.
   - Where this dies as an attack on the group-level claim: a proof of `NS(G)` upward closed must use that the tables
     come from a group, or must change the tables, for instance by enlarging the memories.
5. **The passive-block reduction** (`passive-block-involution-codes-ascend`). General ascent was reduced to: every strict
   pair is equivalent to a copy code or to a passive-block involution code. The pair here is strict at 4 and not at 5,
   so its strict codes are neither kind. The reduction's hypothesis is false.
6. **Closure beyond multiples.** Product closure gives closure under multiples. The composite numbers are closed under
   multiples and not upward closed, so closure under multiples does not extend to upward closure.
7. **Group-level ascent, `k` to `k + 1`.** Not attacked beyond recording the state:
   - Passive extensions are dead by `passive-fixing-injective-automata-are-surjective`.
   - Existentially closed groups reduce the universal form to `NS_all` upward closed.
   - The smallest open instance is `2 ∈ NS(G)` implies `3 ∈ NS(G)`.

## 4. Literature (checked 2026-09-16)

Nothing consulted states or refutes table-level alphabet ascent. For the titles seen only in search listings, this rests
on titles and snippets alone.
- **Seen in search listings, not read:**
  - arXiv:2503.23435 (30 Mar 2025), "On Gottschalk's surjunctivity conjecture for non-uniform cellular automata";
  - arXiv:2410.17688, "Strongly sofic monoids, sofic topological entropy, and surjunctivity";
  - arXiv:2403.05998, "Generalized Gottschalk's conjecture for sofic groups and applications";
  - arXiv:2405.18287, "Stable finiteness of monoid algebras and surjunctivity";
  - arXiv:2511.06586 (Nov 2025), "Surjunctivity does not characterize cosoficity of invariant random subgroups".
- **Abstract fetched:** arXiv:1608.01738, J. Connelly and K. Zeger, "Linear Network Coding over Rings, Part I: Scalar
  Codes and Commutative Alphabets" (submitted 5 Aug 2016). It concerns linear codes over rings and not nonlinear
  single-demand codes like these.
- **Recalled, unverified:** solvability of general network coding problems is not monotone in the alphabet size.
  Nothing here uses it.

No novelty is claimed; the example is elementary.

## 5. What remains open

- `nonsurjunctive-alphabet-sizes-are-upward-closed`, the group-level ascent. It is now the prerequisite of the new
  Gottschalk route, and the linear-sofic route can be rebuilt over it.
- Whether realized table pairs have upward-closed `Adm`. This is vacuous if Gottschalk holds, and by Section 3.4 no
  example short of a counterexample to Gottschalk can refute it.
- Whether `Adm` can fail closure in other patterns, for example a set that is not a union of multiples of a few primes.
  The census gaps at 5 have not been classified beyond the one theorem.

## 6. Files

- `research/table-pair-strict-exactly-at-composite-alphabet-sizes.md` (new claim)
- `research/table-pair-strict-exactly-at-composite-sizes-proof.md` (new direct route)
- `research/nonsurjunctive-alphabet-sizes-are-upward-closed.md` (new open claim)
- `research/gottschalk-via-upward-closed-nonsurjunctive-sizes.md` (new route)
- `research/strict-rule-pairs-ascend-to-larger-alphabets.md` (edited: `refuted_by`, status text, Attempts)
- `research/artifacts/composite-size-strict-table-2026-09-16.md`
- `experiments/composite-size-strict-table-2026-09-16/`, containing:
  - `verify_composite_table.py`, `fastsat.py`, `scan.py`, `follow.py`;
  - `census-summary.txt`, `follow23_nny5.txt`, `follow32_nny5.txt`.

## Referee (2026-09-16)

**Checked.**
- *Scope.* The target quantifies over arbitrary table pairs, as in Section 0 of the boolean artifact (tables are
  arbitrary equivalence relations on cells), so a pair that no group realizes is a valid counterexample. The target's
  group-level consequence is correctly split off as the open `nonsurjunctive-alphabet-sizes-are-upward-closed`. The
  new route to Gottschalk is honestly open.
- *Direct proof, by hand.*
  - Step 1: the two-digit code satisfies `Dec(T_f)`, and the choice `beta(q(1,a)) != beta(q(b,a))` is available for
    every `T_r'`.
  - Step 2: the Shannon chain `1 = I(O;UV) <= I(O;U) + I(O;V) = H(W) - I(X;Z|W) <= 1`; uniformity and product fibers;
    at prime `n`, rows versus columns.
  - Step 3: both cases force `Enc(T_r')`. Case `D = h(x)` leaves `mu` free off the diagonal, which the sink never
    reads there.
  - Small cases: the census numbers and "at least 109" processed pairs for 3x2 match the output files.
- *Computation.* Reran `verify_composite_table.py --sat`: SAT at `n = 3` and `n = 5` is UNSAT and `n = 4` is SAT.
  Separately, in my own scratch code, I checked the code at `n = 4, 6, 8, 10`, for the splits `2x2`, `2x3`, `3x2`, `4x2` and `2x5`, and exhaustively checked the rectangle lemma
  at `n = 3`.
- *Non-realizability.* `x_1 = 1` and `x_1 x_1 = x_1 x_b` force `x_b = 1`.
- *Literature.* WebFetch spot-checks of the cited arXiv abstracts all match. Unfetched items are marked unverified.
- *Duplicates and discipline.* The new claim is distinct from the product-closure, copy-code and equal-label nodes. The
  route has `requires: []` and is complete. The new open claim has `## Attempts`. The committed target was edited only
  as a refutation needs.

**Changed.**
- *"Is a copy code" wording.* At prime sizes a `Dec` solution need not be a copy code, because `mu` is arbitrary off
  the diagonal in Case A. The wording now says it "agrees with a relabelled copy code on every input `Enc` reads". This
  is fixed in the target's Attempts bullet, the new claim's `distinct_from`, the artifact and this note.
- *Closure overclaim.* "No closure beyond multiples holds" became "closure under multiples does not extend to upward
  closure" in the claim, the artifact and this note. Other closure properties are left unsettled.
- *Entropy step.* The route now states the identity `I(X,Z;W) - I(X;W) - I(Z;W) = I(X;Z|W) - I(X;Z)` explicitly.
- *Not fixed, for the record.* Section 5 says "the linear-sofic route can be rebuilt over" the group-level claim. No
  such route was added. Rebuilding it should first re-check the countability hypothesis of
  `linear-sofic-group-algebra-is-stably-finite`.

**Verdict.** Sound. The refutation of fixed-table ascent is proven, and the group-level question stays open. Landed with
fixes.
