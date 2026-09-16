# Zaremsky Problem 2.19: swarm attack on the Z^3 * Z hole, 2026-09-16

- **Lane:** `swarm-zaremsky-2-19-embeddings-into-`.
- **Target:** `zaremsky-2-19-embeddings-into-brin-thompson-groups`.
- **Hole locked and worked:** `z3-free-z-does-not-embed-in-2v`, the
  Belk–Bleak–Matucci Conjecture 1.7 case `n = 2`. It carried the only live
  negative route for part (d), `some-gl-n-z-not-in-2v-via-z3-free-z`.
- **Full proofs:** `research/artifacts/raags-in-2v-via-full-shift-full-group-2026-09-16.md`.
- **Script:** `experiments/raag-conveyor-belts-full-shift-2026-09-16/belts.py`,
  with output `output.txt` in the same folder (31 s, single-threaded, `ALL OK`).
- **Outcome:** the hole is **false**. The claim is now REFUTED, and
  `some-gl-n-z-not-in-2v-via-z3-free-z` is invalidated. None of the five parts
  of 2.19 changes status, but the conditional no to (d) is dead.

## Setup

The graph had the chain

`z3-free-z-does-not-embed-in-2v` + `z3-free-z-embeds-in-gl8z`
⟹ `some-gl-n-z-does-not-embed-in-2v` ⟹ 2.19(d) answered no.

The literature gate found that the first link is false and was already refuted
in 2021.

## Literature gate (2026-09-16)

**Decisive source.** V. Salo, *Graph and wreath products in topological full
groups of full shifts*, arXiv:2103.06663v1 (11 Mar 2021). The LaTeX source was
downloaded and read on 2026-09-16.

- Abstract: "The group $\llb X \rrb$ embeds in the higher-dimensional Thompson
  group $2$V, so it follows that $2$V contains all RAAGs, refuting a conjecture
  of Belk, Bleak and Matucci."
- Introduction: "all (countable) RAAGs embed in $n$V for all $n \geq 2$."
- The arXiv API (2026-09-16) lists v1 only, with no journal reference. A Crossref
  query found no journal version. It found a different Salo paper on
  automorphism groups, *Graph and wreath products of cellular automata* (IJAC
  2024).
- Salo's preprint is unrefereed. Hence the self-contained reproofs below.

**Other sources consulted.**

- Zaremsky, *Some open problems*, version of July 12, 2026, Problem 2.19. It is
  quoted in the root claim, says "For 2V and up, things remain mysterious", and
  does not mention RAAGs.
- Belk–Bleak–Matucci, arXiv:1602.08635v1, Conjecture 1.7 and Theorem 1.1, as
  quoted in existing nodes. The journal version (Math. Proc. Cambridge Philos.
  Soc. 2020, per Salo's bibliography) was not checked.
- Callard–Salo, arXiv:2208.00685, already imported for distortion in `mV`.
- Kojima–Sheng, arXiv:2603.18410v3 (2026-05-23), abstract only. It is about `Q`
  and torsion in `nV`, not RAAGs.
- Bodart–D'Angeli–Perego–Rodaro, arXiv:2608.02111 (2026-08-03). It is about
  subgroups of `V` only.
- arXiv metadata search for "Brin-Thompson", newest first. Nothing disputing
  Salo's result was found.
- Not fetched, known only through Salo's introduction (unverified):
  - Kato, J. Algebra Appl. 17(8) (2018): RAAGs without `Z^d * Z` embed in
    `(d-1)V`.
  - Corwin–Haymaker, IJAC 26(8) (2016): a RAAG embeds in `V` iff it has no
    `Z^2 * Z`.

## What was proved (all unreviewed)

New nodes. Every claim is ESTABLISHED by `check.sh`.

| claim | route | kind |
|---|---|---|
| `full-shift-topological-full-group-embeds-in-2v` | `full-shift-topological-full-group-in-2v-proof` | direct proof (artifact Part A) |
| `every-raag-embeds-in-full-shift-topological-full-group` | `raags-in-full-shift-full-group-conveyor-belt-proof` | direct proof (artifact Part B) |
| `every-raag-embeds-in-brin-thompson-group-2v` | `every-raag-in-2v-via-full-shift-full-group` | composition |
| `z3-free-z-embeds-in-brin-thompson-group-2v` | `z3-free-z-in-2v-as-a-raag` | special case `K_3 ⊔ K_1` |
| `virtually-special-groups-embed-in-brin-thompson-group-2v` | `virtually-raag-groups-in-2v-via-finite-extensions` | D1–D3 |

There is also a second, citation-free route
`virtually-special-in-some-nv-from-2v` into the established
`virtually-special-groups-embed-in-some-brin-thompson-group`.

Edited: `z3-free-z-does-not-embed-in-2v` gained
`refuted_by: [z3-free-z-embeds-in-brin-thompson-group-2v]` and a 2026-09-16
Attempts entry.

**Part A: `[[{0,1}^Z]] ≤ 2V`.**

- Conjugate by `Φ(a,b) = …b_1b_0.a_0a_1…`.
- A cocycle with window `r` makes `F` canonical on the bricks of the uniform
  grid `G_r`, with image prefix lengths `(r-k, r+k)`.
- Refining by `G_{2r}` makes both partitions dyadic subdivisions. This point is
  "obvious" in Salo and spelled out here.

**Part B: `A_Γ ≤ [[{0,1}^Z]]` for finite `Γ`.**

- This specialises Salo's graph-product belt construction to vertex groups `Z`.
  The shared cell between non-commuting neighbours and the greedy chain from
  the right are Salo's. The one-letter-per-cell layout and the window are ours.
  (Referee correction; the original line said "not Salo's graph-product
  machine".)
- One belt type per vertex. The last cell of a belt is relocated onto the next
  block exactly when that block has a non-adjacent type.
- The cocycle has window `x_{[-4,3]}`.
- Adjacent types share no cells, so their generators commute.
- Faithfulness: take the greedy non-adjacent chain from the right of a reduced
  syllable word. On the chain configuration the head runs from the last cell of
  the last belt to the first cell of the first belt.

**Part D: finite extensions.**

- D1: `H ≤ nV` implies `H ≀ S_k ≤ nV`.
- D2: Kaloujnine–Krasner.
- So virtual embedding in a f.g. RAAG gives embedding in `2V`.
- In particular, every cubulated hyperbolic group embeds in `2V`, not merely in
  some `nV`.

**Part E: the limit of the method.**

- Every infinite-order `g` in a f.g. subgroup of `[[Σ^Z]]` satisfies
  `|g^n|_S ≥ n/(2K)`. The proof uses subadditivity of `max|c|`, an infinite
  head orbit from compactness, and Fekete.
- The graph already had a stronger version:
  `subshift-crossed-product-gl-has-no-distorted-elements`, which covers
  topological full groups of Cantor systems. So no new node was added for E1.
- Consequence: `H_3(Z)`, `BS(1,2)`, `SL_3(Z)` and `GL_n(Z)` (`n ≥ 3`) are not in
  `[[Σ^Z]]`. The full-shift route can never answer (c) or (d) yes.
- A side result from B + E1: `H_3(Z)` virtually embeds in no f.g. RAAG.

**Computation.** Exact integer checks.

- Bijectivity of every head map and commutation for adjacent types:
  - all periodic configurations of period `≤ 7` (`N = 2`), `≤ 6` (`N = 3`) and
    `≤ 5` (`N = 4`);
  - 3000 random periodic configurations of period 8–60 per graph.
- Faithfulness: all 305,466 reduced words of length `≤ 4` with `|exponent| ≤ 3`,
  and 4000 random words per graph against the normal form.
- Graphs: `K_2`, `2K_1`, `P_3`, `K_3 ⊔ K_1`, `P_4`, `C_4`.

## Approaches tried and where each dies

- **Prove the conjecture by the germ count** (2026-09-13 attempt). It dies
  because the belt embedding makes the three commuting generators have pairwise
  disjoint moved-point sets. Local triviality of part of `Z^3` is generic, so it
  yields nothing against the free letter.
- **Prove the conjecture by drift and invariant measures.** Not pursued: the
  statement is false.
- **Use the belt embedding to answer (d) yes (`GL_n(Z) ≤ 2V`).** It dies at E1.
  `[[Σ^Z]]` has no distortion elements, but `GL_3(Z) ⊇ H_3(Z)` does. A yes to
  (c) or (d) needs tape-rewriting elements, such as reversible Turing machines,
  not only head-moving ones.
- **Use RAAG subgroups of `GL_N(Z)` for a no to (d).** Dead, by
  `every-raag-embeds-in-brin-thompson-group-2v` and Part D. A no to (d) must use
  a subgroup that is not virtually in a RAAG: `H_3(Z)`, or an infinite Kazhdan
  subgroup such as `SL_3(Z)`.

## Stale text in nodes this lane did not edit

These are nodes other lanes own, so they were left unedited. Suggested
follow-ups:

- `some-gl-n-z-does-not-embed-in-2v`: its Attempts name
  `z3-free-z-does-not-embed-in-2v` as the most promising obstruction and the
  "Next target". That route is now invalidated. The remaining no-routes go
  through `H_3(Z)` (`heisenberg-group-embeds-in-no-brin-thompson-group`) or
  through Kazhdan subgroups.
- `every-gl-n-z-embeds-in-2v`: its Attempts say a yes here contradicts BBM
  Conjecture 1.7. That conjecture is now false, so there is no contradiction.
  The obstacle to a yes is `H_3(Z)` and property (T), not RAAGs.
- Root `zaremsky-2-19-embeddings-into-brin-thompson-groups`, status of (d):
  "A conditional no ... needs Z^3 * Z not to embed in 2V". That route is now
  invalidated by refutation. Status of (a): the cubulated case now lands in
  `2V` (`virtually-special-groups-embed-in-brin-thompson-group-2v`).
- `z3-free-z-embeds-in-gl8z`: its distinct_from text describes the refuted
  pairing. It is harmless.

## What remains open for 2.19

- **(a)** Hyperbolic groups that virtually embed in no RAAG, above all infinite
  hyperbolic Kazhdan groups. The only known no-route is
  `kazhdan-subgroups-of-brin-thompson-groups-are-finite`, i.e. the Haagerup
  side of Problem 2.7.
- **(c)** and **(d)** Both come down to whether `H_3(Z)` and `SL_3(Z)` embed in
  `2V`/`mV`.
  - A yes needs genuinely tape-rewriting elements. Callard–Salo record that even
    `H_3(Z)` in the automorphism group of a full shift is open (as quoted in
    `heisenberg-group-embeds-in-some-brin-thompson-group`; not re-read by this
    lane).
  - A no needs a new obstruction. Undistortion fails in `2V` (it has distortion
    elements), and RAAG subgroups are now ruled out. What remains is an argument
    that uses the Heisenberg relations themselves, or property (T).

## Referee (2026-09-16)

Adversarial referee and landing agent for this lane.

**What was checked.**

- **All files, read in full:**
  - the 11 new nodes;
  - the edit to `z3-free-z-does-not-embed-in-2v`;
  - the artifact, `belts.py`, `output.txt` and this note.
  - `git status` shows no unlisted files of this lane. The untracked
    `virtually-finite-cd-*` nodes belong to another lane.
- **Part A, re-derived by hand.**
  - The baker coordinates are right: `[u.v]` pulls back to `vC × u^R C`.
  - For `k ≥ 0` and for `k = -m`, `F` is canonical on each grid brick, with
    image prefix lengths `(r-k, r+k)`.
  - Refining to `G_{2r}` yields dyadic subdivisions on both sides, and the
    domain pieces are uniform subdivisions of the `G_r` bricks. Sound.
- **Part B, re-derived by hand.**
  - (P1)–(P3) and the orientation of the composition.
  - Disjointness of cell sets of distinct `u`-belts, including one- and
    two-sided infinite belts; `π_β` is a bijection in each case.
  - The four window rules, case by case against the definition.
  - Adjacent types share no cell: all three cases.
  - Lemmas 1–2, and that the chain configuration moves the head from
    `P_{k+1}` to `P_1`. This includes the check that the other syllables fix
    `P_p`, because `j_m ~ u_p` rules out both `u_p` and `u_{p-1}`.
  - Binary recoding.
  - The solver's "weakest step" (no collision of relocated cells) holds: a
    relocated cell is a `T` letter of a non-adjacent type, and at most one belt
    ends at `P-2`. Sound.
- **Parts D and E, re-derived.**
  - D: the wreath closure (`P_τP_ρ = P_{τρ}`, the conjugation formula,
    injectivity) and Kaloujnine–Krasner.
  - E: the compactness step `g^{J!} = id`, the counting bound `μ_n ≥ n/2`, and
    Fekete.
  - The side result that `H_3(Z)` virtually embeds in no RAAG.
  - The cited `subshift-crossed-product-gl-has-no-distorted-elements` does
    cover full groups of Cantor systems with periodic points, so the reference
    is accurate. Sound.
- **Computation.**
  - Re-ran `belts.py`; md5 matches, output `ALL OK`.
  - Wrote an independent script (referee scratchpad, not landed). It builds each
    head map from the *definition* (parse belts, relocate, cycle) rather than
    from rules 1–4, and compares against `belts.py`'s rule-based cocycle. It
    covers 64,000 (configuration, vertex) pairs on random periodic
    configurations of period 10–80 over `K_2`, `2K_1`, `P_3`, `K_3 ⊔ K_1` and
    the 5-vertex graph with edges 01, 23, 34, 14. All match.
- **Literature.**
  - Fetched arXiv:2103.06663 (abstract page: v1 only, 11 Mar 2021, no journal
    reference) and its LaTeX source. Every quote in the artifact is verbatim:
    the abstract, "all (countable) RAAGs embed in $n$V for all $n \geq 2$", "The
    way the definitions are stated, the following is obvious.", the RAAG
    theorem, and the commented "Restrictions" block with the Fekete hint.
  - The Kato and Corwin–Haymaker references agree with Salo's bibliography.
    They remain unverified at the source.
  - A web search for a journal version could not be run (search budget
    exhausted), so "no journal version" rests on the arXiv page and the
    solver's Crossref query.
- **Duplicates.** `bin/cairn search --similar` on all five new claims found no
  duplicate and no prior record of Salo's paper in the graph.

**What was changed.**

1. **Novelty.** Reading Salo's Section 3 shows that his graph-product proof
   already uses conveyor belts, a cell shared between neighbouring belts of
   non-commuting types, and the greedy non-commuting chain from the right. The
   artifact said Part B "borrows only the idea of belts and of moving a head",
   which is overclaimed. It now reads as a specialisation of Salo's construction
   to vertex groups `Z`, with a new concrete layout and a complete proof.
   Changed in the artifact, the route `raags-in-full-shift-full-group-conveyor-belt-proof`,
   the claim `every-raag-embeds-in-full-shift-topological-full-group`, and this
   note.
2. **`virtually-special-groups-embed-in-brin-thompson-group-2v`, examples.**
   - "Every virtually special group" is now "every finitely generated virtually
     special group". Non-compact special cube complexes can need infinite-graph
     RAAGs, which Part B does not cover.
   - The examples now cite the existing some-`nV` node.
   - The Haagerup reason for the property (T) exclusion is stated.
3. **`every-raag-embeds-in-brin-thompson-group-2v`.**
   - "The case n = 1 stays true" is now "the obstruction at n = 1 still holds".
     The converse direction is Corwin–Haymaker, which was not fetched.
   - "cannot answer 2.19(c)/(d)" is now "cannot give a yes to".
4. **Artifact, small precision fixes.**
   - Part C now says "finitely generated RAAG".
   - Part E: E1 is described as writing out Salo's Fekete hint, not as
     independent of it.

**More stale text, not edited** (in addition to the list above):

- `some-gl-n-z-embeds-in-no-brin-thompson-group`, Attempts: it presents BBM
  Conjecture 1.7 as a possible obstruction.
- `zaremsky-2-19d-every-gl-n-z-in-2v-resolved`, Couplings: RAAG subgroups could
  obstruct embeddings in 2V "if that conjecture holds". It does not hold.

**Verdict.**

- **Sound, landed with fixes.**
  - Both direct proofs (`requires: []`) are complete.
  - The refutation of `z3-free-z-does-not-embed-in-2v` is correct, and so is
    the resulting invalidation of `some-gl-n-z-not-in-2v-via-z3-free-z`.
- **Credit.** The results in Parts A–C are Salo's (arXiv:2103.06663v1,
  unrefereed). The graph's contribution is a complete, checked proof of what it
  uses, plus Parts D and E.
- **Unchanged.** No part of Zaremsky 2.19 changes status.
