# Zaremsky 3.6 (are braid groups CAT(0)?): special case / strengthening swarm, 2026-09-16

Agent `hi-spec-zaremsky-3-06-braid-groups-cat`. Root `zaremsky-3-06-braid-groups-cat0`.
Hole locked and worked: `every-braid-group-is-cat0`.

## Angle

Special case / strengthening. Find the best dated partial results, then prove a
new implication or a new class. The result is an implication between the variants
"B_n is CAT(0)" for different `n`: **CAT(0) passes from `B_{n+1}` to `B_n`.**
This turns the "yes" direction into a statement about infinitely many `n`, and it
propagates any "no" at one `n` to every larger `n`.

## State of the art (dated sources)

- **n ≤ 6.** Haettel–Kielak–Schwer, "The 6-strand braid group is CAT(0)",
  arXiv:1304.5990v2 (April 2013). Full text fetched and searched 2026-09-16.
  - They prove the diagonal links of `|NCP_n|` are CAT(1) for `n ≤ 6` (Theorem
    4.17, Corollary 4.18), by embedding into spherical buildings of type A.
  - Brady–McCammond's criterion then gives a geometric action of `B_n`.
  - In the graph: `braid-groups-on-at-most-six-strands-are-cat0`.
- **n = 7.** Jeong, "The seven-strand braid group is CAT(0)", arXiv:2009.09350v1
  (September 2020). Full text fetched and searched 2026-09-16 (Corollary 14).
  Not imported into the graph.
- **Criterion and n = 5.** Brady–McCammond, "Braids, posets and orthoschemes",
  arXiv:0909.4778v1 (September 2009). Abstract only: the PDF download failed
  (connection reset). Their Theorem 5.10, Lemma 5.8 and Proposition 8.3 are
  known here only as quoted by HKS (see
  `every-braid-group-is-cat0-via-diagonal-links`).
- **Open for n ≥ 8.** Bregman–Libgober–Zhu, "CAT(0) geometry of complex curve
  complements and families", arXiv:2411.18067v1 (November 2024). Full text
  fetched and searched 2026-09-16. It says CAT(0)-ness "is open even for finite
  type Artin groups such as braid groups B_n, n > 7".
- **Recency check.** The arXiv API was queried on 2026-09-16 with
  `abs:braid AND abs:"CAT(0)"` and with `abs:"braid groups" AND abs:"CAT(0)"`,
  sorted by date. The only newer hit is Gavazzi–Martin, "A Deligne complex for
  virtual Artin groups", arXiv:2607.24367v1 (July 2026), on virtual Artin groups,
  which does not bear on `B_n`. The abstract of Barre–Pichot, arXiv:1912.13391v1
  (December 2019), concerns a finite-index subgroup of `B_4/Z(B_4)` only. No
  source announces `B_8` CAT(0) or states monotonicity in `n`. The WebSearch
  budget was exhausted, so only the arXiv API and direct fetches were used.
- **Graph state.** `noncrossing-partition-diagonal-links-are-cat1` records the
  turning-face search: 22268 candidate chains at `n = 8`, so Theorem R as stated
  cannot reach `n = 8`.

## What was proven (new claim with a complete direct proof)

**Theorem M** (`braid-cat0-passes-to-fewer-strands`, established by the
`requires: []` route `braid-cat0-passes-to-fewer-strands-proof`, artifact
`research/artifacts/braid-cat0-fewer-strands-2026-09-16.md`). If `B_{n+1}` acts
geometrically on a complete CAT(0) space, so does `B_n`.

The proof has two independent parts.

1. **Proposition G (general CAT(0) geometry).**
   - Setup: `G` acts geometrically on a complete CAT(0) space, and
     `C_G(γ) = H × ⟨z⟩` with `z` of infinite order.
   - Conclusion: `H` acts geometrically on a complete CAT(0) space.
   - Ingredients:
     - `C_G(γ)` acts geometrically on `Min(γ)`. The finite-return-set argument is
       written out in full (artifact §§1–2).
     - A central `z` of infinite order is hyperbolic on `Min(γ)`.
     - `Min(z) = Y × R` (Bridson–Haefliger II.6.8), and `G/⟨z⟩` acts
       geometrically on `Y` (artifact §3). Properness on `Y` is checked
       explicitly: for suitable `m`, `gz^m` moves a point of a compact ball
       `B̄((y,0), 1 + |z|)` into it.
2. **Proposition B (braid combinatorics).** `C_{B_{n+1}}(ι(Δ²_n)) = ι(B_n) × ⟨Δ²_{n+1}⟩`
   for `n ≥ 2`. The proof is elementary, from configuration spaces (artifact §4).
   - Conjugation permutes winding numbers `lk_ij`. The total windings
     `tot_k(ι(Δ²_n))` are `n − 1` for `k ≤ n` and `0` for `k = n+1`, so a
     centralizing braid fixes the last strand.
   - Peel off `ι(f(β))`, where `f` forgets the last strand and `f∘ι = id`. The
     remainder lies in the free group `ker f` (Fadell–Neuwirth) and commutes with
     `δ = ι(Δ²_n)⁻¹Δ²_{n+1} ∈ ker f`.
   - `lk_{1,n+1}(δ) = 1`, so `δ` is not a proper power, and the remainder is a
     power of `δ`.

**Corollaries** (artifact §5).
- The set of `n` with `B_n` CAT(0) is an initial segment: `{1, …, N}` with
  `N ≥ 7`, or everything.
- `every-braid-group-is-cat0` ⟺ `braid-groups-cat0-for-infinitely-many-strands`.
  The new reduction route is `every-braid-group-cat0-from-infinitely-many-strands`.
- `some-braid-group-is-not-cat0` ⟺ `B_n` is not CAT(0) for all large `n`. An
  obstruction at `n_0` propagates to all `n ≥ n_0`.
- If `B_n` is CAT(0), so are `B_n/⟨Δ²_n⟩` and `P_n/⟨Δ²_n⟩`.

**What is new.**
- No primary source read here (HKS, Jeong, BLZ in full; BM abstract) states
  Theorem M or any monotonicity in `n`.
- HKS list centralizer splitting only as a general property of CAT(0) groups.
- The statement is about arbitrary geometric actions, not a specific complex.
  So a future proof for a sparse family of `n`, or an obstruction at a single
  `n`, gets the other `n` for free.
- The ingredients are textbook, so this may be folklore among experts. No
  statement of it was found, and the note and artifact say so.

**Small cases tested.**
- By hand: `n = 2` gives `C_{B_3}(σ_1²) = ⟨σ_1⟩ × ⟨Δ²_3⟩`, consistent with the
  curve-stabilizer picture.
- By computer: `experiments/braid-cat0-fewer-strands-2026-09-16/centralizer_check.py`
  uses the faithful Artin action on `F_{n+1}`, which is independent of the proof.
  - It checked every braid of word length at most `12, 6, 5` in `B_3, B_4, B_5`
    that commutes with `(σ_1⋯σ_{n−1})^n`: `79`, `579` and `1579` elements.
  - All of them fix the last strand and lie in
    `⟨Δ²_{n+1}⟩·⟨σ_1, …, σ_{n−1}⟩`.
  - Output is in `results.txt` in the same folder.

## Approaches and where they die

1. **Strengthen Theorem R at `n = 8` (not pursued).**
   - Idea: quantify condition IV over all opposite universal pairs, then rerun
     the `n = 8` search.
   - Status: `noncrossing-partition-diagonal-links-are-cat1` says a search of this
     kind is already running elsewhere, so it was not duplicated.
   - Where it dies here: it needs the large `n = 8` computation that is already
     in progress. This pass did not duplicate it and has no partial result on it.
2. **Upward transfer (fails).**
   - Idea: get `B_{n+1}` CAT(0) from `B_n` CAT(0).
   - Where it dies: Proposition G only extracts smaller groups from centralizers.
     It builds no space for a larger group.
   - We know no general principle that builds a CAT(0) space for `B_{n+1}` from
     one for `B_n`. `B_{n+1}` is not a direct product involving `B_n`, and we
     found no amalgam or HNN decomposition of `B_{n+1}` over `B_n` to which a
     gluing theorem would apply.
3. **A cofinal family of `n`.**
   - Idea: after Theorem M, it is enough to treat `n = 2^k`, or any other
     unbounded family.
   - Where it dies: the Brady–McCammond criterion for `B_n` needs CAT(1) diagonal
     links for all `m ≤ n`, so the orthoscheme route gains nothing from sparsity.
     A sparse family helps only a construction that is not inductive in `n`.
4. **Ambient groups.**
   - Idea: by Proposition G, a CAT(0) group containing elements with centralizers
     `B_n × Z` for infinitely many `n` would prove the claim.
   - Where it dies: by Proposition G, any such group is at least as hard as the
     problem, and no candidate was found.
   - The obvious hosts of braid groups, mapping class groups, are not CAT(0) in
     genus `≥ 3` (Kapovich–Leeb; Bridson; not re-read), so they give nothing.
5. **General form for other Artin groups.**
   - Idea: Proposition G applies wherever a centralizer splits off a `Z`, for
     example Artin groups of type `B_n` or `Ã_{n−1}`.
   - Classical identifications (unverified in this pass) could give more
     implications between these CAT(0) questions:
     - `A(B_n)` with the finite-index subgroup of `B_{n+1}` whose first strand is
       pure;
     - `A(Ã_{n−1})` with a normal subgroup of `A(B_n)` with quotient `Z`
       (Kent–Peifer, 2002).
   - Nothing was recorded in the graph.

## Graph changes

- New claim `braid-cat0-passes-to-fewer-strands`, with direct-proof route
  `braid-cat0-passes-to-fewer-strands-proof` (`requires: []`) and artifact
  `research/artifacts/braid-cat0-fewer-strands-2026-09-16.md`.
- New hole claim `braid-groups-cat0-for-infinitely-many-strands`, with
  `distinct_from` entries for `every-braid-group-is-cat0` and
  `braid-groups-on-at-most-six-strands-are-cat0`, and `## Attempts`.
- New reduction route `every-braid-group-cat0-from-infinitely-many-strands`,
  targeting `every-braid-group-is-cat0` and requiring the two claims above.
- Duplicate checks: `bin/cairn search --similar` on the statements, and
  `bin/cairn search` for "braid" / "CAT(0)" nodes. Near neighbours are
  `every-braid-group-is-cat0`, `every-braid-group-acts-properly-on-a-proper-cat0-space`
  and `some-braid-group-is-not-cat0`. None states monotonicity in `n`.

## Weakest points (for a referee)

- **Textbook inputs, cited by number and not re-read in this pass.**
  - Bridson–Haefliger II.6.8: `Min(z) = Y × R`, with commuting isometries
    splitting as products and a translation on the `R` factor.
  - II.2.2: convexity of the metric.
  - I.3.7: Hopf–Rinow–Cohn-Vossen.
  - The Fadell–Neuwirth short exact sequence.
  All are standard, and II.6.8 is used the same way by COMPLETE routes in the
  graph.
- **The winding-number conjugation formula (W1).** It depends on the lift
  convention for `p` at the permuted basepoint. The artifact spells it out, and
  the computer check agrees with its consequence (every centralizing braid fixes
  the last strand).

## What next

- Use the reduction: `braid-groups-cat0-for-infinitely-many-strands` is the
  sharpest open form of the yes-direction. Any construction for a sparse family
  of `n` now settles all `n`.
- Use the propagation on the no-direction: any obstruction attempt in
  `some-braid-group-is-not-cat0` can target the smallest convenient
  `n_0 ≥ 8`, and then holds for every `n ≥ n_0`. Equivalently, a no-answer for
  one `n` means that `B_n` is not CAT(0) for all large `n`.
- Cross-check: Barre–Pichot (arXiv:1912.13391, abstract only) study a geometric
  action on a CAT(0) space of a finite-index subgroup of `B_4/Z(B_4)`.
  - Corollary 5.4 with `n = 4` gives a geometric action of `B_4/Z(B_4)` itself,
    since `B_4` is CAT(0). So there is no conflict.
  - For the specific `n ≤ 7`, Corollary 5.4 may also be visible directly from the
    Brady–McCammond complex (not checked). The general transfer is the new
    content.
- Possible extension: identify when Proposition G gives implications among the
  CAT(0) questions for Artin groups of types `A`, `B` and `Ã`. Verify the
  relevant centralizer computations first.

## Files touched

- `research/braid-cat0-passes-to-fewer-strands.md` (claim)
- `research/braid-cat0-passes-to-fewer-strands-proof.md` (route, `requires: []`)
- `research/braid-groups-cat0-for-infinitely-many-strands.md` (claim, hole)
- `research/every-braid-group-cat0-from-infinitely-many-strands.md` (route)
- `research/artifacts/braid-cat0-fewer-strands-2026-09-16.md` (artifact)
- `experiments/braid-cat0-fewer-strands-2026-09-16/centralizer_check.py`
- `experiments/braid-cat0-fewer-strands-2026-09-16/results.txt`
- `notes/zaremsky-3-06-braid-groups-cat0-special-case-swarm-2026-09-16.md` (this note)
