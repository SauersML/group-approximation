# Zaremsky 4.2 (planar Rips complexes as wedges): infinite-set hole, swarm note 2026-09-16

- Agent: `swarm-zaremsky-4-02-planar-rips-comp`.
- Target: `zaremsky-4-02-planar-rips-complexes-wedges-of-spheres`.
- Hole locked and worked: `some-infinite-planar-set-has-a-non-wedge-rips-complex`.
- Full proofs: `research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md`.

## Setup

- `R_r(X)` is the clique complex of the graph "distance `≤ r`" (or `< r`) on
  `X ⊆ R^2`.
- The infinite negation matters on its own only if the finite reading is
  positive, because a finite counterexample thickens to an infinite one.
- For infinite `X`, `H_q(R(X)) = colim_F H_q(R(F))` over finite `F`. So the new
  phenomena an infinite set can show are *colimit* phenomena. For example,
  non-free but torsion-free groups like `Z[1/m]` can appear in a colimit of
  free groups.
- The natural question is which invariants can become non-free in the limit.

## What was proven

1. **`H_1` is always free (Theorem A).** New claim
   `planar-rips-complexes-have-free-first-homology`, route
   `planar-rips-complexes-have-free-first-homology-proof`. It requires only
   the established CdSEG import (as submitted). After refereeing it also
  requires the Nöbeling import `profinite-integer-function-groups-are-free`.
   - For every `X ⊆ R^2`, in both conventions, `H_1(R_r(X))` embeds in
     `C(Ω, Z)` with `Ω = lim_F (holes of shadow(F) ⊔ {∞})` profinite.
   - Nöbeling's theorem then gives freeness. For countable `X`, Lemma C gives
     it without the citation.
   - Ingredients: CdSEG on each finite stage, then winding numbers
     (`ω_K : H_1(K) ≅ Z^{holes}`, proved by triangulating a big triangle),
     then naturality via the pullback `π^*`, then injectivity into
     `C(Ω, Z)` by a compactness argument.
   - Consequence: `H_1` can never certify an infinite counterexample.
2. **Reduction (Theorem D).** New route
   `infinite-non-wedge-from-a-multiplying-chain-gadget`, targeting the hole
   and requiring the new claim
   `some-planar-rips-chain-gadget-multiplies-a-sphere-class`.
   - A finite gadget `(G, r, τ, A, z, m)` is required to satisfy:
     separation, `B = τA ⊆ G` disjoint from `A`, a torsion kernel on the
     port, and `i_{A*} z = m · i_{B*} τ_* z` with infinite order and
     `|m| ≥ 2`.
   - Given such a gadget, `X = ∪_{k ≥ 0} τ^k G` has a connected Rips complex
     whose `H_2` has a nonzero element divisible by every `m^k`. So `H_2` is
     not free and the complex is not a wedge.
   - Proof: levels and a separation lemma show every simplex lies in one
     copy. Mayer–Vietoris along the chain gives `α_k = m α_{k+1}`. A
     compatible family of maps to the injective module `Q` shows `α_0 ≠ 0`.
     The strict convention follows by moving from `r` to `r + ε`.
   - Variants: (G4) up to torsion, and non-periodic chains.
3. **Constraints on gadgets** (artifact §4, recorded in the new claim's
   Attempts):
   - (4.1) With a rank-one port, a gadget forces torsion in
     `H_2(R(G) ∪ cone R(A))`, a flag complex.
   - (4.2) A coneable port turns the gadget into a *finite* counterexample.
   - (4.3) Adding a single point keeps `H_2` images pure. Purity is not
     preserved under composition.
   - (4.4) Sliding an octahedral sphere changes its class only by a boundary,
     so the multiplier is `±1`.
   - (4.6) **New lemma.** For any far pair `a, a′`, the far graph on
     `N(a) ∩ N(a′)` is bipartite, split by the line `aa′`. The proof uses
     crossing diagonals of a convex quadrilateral. So `S^0 * Ind(K_3)` is
     never induced, and the "pants" mechanism
     `S^0 * S^0 * Ind(K_3)`, with `O_13 = O_12 + O_23`, is not planar.
4. **Lemma C (positive direction).** An increasing union of finitely generated
   pure subgroups of a torsion-free group is free. So `H_q(R(X))` is free for
   countable `X` whenever it is torsion-free and the images of the finite
   stages are pure. A gadget is an instance of a failure of this purity.
5. **`π_1(R(X))` is locally free** for every planar `X`. The proof uses the
   Hopfian stabilization of image ranks.

## Approaches and where each dies

- **`H_1` certificates for infinite sets.** Dead by Theorem A.
- **Non-free `π_1`.** `π_1(R(X))` is locally free.
  - For countable `X`, freeness would follow from a planar free-factor lemma:
    each image is a free factor of the next. That lemma is not proved.
  - Purely algebraic composites fail: `x_1^2 x_n` is primitive in
    `F(x_1, x_n)`, but killing `x_n` leaves `x_1^2`.
  - For uncountable `X`, `ℵ_1`-free non-free groups exist, so even the lemma
    would not suffice.
  - Open.
- **Non-free `H_2` via a chain gadget.** Reduced to the new claim.
  - With a rank-one port the gadget needs relative torsion, and none was
    observed.
  - Sliding gives `m = ±1`.
  - The simplest branching relation (pants) is not planar.
  - Open: ports with `H_2` of rank `≥ 2`, or multiplicities from sums over
    several tracks.
- **Free homology as evidence for a wedge.** Not a certificate:
  `CP^2` has free homology.
  - Any positive answer for infinite sets must control attaching maps as well
    as homology.
- **Circle of spheres (Attempt (B) of the finite claim).** Same local
  obstruction as the gadget: carrying a sphere needs steps below `r`, while
  separation needs steps above `r`.

## Computation (evidence only)

Directory: `experiments/zaremsky-4-02-planar-rips-comp-2026-09-16/`.

- `relative_torsion_search.py`:
  - builds the cofibre flag complex (the `r`-graph plus a cone vertex on the
    port);
  - reduces it by dominated vertices and dominated edges;
  - compares Betti numbers mod 2, 3 and 1000003.
- Families: `hexcloud`, `twohex(-both)`, `disk`, `halfplane` (basic mode,
  seeds 1–4, 3000 each), plus `hexdense` and `chain(-both)` (dense mode, seeds
  5–7, 4000 each).
- Result: 24,000 complexes, none skipped for size. Nontrivial relative
  homology was common, and **no 2- or 3-torsion was detected** (other primes
  untested). Output is in
  `results-2026-09-16.txt`.
- `far_k2_k3_search.py`: a hill-climbing check of Lemma 4.6.
  - Best slack was `−7.6e−5` (seed 1) and `−6.1e−5` (seed 2), with 1500
    restarts each.
  - Calibration: the square pattern reaches `+0.17`.

## Literature gate (arXiv API and listing pages, 2026-09-16)

- Adamaszek–Frick–Vakili, arXiv:1602.04131v1 (2016). Theorem 1.3 restates
  CdSEG. They say freeness of `π_1` is the only known non-trivial information
  about planar Rips homotopy types.
- Sipani–Kasilingam, arXiv:2406.01082 (2024): classification of planar Rips
  complexes and unit disk graphs (pseudomanifolds). Nothing on wedges or
  infinite sets.
- Komendarczyk–Majhi–Mitra, arXiv:2506.01603 (2025): Vietoris–Rips shadow for
  Euclidean graph reconstruction. Restates CdSEG `π_0`/`π_1`.
- Kawamura–Majhi–Mitra, arXiv:2601.01359 (2026): shadows of Vietoris–Rips
  complexes in limits (`β → 0`). Not the fixed-scale infinite question.
- Adams et al., arXiv:2511.09471 (2025): ellipses at larger scales.
- Adams–Karassev–Virk, arXiv:2512.23108 (2025): Vietoris thickenings.
- Hulbert–Zaremsky, arXiv:2608.25614 (2026): Morse theory for Vietoris–Rips
  complexes of groups.
- Asgeirsson, arXiv:2309.07252v2 (2023): statement of Nöbeling's theorem
  (Theorem 18). The original 1968 paper was not opened.
- Zaremsky's problem list (version of 12 July 2026): Problem 4.2 still open.
- None of these gives freeness of `H_1` for infinite planar sets or a
  non-wedge planar Rips complex.
- Whether Lemma 4.6 appears in CdSEG or AFV was not checked. Text extraction
  from the AFV PDF failed.

## Files touched

- `research/planar-rips-complexes-have-free-first-homology.md` (new claim)
- `research/planar-rips-complexes-have-free-first-homology-proof.md` (new
  route)
- `research/some-planar-rips-chain-gadget-multiplies-a-sphere-class.md` (new
  claim, open hole with Attempts)
- `research/infinite-non-wedge-from-a-multiplying-chain-gadget.md` (new route)
- `research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md`
- `experiments/zaremsky-4-02-planar-rips-comp-2026-09-16/relative_torsion_search.py`
- `experiments/zaremsky-4-02-planar-rips-comp-2026-09-16/far_k2_k3_search.py`
- `experiments/zaremsky-4-02-planar-rips-comp-2026-09-16/results-2026-09-16.txt`
- this note

check.sh on the four nodes plus the artifact: exit 0.

## Referee (2026-09-16)

### What was checked

- **Theorem A** (free `H_1`), line by line:
  - the reduction to finite stages;
  - the winding-number isomorphism `ω_K`;
  - naturality via `π^*` on `holes ⊔ {∞}`;
  - the compactness argument for injectivity into `C(Ω, Z)`;
  - Lemma C.

  All sound, with one gap: step 3 said "triangulate a big triangle" without
  saying how `K` becomes a subcomplex.
- **Theorem D** (chain gadget reduction):
  - lemma (S) and the level decomposition;
  - "every simplex lies in one copy";
  - `Y_N ∩ R(G_{N+1}) = R(τ^{N+1}A)`;
  - the Mayer–Vietoris extension of `φ_N` into `Q`, which needs only that
    the kernel in (G3) is torsion;
  - divisibility `α_0 = m^k α_k`;
  - the strict convention via `r + ε`.

  Sound.
- **Lemmas 4.1, 4.3, 4.4, 4.6 and the `π_1` local-freeness proposition.**
  Sound. For 4.6, I checked the convex-position step and the
  crossing-diagonal step. If `aa′` were a side, the opposite sides `aa′`, `pq`
  would sum to more than `2r` while the diagonals sum to at most `2r`.
- **§4.2 (a coneable port gives a finite counterexample).** This was an
  overclaim. §4.2 cited 4.1, which needs a rank-one port, but was stated for
  every gadget.
- **Citations:**
  - Nöbeling's theorem was used in the Theorem A route without an import
    node. I read the statement from the LaTeX source of Asgeirsson
    arXiv:2309.07252v2 (§4, Theorem 18). The 1968 original was not opened.
  - CdSEG arXiv:0712.0395v1: searched the source for Lemma 4.6. It is not
    there in this form.
  - AFV arXiv:1602.04131 was not checked for Lemma 4.6.
- **Novelty and duplicates.**
  - No node in the tree states Nöbeling's theorem, and no in-flight file
    duplicates it.
  - No literature found giving free `H_1` for infinite planar sets or a
    non-wedge planar Rips complex.
- **Computation.**
  - Re-ran single-threaded, under `timeout 600`: `relative_torsion_search.py 1
    3000 basic` and `far_k2_k3_search.py 1 1500`. The output matches
    `results-2026-09-16.txt` (e.g. hexcloud: 922 tested, 447 nontrivial,
    0 flags).
  - Checked that the mod-p Betti comparison does detect torsion, on an
    `RP^2` flag triangulation: mod-2 Betti numbers jump and mod-3 do not.
  - The script compares only mod 2 and mod 3 against mod 1000003. So
    "zero torsion" was an overstatement: only 2- and 3-torsion is excluded.
- **Cairn discipline:**
  - both new holes have `## Attempts`;
  - the route into the hole requires the open gadget claim, so it is not a
    `requires: []` route into the root;
  - ids are within the length caps.

### What was changed

- New import nodes: `research/profinite-integer-function-groups-are-free.md`
  (claim) and `research/profinite-integer-function-groups-are-free-citation.md`
  (citation route). The citation route quotes the statement verbatim and
  marks the original paper as not opened.
- `research/planar-rips-complexes-have-free-first-homology-proof.md`:
  - now requires the Nöbeling import;
  - step 3 now points to the explicit triangulation in artifact A3;
  - step 5 cites the import;
  - the countable remark notes that the import is unnecessary there.
- Artifact `research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md`:
  - A3: an explicit triangulation with `K` as a subcomplex (lines through
    every vertex, 2-cells coned from interior points);
  - A6: points to the import;
  - new **Lemma 4.1′**: for any port with torsion-free `H_2(R(A))`, a gadget
    forces torsion of order dividing `m` in `coker(i_{A*})`, by iterating
    `z = m^k w_k`. If `H_2(R(A))` has torsion, a component of `R(A)` is
    already a finite non-wedge;
  - §4.2: rewritten on top of 4.1 and 4.1′, which repairs the overclaim;
  - §4.6: records which citation checks were done;
  - §5: "exactly" changed to "an instance of";
  - §7: evidence wording limited to "no 2- or 3-torsion detected".
- `research/some-planar-rips-chain-gadget-multiplies-a-sphere-class.md`:
  - `distinct_from` now says "is known to give";
  - new Attempts bullet for 4.1′;
  - coneable-port bullet justified by 4.1′;
  - computation wording limited to 2- and 3-torsion.
- This note:
  - the Theorem A prerequisites are updated;
  - the evidence wording is corrected;
  - "exactly" is changed to "an instance of".

### Verdict

**Landed with fixes.**

- Theorem A (free `H_1(R_r(X))` for every planar `X`, both conventions) is
  proved, modulo the CdSEG and Nöbeling imports.
- The reduction of the infinite hole to the finite gadget claim is proved.
- The gadget claim stays open, as do the hole and the target.
- The computations are evidence only.

### Files touched by the referee

- `research/profinite-integer-function-groups-are-free.md` (new)
- `research/profinite-integer-function-groups-are-free-citation.md` (new)
- `research/planar-rips-complexes-have-free-first-homology-proof.md`
- `research/some-planar-rips-chain-gadget-multiplies-a-sphere-class.md`
- `research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md`
- this note
