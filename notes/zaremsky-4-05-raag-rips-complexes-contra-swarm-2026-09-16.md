# Zaremsky 4.5 via cube complexes: swarm attack, 2026-09-16

- **Lane:** `swarm-zaremsky-4-05-raag-rips-comple`.
- **Root:** `zaremsky-4-05-raag-rips-complexes-contractible`.
- **Hole locked and worked:** `raag-salvetti-covers-have-the-jensen-helly-property`.
- **Full proofs:** `research/artifacts/zp-cube-complex-jensen-helly-2026-09-16.md`.
- **Scripts:** `experiments/zaremsky-4-05-jensen-cube-2026-09-16/` (`raagcube.py`, `jtest.py`, `jtest2.py`,
  `jhelly.py`, `jhelly_adv.py`, `jhelly_splits.py`).

## Setup

The root reduces, through `zaremsky-4-05-by-yes` → `every-raag-is-rips-type-r` →
`every-raag-is-rips-type-r-via-jensen-helly`, to two claims.

1. `jensen-helly-graphs-have-contractible-rips-complexes` (UNREVIEWED, already landed). If a bounded-degree graph
   has a realization with (J) Jensen barycentres, (H) Helly number `k+1` for vertex-centred balls and (R) rounding
   within `k/2`, then `VR_t` is contractible for every integer `t ≥ k(k+1) − 1`. It rests on Zaremsky's criterion
   (arXiv:2410.11993v2, Theorem 3.1).
2. The hole: the Cayley graph of `(A_Γ, V(Γ))` has this property with `k` the clique number.

Before this attack the hole was proved for cographs only (products and one-vertex wedges). The Attempts recorded
that the naive projected mean fails in `Z^2 * Z`, and that l^1-balls are not convex along CAT(0) geodesics.

## Status gate (checked 2026-09-16)

- **Zaremsky, *Some open problems*,** PDF dated July 12, 2026 (text in hand 2026-09-16). Section 4, Problem 5 reads
  "(Added 10/2/24): Is the Rips complex of any RAAG with the standard word metric contractible for large enough
  Rips parameter?", with no answer marked. Problem 4.3 is marked solved by Virk.
- **Hulbert–Zaremsky,** *Word length, Morse theory, and Vietoris–Rips complexes*, arXiv:2608.25614v1 (API date
  2026-08-26; PDF dated August 27, 2026). Read: abstract, §1, §4 up to Proposition 4.4.
  - They prove `VR_2(A_Γ)` contractible for triangle-free `Γ`.
  - They say the contractibility question "is open in general" and call `t ≥ n` (clique number `n`) "a natural
    prediction".
  - Observation 4.2 ("Squares are visible") is used in §9 of the artifact.
- **Li–Sánchez Saldaña,** *Contractible Rips complexes of groups via metric gluings*, arXiv:2608.24279v1 (API date
  2026-08-25). Read: abstract and §1.
  - They call "all RAAGs of type R" a natural question (citing Zaremsky's Question 4.5).
  - They prove it for triangle-free `Γ` (Theorem 1.5).
  - They say that in higher dimensions "the combinatorics of the gluings [is] intractable".
- **arXiv API searches over https, run 2026-09-16:**

  | Query | Hits | What they are |
  | --- | --- | --- |
  | `abs:Rips AND abs:Artin` | 2 | The two papers above |
  | `abs:"right-angled Artin" AND abs:"Vietoris-Rips"` | 1 | 2608.25614 |
  | `abs:Rips AND abs:Helly AND abs:contractible` | 1 | 2201.01599v2 (Chalopin–Chepoi–Giocanti, *Graphs with convex balls*); listing only, off-axis |
  | `abs:Rips AND abs:cube AND abs:complex` | 5 | Fournier-Facio 2603.12095 and four applied-topology papers; none on Rips complexes of cubulated groups |
  | `abs:Rips AND abs:median` | 5 | All off-axis (includes Chatterji–Druţu 1708.00254 and Fioravanti 2601.22789) |

  Two phrase queries (`abs:Rips AND abs:"cube complex"` and `abs:"Vietoris-Rips" AND abs:"median graph"`) returned
  no parseable response.
- **Conclusion:** no resolution of Problem 4.5 was found as of 2026-09-16. Dimension ≥ 3 was open in the literature.

## What was established (UNREVIEWED)

1. **`cat0-cube-complexes-have-the-jensen-helly-property`** (new claim; route `-proof`, `requires: []`).
   - *Statement.* Let `G` be a median graph of finite cube dimension `k ≥ 1`, that is, the 1-skeleton of a
     `k`-dimensional CAT(0) cube complex. Then `G` has the Jensen–Helly property of dimension `k`. It is realized by
     the cube complex `|X|` inside the hyperplane box `[0,1]^H`, with the coordinate l^1 metric.
   - No bounded degree is needed here.
2. **Route `raag-salvetti-covers-jensen-helly-via-cube-complexes`** into the hole.
   - Salvetti covers are CAT(0) cube complexes with median 1-skeleton (standard).
   - Their cube dimension is at most the clique number. An induced square forces commuting labels by an
     exponent-sum argument (Hulbert–Zaremsky, Observation 4.2), and distinct commuting generators are adjacent
     (retract onto `F_2`).
3. **Consequence.** `check.sh` reports that the change establishes `raag-salvetti-covers-have-the-jensen-helly-property`,
   `every-raag-is-rips-type-r` and the root. Every RAAG with standard generators is of Rips type R, with
   `R_t(A_Γ, V(Γ))` contractible for all integers `t ≥ k(k+1) − 1`. The answer to Problem 4.5 is **yes**. The same
   argument covers right-angled Coxeter groups (a remark only; no node).

**Proof shape** (artifact §§1–8).
- **Affine distances.** Coordinates are `c_v(h) = [v ∈ h^1]`, and `L_x(p) := d_1(c_x, p)` is **affine on the whole
  box**. With `w_h = μ(h^1)` this gives `L_x(w) = ∫ d(x,y) dμ`.
- **Lemma C.** A box point lies in `|X|` iff no *empty quadrant* is charged. An empty quadrant is a pair of
  disjoint halfspaces of distinct hyperplanes; "charged" means both carry positive charge. The proof uses Helly
  number 2 for convex sets (median argument).
- **Lemma U (unfolding).** Removing the smaller charge `s` from a charged empty quadrant fixes every `L_x`, except
  that it lowers `L_x` by `2s` on the nonempty set `A* ∩ B*`.
- **Lemma J.** A minimizer of `Σ_x L_x` over `{L_x ≤ L_x(w)}` has no charged quadrant, so it is a Jensen centre in
  `|X|`. The infinite case goes through the finite hull and gates.
- **Lemma Rt.** `r(c) = argmin (Σ L_x + (1/8)|c|²)` over `{L_x ≤ L_x(c)}` is a continuous retraction of the box onto
  `|X|` that does not increase any `L_x`. Consequences: every nonempty intersection of vertex-centred balls is a
  retract of a convex polytope, and `|X|` is contractible.
- **Lemma H.** Triangulate so that the balls are subcomplexes, of dimension `≤ k`. A minimal empty family of `n+1 ≥ k+2`
  balls has union `≃ S^{n−1}` by the nerve theorem. That contradicts `dim ≤ k` when `n−1 > k`, and
  `H^k(|X|) = 0 = H^{k+1}(|X|, U)` when `n−1 = k`.
- **Lemma R.** Round to the nearest corner.
- **Sharpness.** Helly number `k` fails already for `Z^3`: an explicit four-ball family in `R^3` with gap 0.375
  (artifact §10).

## Approaches and where they die

- **Piece-by-piece projected mean (tree-graded pieces, as in the cograph wedge lemma).**
  - *Dies:* the `Z^2 * Z` counterexample in the hole's Attempts. The rule oscillates between a piece and a cut
    point.
  - *Consistency check:* Lemma J reproduces the forced value `d_1(g,b) = 4.5` recorded there (artifact §10).
- **The box mean `w` itself.**
  - *Works in the box:* it satisfies (J) with equality.
  - *Dies:* `w ∉ |X|` as soon as an empty quadrant is charged (the same example).
  - *Repair:* Lemma J minimizes `Σ L_x` over the Jensen polytope and unfolds.
- **Topological Helly via convexity of l^1-balls along CAT(0) geodesics.**
  - *Dies:* `d_1(x,·)` is concave at cut points in `Z^2 * Z`, so the geodesic bicombing does not preserve balls.
  - *Repair:* the box retraction `r` (Lemma Rt). It gives contractible intersections without any bicombing. The
    dimension count then uses `dim |X| = k`. Helly in the box itself would only give the useless number `|H| + 1`.
- **Computational falsification of (H) directly on Salvetti-cover hulls (`jhelly.py`, `jhelly_adv.py`).**
  - *What happened:* random and hill-climbed radii found no `(k+1)`-failures, but they also found no `k`-member
    failures ("teeth 0").
  - *Dies as evidence:* the searches were too weak to be evidence for (H).
- **Split-system reformulation (`jhelly_splits.py`).**
  - *Method:* the box minimum depends only on the split system of the centres. By Lemma Rt and test (E) of
    `jhelly.py`, it equals the minimum on `|X|`. Hill-climb over arbitrary weighted split systems.
  - *Result:* it finds `κ`-member failures (teeth at `κ = 3, 4`, including the `R^3` example) and no
    `(κ+1)`-member failure. This was the computational support for Lemma H before the hand proof.

## Experiments

All runs are single-threaded, under 10 minutes each, and use scipy HiGHS LPs. They are evidence, not proof.

| Command (in the experiments directory) | Result |
| --- | --- |
| `python3 jtest.py 1` | P4: 60 trials; K1*P4: 40 trials; worst min-slack `-0.0` (no (J) failure) |
| `python3 jtest2.py 5 2 20 5 C5,K4-minus-path,K1*P4` | 20 trials each, worst min-slack `-0.0` |
| `python3 jhelly.py 2 2 6 "P4,K1*P4,C5"` (32 s) | `helly_fail 0`, `box_mismatch 0`, `unfold_worst 0.0`; maxV 21/38/21 |
| `python3 jhelly_splits.py 3 4 10 30` | `R^3` example `kappa 3 gap_3 0.375`; m=4, κ=1,2: `fail 0` |
| `python3 jhelly_splits.py 7 5 25 30` (66 s) | m=5, κ=1,2,3: `fail 0` (max gap `4.44e-16`, rounding); teeth 2, 0, 5 |

Earlier runs from the same session, larger:
- `jhelly.py` at R=3 with 40 trials each on P4, C5, triangle+pendant and K4−path (maxV up to 100);
- K1*P4 at R=2 with 30 trials, and K2*P4 (`k = 4`) at R=2 with 8 trials (maxV 198);
- `jhelly_splits.py` with m=6 (90 systems; `fail 0` at κ=2,3,4; teeth at κ=3,4) and m=5 (κ=3: 39 systems,
  `fail 0`, teeth 14).

All counts were zero.

## Weakest steps (for the referee)

1. **Lemma Rt(c), continuity of `r`.** It uses Hoffman's error bound for lower semicontinuity of `c ↦ D_c`, plus
   uniqueness of the minimizer. It is needed only for contractibility of ball intersections; emptiness equivalence
   needs only Rt(a).
2. **Lemma H.** The common triangulation of `|X|` refined by the hyperplanes `{L_{z_i} = ρ_i}`, and the nerve theorem
   for subcomplexes.
3. **Standard facts not re-fetched.** The median graph facts (M1)–(M4), and that Salvetti covers are CAT(0) with
   median 1-skeleton (stated as standard in arXiv:2608.25614v1, §4).
4. **Upstream.** `jensen-helly-graphs-have-contractible-rips-complexes` is UNREVIEWED. Its import (Zaremsky's
   Theorem 3.1) was re-read verbatim.

## Literature consulted

- M. C. B. Zaremsky, *Contractible Vietoris–Rips complexes of Z^n*, arXiv:2410.11993v2 (dated August 14, 2025).
  Theorem 3.1, Corollary 3.2 and their proofs were read verbatim 2026-09-16.
- M. C. B. Zaremsky, *Some open problems*, PDF dated July 12, 2026. Section 4 was read 2026-09-16.
- S. Hulbert, M. C. B. Zaremsky, arXiv:2608.25614v1. Abstract, §1 and §4 through Proposition 4.4 were read
  2026-09-16.
- K. Li, L. J. Sánchez Saldaña, arXiv:2608.24279v1. Abstract and §1 were read 2026-09-16.
- R. K. Gupta, S. Sarkar, S. Shukla, *On the Vietoris–Rips complexes of integer lattices*, arXiv:2511.04238v1
  (2025-11-06). Only the API abstract was read, 2026-09-16. It treats `Z^n` only (the conjecture `r ≥ n` for
  `n ≤ 5`), so it is off-axis for general RAAGs.
- arXiv:2201.01599v2 (Chalopin–Chepoi–Giocanti): API listing only, 2026-09-16, off-axis.
- Ž. Virk, arXiv:2405.09134: cited through Zaremsky's list and the existing node; not re-read.
- J. Chalopin, V. Chepoi, A. Genevois, H. Hirai, D. Osajda, *Helly groups*, arXiv:2002.06895: cited through the root
  node; not re-read.
- **Unverified here (standard references, not fetched):**
  - A. J. Hoffman, *On approximate solutions of systems of linear inequalities*, J. Res. Nat. Bur. Standards 49
    (1952).
  - A. Björner, *Topological methods*, Handbook of Combinatorics (1995), Theorem 10.6 (nerve theorem).
  - V. Chepoi, *Graphs of some CAT(0) complexes*, Adv. Appl. Math. (2000).
  - M. Roller, *Poc sets, median algebras and group actions* (1998 preprint).
  - R. Charney, M. Davis, *Finite `K(π,1)`s for Artin groups* (1995).
  - H. M. Mulder (1980), and H.-J. Bandelt, V. Chepoi, *Metric graph theory and geometry: a survey* (2008).

## Files touched

- `research/cat0-cube-complexes-have-the-jensen-helly-property.md` (new claim)
- `research/cat0-cube-complexes-have-the-jensen-helly-property-proof.md` (new route, `requires: []`)
- `research/raag-salvetti-covers-jensen-helly-via-cube-complexes.md` (new route into the hole)
- `research/artifacts/zp-cube-complex-jensen-helly-2026-09-16.md` (new artifact)
- `notes/zaremsky-4-05-raag-rips-complexes-contra-swarm-2026-09-16.md` (this note)
- `experiments/zaremsky-4-05-jensen-cube-2026-09-16/{raagcube,jtest,jtest2,jhelly,jhelly_adv,jhelly_splits}.py`

No existing node was edited. The hole's Attempts section was left as is; the new route targets it.

## Referee (2026-09-16)

Adversarial referee pass by the swarm landing agent. It is one pass, not an independent human review, so every node
keeps the UNREVIEWED label.

**What was checked.**
- Every listed file was read in full. So were the upstream nodes `jensen-helly-graphs-have-contractible-rips-complexes`
  (claim and proof route), `zaremsky-rips-contractibility-criterion` (and its citation), `every-raag-is-rips-type-r`,
  `every-raag-is-rips-type-r-via-jensen-helly`, `zaremsky-4-05-by-yes` and the root. `git status` shows no unlisted
  solver files.
- **Artifact §§1–9, re-derived line by line.**
  - (M5), with the induction step: `C_1 ∩ C_2` meets every `C_j` by the triple case.
  - Distinct hyperplanes give distinct splits.
  - Affinity of `L_x` on the box, and (2.1).
  - Lemma C, both directions and all three corner cases.
  - Lemma U (1)–(4), including `(y ± s)² − y² ≤ 3s`.
  - Lemma J, in the finite case and the infinite case. Hyperplanes separating `x` from its gate do not cross the hull,
    and `d_1(x,b) = d(x,x') + d_1(x',b_K)`.
  - Lemma Rt:
    - (a): `Ψ` drops by at least `2s − 6s/8`.
    - (b): the antipodal sum forces `c' = p` off `F`, equal corner sums force equalities, and the flip identity
      `ℓ_σ − ℓ_{σ^g} = (1 − 2σ_g)(2y_g − 1)`.
    - (c): Hoffman gives lower semicontinuity of `c ↦ D_c`, since `D_{c_n} ∋ c_n` is nonempty. With closedness and
      uniqueness of the strictly convex minimizer, `r` is continuous.
  - Corollary Rt: `r(P_I) = B_I` and `r|_{B_I} = id`.
  - Lemma H:
    - The common refinement makes each `B_i` a subcomplex of dimension `≤ k`.
    - The nerve of a minimal non-meeting family is `∂Δ^n`.
    - Case `n − 1 > k` fails by dimension. Case `n − 1 = k` fails because
      `H^k(|X|) → H^k(U) → H^{k+1}(|X|,U)` is exact with both ends zero.
    - Passage to a finite hull: witnesses' free coordinates cross the hull, and centres and corners share `c_K` off
      `H(K)`.
  - Lemma R.
  - §9. The exponent-sum argument, including the exclusions `b = a^{−1}` ⇒ `g_12 = g`, `d = a^{−1}` ⇒ `g_2 = g_1`,
    `c = b^{−1}` ⇒ `g_2 = g_1`, `b = a` ⇒ `g_2 = g_1`. Also the retraction `A_Γ → F(u,v)`.
  - I found no mathematical error, no circularity and no hidden hypothesis. Bounded degree enters only through the
    upstream Rips theorem, and the Cayley graph of `A_Γ` has degree `2|V(Γ)|`.
- **Definitions against upstream.**
  - (J), (H) and (R) as proved match the definitions in `jensen-helly-graphs-have-contractible-rips-complexes`: closed
    balls, vertex centres, real radii and a metric realization containing `V` isometrically.
  - The upstream proof uses only vertex-to-point distances and the triangle inequality in `|G|`, and `(|X|, d_1)`
    provides both.
  - Upstream step 3 and its `r_t` arithmetic were rechecked.
- **Citations spot-checked by WebFetch (2026-09-16).**
  - Zaremsky, *Some open problems*: the PDF is dated July 12, 2026, and Section 4 Problem 5 is verbatim as quoted,
    with no answer marked.
  - arXiv:2608.25614v1 (Hulbert–Zaremsky, submitted Aug 26, 2026):
    - Observation 4.2 "Squares are visible" reads "Then c=a⁻¹ and d=b⁻¹, so a and b commute".
    - §1 says the general problem is "wide open" and predicts `t ≥ n`.
    - §4 states that the Cayley graph is the 1-skeleton of a CAT(0) cube complex and hence median, as a standard fact.
  - arXiv:2608.24279v1 (Li–Sánchez Saldaña, Aug 25, 2026): the abstract proves type R for two-dimensional RAAGs only.
  - arXiv API, `abs:Rips AND abs:Artin`, newest first: only these two papers.
  - arXiv API, `abs:Rips AND (cubical OR median OR cubulated)`: nothing on Rips contractibility for cube complexes.
  - General web search was unavailable (the session search budget was exhausted), so the novelty check rests on the
    arXiv API and the dated problem list.
  - Hoffman (1952) and Björner (1995, Theorem 10.6) were not re-fetched. The bibliographic details agree with the
    referee's knowledge of these standard references.
- **Duplicates.** `bin/cairn search --similar` and lexical searches found no existing claim on Jensen–Helly or Rips
  contractibility for general median graphs. `cube-level-set-clique-complexes-model-the-level-set` is unrelated.
- **Computations.**
  - Replay: `python3 jhelly.py 2 2 6 "P4,K1*P4,C5"` reproduced `helly_fail 0, box_mismatch 0, unfold_worst 0.0` in
    7.5 s.
  - Replay: `python3 jhelly_splits.py 3 4 10 30` reproduced the `R^3` gap 0.375 and `fail 0`.
  - The `R^3` sharpness example was recomputed by a separate LP: full value 0.125, best 3-subfamily −0.25, gap 0.375.
  - **Independent checker** `experiments/zaremsky-4-05-jensen-cube-2026-09-16/referee/ref_check.py` shares no code
    with the solver's scripts.
    - It builds median graphs as Roller duals of random split systems (4–6 points, up to 6 splits), and verifies the
      median property and `d` = Hamming distance by BFS.
    - It then tests Lemma J: LP minimizers of `Φ` have no charged empty quadrant.
    - It tests Lemma H by hill-climbing radii to maximize the `(k+1)`-Helly gap, and records `k`-subfamily failures
      ("teeth") as a power check.
    - Results (`python3 ref_check.py SEED TRIALS`, each run under `timeout 600`):
      - seed 1, 6 trials: `{'graphs': 6, 'nonmedian': 0, 'charged': 0, 'helly_fail': 0, 'worst_gap_k1': 0.0, 'teeth_k': 1}`.
      - seed 2, 8 trials (|V| 4–21, k 1–3): `{'graphs': 8, 'nonmedian': 0, 'charged': 0, 'helly_fail': 0, 'worst_gap_k1': 1.1e-16, 'teeth_k': 6}`.
      - seed 3, 8 trials (|V| 6–14, k 2–3): `{'graphs': 8, 'nonmedian': 0, 'charged': 0, 'helly_fail': 0, 'worst_gap_k1': 0.0, 'teeth_k': 0}`.
      - Total: 22 median graphs. There were no charged quadrants at Φ-minimizers and no `(k+1)`-Helly failures
        (the worst gap was float noise). The same search found `k`-member failures in 7 cases, so the Helly search
        does have power.
      - This is weak evidence (small graphs, k ≤ 3, local search). The proof stands on the argument, not on these runs.
      - A 25-trial run for seed 2 timed out before it printed anything, and a 25-trial run for seed 3 was killed.
        Neither gave any partial evidence against the claim.

**What was changed.**
- Claim title and body: the title now leads with "median graph of finite cube dimension k". "Cube dimension =
  dimension of the CAT(0) cube complex" is marked as a standard fact that the proof does not use. The RAAG route
  bounds the cube dimension directly.
- The proof route gains an explicit "Trust surface" list of the standard results used without proof: median-graph
  facts (M1)–(M4), Hoffman's bound and the nerve theorem.
- Artifact: the status line records this referee pass. Lemma H's infinite case now notes that the finite proof uses
  only `dim ≤ k` and `k ≥ 1`.
- Added the referee checker script above.

**Verdict.** The mathematics looks sound as written. The direct proof is complete modulo textbook imports: median
graph structure, Hoffman's error bound and the nerve theorem. It lands with minor fixes. Landing makes
`raag-salvetti-covers-have-the-jensen-helly-property`, `every-raag-is-rips-type-r` and the root
`zaremsky-4-05-raag-rips-complexes-contractible` computed ESTABLISHED. Every link is UNREVIEWED, and the chain also
rests on the earlier UNREVIEWED `jensen-helly-graphs-have-contractible-rips-complexes` and Zaremsky's Theorem 3.1.
Given that it claims to settle a published open problem, the chain deserves an independent human review before it is
announced. Still open: the Hulbert–Zaremsky prediction `t ≥ k`.
