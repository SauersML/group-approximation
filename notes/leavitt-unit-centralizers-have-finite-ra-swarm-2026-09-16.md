# Leavitt unit centralizers have finite rank: swarm lane, 2026-09-16

Target: `leavitt-unit-centralizers-have-finite-rank`. Let `R = L_(F_2)(1,2)`. Is
`rho(u) = dim_(F_2(u)) F_2(u) ⊗_(F_2[u]) C_R(u)` finite for every infinite-order unit `u`?

- **Locks.** `leavitt-unit-centralizers-have-finite-rank` (hole worked) and
  `infinite-order-elements-of-v-have-hyperbolic-periodic-points`, the dynamical input. The second lock was taken
  because the proof needs a strengthened form of that claim.
- **Outcome.** Partial progress. The target is proved for every conjugate of an infinite-order Thompson unit.
  It stays open for linear units.

## 1. Results

- **Theorem A**, new claim `leavitt-thompson-units-have-finite-centralizer-rank`, direct route
  `leavitt-thompson-units-have-finite-centralizer-rank-proof`.
  - Let `g ∈ V` have infinite order, and let `w` be any unit of `R`. Then
    `1 <= rho(w u_g w^(-1)) <= min(N(g), N(g^(-1)))`.
  - Here `N(g) = |P_a| · Σ_O d_O`, where `P_a` is the finite set of attracting periodic points and `d_O` is the
    length gain of the local replacement over the orbit `O`.
- **Theorem B**, route `v-hyperbolic-periodic-points-from-rigid-words` into the V0 claim, with `requires: []`.
  - Every infinite-order `g ∈ V` has a hyperbolic periodic point.
  - The artifact proves more: `A0 = P_0` is open, `B = P_r`, `P_a` and `P_r` are finite, and both are nonempty
    for infinite order.
  - With exit 0, `check.sh` reports that this route establishes the V0 claim. It also unlocks
    `bs-1-n-does-not-embed-in-thompson-v` and `torsion-free-nilpotent-subgroups-of-thompson-v-are-abelian`.
- **Full proofs.** `research/artifacts/leavitt-thompson-unit-centralizer-rank-2026-09-16.md`.
  - §1 is the groupoid model: `φ(s_α t_β) = 1_(Z(α,β))` is injective, and supports are closed with compact
    range projection.
  - §2 is the dynamics of one element of `V`: rigid words, ladder times and new-minimum times.
  - §3 is the germ map `κ : C_R(u_g) -> ⊕_(P_a × P_a) F_2[x^(±1)]`. The target is free of rank `N(g)` over
    `F_2[t^(±1)]`, and `ker κ` is `F_2[u]`-torsion by a limit and compactness argument on supports.

## 2. Consequences for `U_V`, the conjugates of Thompson units (artifact §4)

- **4.1.** Elements commuting with `y ∈ U_V` are algebraic over `F_2[y]`.
- **4.2.** No `y ∈ U_V` is a Heisenberg center or a `BS(1,k)` base in `R^x`.
- **4.3.** No `y ∈ U_V` is conjugate to `phi(y)`.
- **4.4.** The remark on `f(1 ⊗ c)` depends on a reduction this lane did not re-check.

## 3. Examples and experiments

- **Exact values.** `N = rho` for `c` (1), `c^2` (2) and `phi(c)` (4).
- **Not sharp.** For the two-cycle `u = s_1 c t_0 + s_0 t_1`, the matrix form `[[0,1],[c,0]]` gives
  `C_R(u) = F_2[u^(±1)]`, so `rho = 1 < N = 2`.
- **Script.** `experiments/leavitt-thompson-centralizer-rank-2026-09-16/thompson_rank.py`, with log `run-N3.log`.
  - **Part A**, 300 random elements of `V`, seed 7.
    - 194 elements were detected as finite order, and none had a germ.
    - All 106 elements whose order was not detected had germs for `g` and `g^(-1)`.
    - Heuristic trichotomy on 1500 points: 994 points in `A0` were all periodic-cylinder points, 34 points in `B`
      were all periodic, 472 were in `A+`, and the largest `|P_a|` seen was 4.
  - **Part B**, exact `F_2` elimination on `R_3`, which has dimension 176. The eventual increments are 1, 2, 4 and
    1 for `c`, `c^2`, `phi(c)` and the two-cycle, consistent with the values above.

## 4. Where the method stops

- **Linear units.** For a unit outside `U_V`, `φ(u)` is not a bisection indicator. There is then no point map
  `T` on supports, and Lemma 3.2 (kernel torsion) has no analogue.
  - The annulus north–south result covers some linear twists by a different method.
  - Neither that result nor Theorem A contains the other.
- **Open.**
  - The exact value of `rho(u_g)`.
  - Any linear unit with more than one attracting germ.
  - The general target.

## 5. Weakest steps (for the referee)

- **Lemma 3.2(ii).** The limit argument needs `W` closed in `X × Z × X`, `c_(J−j)` locally constant, and the
  middle coordinate affine in `m` and bounded, hence eventually constant.
- **Lemma 2.5 / Step 5 of the V0 route.** Bookkeeping of the backward rigid words `V_i(v)` at new-minimum times.

## 6. Literature (checked 2026-09-16 unless noted)

- **Brownlowe–Sørensen, arXiv:1603.03618.** Abstract only; the PDF could not be parsed. Not used.
  - *Referee addition.* Their Proposition 3.4 (commuting elements of `U_V` are algebraically dependent) is recorded
    in `research/artifacts/brownlowe-sorensen-transfer-to-f2-2026-09-13.md`. It is the both-Thompson special case of
    consequence 4.1, and it is now cited there.
- **Bilich–Hazrat–Nam, arXiv:2512.09241v2.** Read through the existing repo artifact. Not used in proofs.
- **Clark–Sims, arXiv:1311.3701** (Steinberg-algebra model). Through the repo node; not re-read. The groupoid
  model is proved from scratch in artifact §1.
- **Brin, Geom. Dedicata 108 (2004)** (revealing pairs). Not re-read; Theorem B is expected to follow from it, and
  §2 is independent.
- **Bleak–Bowman–Gordon–Graham–Hughes–Matucci–Sapir, arXiv:1107.0672** (centralizers in `V_n`). Not re-read.
- **arXiv API**, 5 abstract queries through `export.arxiv.org`, run 2026-09-16. Only the returned titles were
  scanned:
  - `abs:centralizer AND abs:Leavitt`
  - `abs:centralizer AND abs:"Steinberg algebra"`
  - `abs:centralizer AND abs:"topological full group"`
  - `abs:centralizers AND abs:Thompson AND abs:"group V"`
  - `abs:"Leavitt algebra" AND abs:"unit group"`

  No returned title concerns centralizers of topological-full-group units inside Leavitt or Steinberg algebras. This is weak
  novelty evidence only.
- **WebSearch.** The session budget was exhausted, so no further web search was possible.
- **Same-date lane `zaremsky-2-15b`.** Its artifact `infinite-order-v-elements-hyperbolic-points-2026-09-16.md`
  was read and checked. It is an independent proof of V0, has not landed, and is not cited as a dependency.

## 7. Files

- `research/leavitt-thompson-units-have-finite-centralizer-rank.md` (claim)
- `research/leavitt-thompson-units-have-finite-centralizer-rank-proof.md` (route, `requires: []`)
- `research/v-hyperbolic-periodic-points-from-rigid-words.md` (route, `requires: []`)
- `research/artifacts/leavitt-thompson-unit-centralizer-rank-2026-09-16.md`
- `experiments/leavitt-thompson-centralizer-rank-2026-09-16/thompson_rank.py` and `run-N3.log`
- `check.sh` on the four research paths: exit 0.

## Referee (2026-09-16)

**Checked.** I read the artifact, both routes, the claim and this note in full, together with the committed nodes
they rely on:
- `leavitt-unit-centralizers-have-finite-rank` and `infinite-order-elements-of-v-have-hyperbolic-periodic-points`;
- `leavitt-north-south-thompson-unit-has-cyclic-centralizer` and `leavitt-heisenberg-centers-have-infinite-centralizer-rank`;
- `no-diagonal-conjugacy-from-finite-centralizer-rank` and `algebraic-dependence-from-finite-centralizer-rank`;
- `leavitt-annulus-north-south-units-have-cyclic-centralizers` and the (V0) section of
  `research/artifacts/zp-pl-interval-subgroup-obstructions-2026-09-13-part3.md`.

Section 1 (groupoid model):
- I checked injectivity of `φ` by padding and disjointness, and the identity `B W B^(-1) = T(W)`.

Section 2 (dynamics), line by line:
- I checked Lemma 2.1(a)–(e) and Lemma 2.2, including the case `d < 0`, where `y = a'_p δ^∞`.
- For the ladder-time argument of Lemma 2.4, I checked that the last minimiser is a ladder time and that the
  length is `L + c_n − c_j`.
- For the backward bookkeeping of Lemma 2.5 (the solver's second weakest step):
  - the increment of `(g^(-1))_*` at `g^(j−i) x` is `−c(g^(j−i−1) x)`, which gives `L + c_(j−i−1) − c_j`;
  - `V_i(v)` is defined from `v` alone;
  - `ε_k^(p_2) = ε_2^(p_k)` follows by Lemma 1.1.
- I checked Lemmas 2.6 and 2.7 and Corollary 2.8.

No gap found.

Section 3 (Theorem A):
- **Lemma 3.1.** The Z-action on the monomial basis is free, and each fibre `(p', O)` has `d_O` orbits.
- **Lemma 3.2(ii)** (the solver's weakest step) holds. `T^(n_m)` of the arrow has endpoints converging to
  `g^(J−j) q, g^(J−j') q' ∈ P_a`. Its middle coordinate is `k + C_x − C_y + m(p'|γ| − p|γ'|)` for large `m`,
  because `c_(J−j)` is locally constant. That coordinate is bounded by `K_W`, hence constant. `W` is compact,
  hence closed, so the limit arrow lies in `W ∩ (P_a × Z × P_a)`, which is empty.
- **Lemma 3.2(iii).** The perturbation `z'` agreeing with `z` on `|a| + |b|` letters gives `α z' ∈ [a] − {x}` and
  `β z' ∈ [b] − {y}`, both in `A+` by Lemma 2.7.
- **Lemma 3.2(iv)** and the localization argument hold.
- **Lower bound.** `κ(1) != 0` because `P_a != ∅`, and a free module over a domain is torsion-free.
- **The bound for `g^(-1)`.** Inverting `F_2[u] − 0` and `F_2[u^(-1)] − 0` gives the same localization.

Examples and consequences:
- **Example 4.** I recomputed the matrix `[[0,1],[c,0]]` and the commutant `a I + b U` by hand. The codes
  `00->100, 010->101, 011->11, 1->0` reproduce `u = s_1 c t_0 + s_0 t_1`.
- **Consequences 4.1–4.3.** They follow from Theorem A and the cited committed nodes. 4.3 uses step 2 of
  `no-diagonal-conjugacy-from-finite-centralizer-rank`, which is proved in that route's body.

Computations:
- I re-ran `thompson_rank.py 3`; the output is identical to `run-N3.log` (about 3.5 min).
- New falsification probe `referee_randtest.py 11 2 12` (log `referee-randtest-seed11-N2.log`). It tested 12 random
  infinite-order elements of `V` with codes of length at most 3. In every case the truncated rank lower bound at
  `R_2` is at most `min(N(g), N(g^(-1)))`, and it attains 2 once. No violation.

Literature:
- arXiv abstract pages for 1107.0672 (BBGGHMS, centralizers in `V_n`), 1603.03618 (Brownlowe–Sørensen) and 1311.3701
  (Clark–Sims) were fetched on 2026-09-16. Titles and authors match.
- Brownlowe–Sørensen Proposition 3.4, taken from the repo artifact of 2026-09-13 and not re-read, already covers
  consequence 4.1 when both commuting elements lie in `U_V`. The solver's literature section missed this.
- (V0) is expected folklore from revealing pairs. The route is a self-contained proof and claims no novelty.
- WebSearch budget was exhausted for this referee too.

**Changed.**
- **Artifact, Lemma 1.5.** Added the missing justification that `1_B * 1_W = 1_(BW)` when `W` is not a bisection
  (left multiplication by `B` is an injective map of `G`).
- **Artifact, §4.1 and §7, and the claim's Consequences.** Added the Brownlowe–Sørensen Proposition 3.4 prior result.
- **This note, §6.** Corrected the literature bullet.
- **Experiments.** Added `referee_randtest.py` and its log.

**Verdict.** Sound. Both direct routes (`requires: []`) are complete proofs. Landing
`v-hyperbolic-periodic-points-from-rigid-words` establishes (V0), and through committed routes
`bs-1-n-does-not-embed-in-thompson-v` and `torsion-free-nilpotent-subgroups-of-thompson-v-are-abelian`. I did
not re-referee those downstream routes. The target `leavitt-unit-centralizers-have-finite-rank` stays OPEN for
linear units.
