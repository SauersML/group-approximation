# Swarm note: fpbs-residual-price-one-non-ah-class-nonuniqueness, 2026-09-16

Agent: swarm-fpbs-residual-price-one-non-ah. The hole worked was the target
itself, `fpbs-residual-price-one-non-ah-class-nonuniqueness`. It was locked
at about 02:30 UTC with a 180 minute TTL and re-locked at 03:18 UTC. Nothing
was committed.

**Outcome: obstruction.** The target is still OPEN. This session establishes
two things about the method the frontier map proposes for it:

- an exact percolation formula along normal subgroups of free groups on their
  trees;
- counterexamples to the divergence crux `D(I)` of the frontier map, Section
  7(d).

## 1. Setup

The target says: if `Gamma` is nonamenable and finitely generated, has fixed
price one, is not acylindrically hyperbolic, and has no infinite amenable
wq-normal subgroup, then every Cayley graph of `Gamma` has `p_c < p_u`. The
node splits the class into two parts:

- **(R0)** torsion groups with no infinite amenable subgroup;
- **(R1)** groups whose infinite amenable subgroups all have proper, almost
  malnormal hulls.

The only unconditional members are in (R0). They are products `H x K` of
infinite finitely generated groups whose amenable subgroups are all finite,
such as `T x T'` for Tarski monsters, or `B(m,n) x B(m',n')` for free Burnside
groups.

**Why a direct resolution is out of reach.** The class contains the products
`T x T'` on *all* of their finite generating sets. A proof would therefore
include Benjamini–Schramm non-uniqueness for every Cayley graph of a product of
two torsion monsters. No available tool gives that:

- **Lyons' theorem** requires a group not of fixed price one, which hypothesis
  1 rules out.
- **Choi–Seo** does not apply, since products are not acylindrically
  hyperbolic.
- **The relative susceptibility equivalence**
  `fpbs-bs-iff-finite-relative-susceptibility` needs an infinite amenable
  wq-normal subgroup, and (R0) has none.
- **Pak–Smirnova-Nagnibeda and Thom** give a gap only for *some* generating
  set of a nonamenable group. See `fpbs-simple-generating-set-with-gap-exists`
  and `fpbs-thom-small-spectral-radius-generating-sets`.
- **`fpbs-expanding-factor-product-strict-thresholds`** is perturbative. It
  needs a Cartesian generating set whose first factor expands strongly relative
  to its adjacency norm and to the degree of the second factor.

So the session followed the one route the frontier map offers that does not
need amenability. Take an infinite subgroup `I`, which in (R0) must be
nonamenable, for instance a factor `H x 1`, and try to prove
`p_c(G) < p_c(I;G)`. By `fpbs-relative-gap-along-any-subgroup-separates` this
suffices. The frontier map (Section 7(d)) decomposes it into two premises:

- **the divergence crux `D(I)`:** `chi^I_p -> infinity` as `p ↑ p_c(I;G)`;
- **critical relative finiteness:** `chi^I_(p_c(G)) < infinity`.

The map lists two sanity checks consistent with `D`: the `Z`-axis in `Z^2`, and
a geodesic line in a tree. The question for this session was whether `D(I)` is
a plausible general principle, and whether critical relative finiteness by
itself could suffice. Both can be settled exactly on free-group trees.

## 2. Literature gate

Search date: 2026-09-16.

**Tools.** The WebSearch budget ran out partway through the session. After
that, the arXiv API returned HTTP 429, and later Crossref requests through the
proxy were reset or timed out. The items below come from arXiv listing pages
and API responses fetched earlier in the session, and from Crossref responses
obtained earlier in the session.

**Result.** I found no preprint that proves `p_c < p_u` for a class meeting the
target. In particular I found none for products of torsion monsters on all
generating sets, and none for fixed-price-one groups that are not
acylindrically hyperbolic and have no amenable wq-normal subgroup. Date-sorted
arXiv API searches on percolation with nonamenable, and percolation with
uniqueness, run through 2026-09-10, found nothing covering the class.

**Relevant items, with dates.**
- **Choi–Seo, arXiv:2508.08932** (August 2025; v2 is cited in the repo).
  Acylindrically hyperbolic groups. The target excludes them by hypothesis 2.
- **Hutchcroft–Pan, arXiv:2409.12283v1** (2024-09-18). Relative thresholds
  `p_c(H;G)`, relative Burton–Keane, and relative sharpness. These are imported
  in `fpbs-hp-relative-sharpness` and in
  `research/artifacts/fpbs/docs/relative-susceptibility-reduction.md`.
- **Hutchcroft–Pan, arXiv:2412.15895v1** (2024-12-20), *Dimension jump at the
  uniqueness threshold for percolation in infinity+d dimensions*. It concerns
  `T x Z^d` and related nonunimodular products, where the gap comes from
  nonunimodularity. It does not apply to the target.
- **arXiv:2502.02560v2** (2025-02-04), *Weighted-amenability and percolation*.
  It covers the nonunimodular setting. I read only its listing summary, and it
  does not touch the class.
- **Bevilacqua–Bowen, arXiv:2510.05459v1** (2025-10-06). A fixed-price-one
  statement for products. In the repo, the (R0) products enter the class through
  `fpbs-residual-class-has-torsion-products`.
- **Donoso-Echenique–Silva, arXiv:2608.20472v1** (2026-08-20). The free Burnside
  groups `B(m,n)` in the stated range have cost one, and their fixed price is
  stated to be open.
- **Slutsky, arXiv:2607.20273v1** (2026-07-22). Direct fixed-price-one criteria.
  Nothing on percolation thresholds.
- **Chu, arXiv:2608.06644** (v1 2026-08-06, v2 2026-09-05), *Applications of the
  cluster graphing*. A short proof that there is no infinite cluster at `p_c` on
  unimodular nonamenable quasi-transitive graphs. It concerns criticality, not
  `p_c < p_u`.

**Classical sources for the tree computation.** These are listed in Section 9
of the artifact.
- *Metadata verified by Crossref on 2026-09-16:*
  - Kesten, Trans. AMS 92 (1959), DOI 10.1090/s0002-9947-1959-0109367-6;
  - Woess, *Cogrowth of groups and simple random walks*, Arch. Math. 41 (1983),
    DOI 10.1007/bf01371408;
  - Northshield, *Cogrowth of arbitrary graphs* (2004),
    DOI 10.1515/9783110198089.2.501;
  - Ortner–Woess, *Non-backtracking random walks and cogrowth of graphs*,
    Canad. J. Math. 59 (2007), DOI 10.4153/cjm-2007-035-1;
  - Glasser–Zucker, PNAS 74 (1977), DOI 10.1073/pnas.74.5.1800.
- *Unverified and not fetched:* Grigorchuk 1980, which is the original cogrowth
  formula; Watson 1939; Pólya 1921; Guivarc'h 1980.

**Novelty.** The cogrowth formula and the cogrowth criterion are classical, and
no novelty is claimed for them. I found no source stating their percolation
reading: `p_c(N;T)` as inverse cogrowth, and the endpoint value of `chi^N`.
Because the search tools were cut off, that absence is weak evidence.

## 3. What was proven

Full proofs are in
`research/artifacts/fpbs-tree-relative-cogrowth-2026-09-16.md`.

**Theorem A** (node `fpbs-tree-normal-relative-threshold-is-inverse-cogrowth`,
direct route `requires: []`).
- *Setting.* `T` is the `(q+1)`-regular Cayley tree of `F_d`, with `q = 2d-1`.
  `N ◁ F_d`, `Q = F_d/N`, and `mu` is the image of the uniform measure on
  `S = {a_i^(±1)}`. Put `rho_Q = limsup mu^(*n)(e)^(1/n)`.
- *Hypothesis.* `rho_Q > 2 sqrt q/(q+1)`.
- *Notation.* `z(s) = s/(1+q s^2)`, `phi(s) = (1-s^2)/(1+q s^2)`, and `s_N` is
  the smaller root of `q s^2 - (q+1) rho_Q s + 1 = 0`.

Conclusions:
- **(A1)** The cogrowth series of `N` has radius `s_N`. For `p <= s_N`,
  `chi^N_p = phi(p) G_Q((q+1) z(p))`, and `chi^N_p = infinity` for `p > s_N`.
- **(A2)** `p_c(N;T) = s_N`. An `N`-infinite cluster exists with probability 0
  below `s_N` and with probability 1 above it.
- **(A3)** `chi^N_(s_N) = phi(s_N) G_Q(1/rho_Q)`. So `D(N)` holds iff `mu` is
  rho-recurrent.
- **(A4)** `p_c(T) < p_c(N;T)` iff `rho_Q < 1`, that is, iff `Q` is nonamenable
  (Kesten).
- **(A5)** `chi^N_(1/q) = ((q-1)/q) G_Q(1)`. This is the mean-field prediction
  of Section 4.2 of `relative-susceptibility-reduction.md`, the quotient Green
  function at 1, now proved on trees with an explicit constant.

**Proof ingredients.**
- *Non-backtracking recursion.* `A_1 A = A_2 + (q+1) I` and
  `A_n A = A_(n+1) + q A_(n-1)`, so `B(s)((1+q s^2) I - s A) = (1-s^2) I`. The
  `(e,e)` entry is Grigorchuk's cogrowth identity
  `F_N(s) = phi(s) Gamma(z(s))`.
- *Radius.* Pringsheim's theorem, applied to `F_N` and to
  `Gamma(z) = sum (q+1)^m p_m z^m`, together with the holomorphic inverse
  function theorem at `s_N`. Here `z'(s_N) > 0` because `s_N < 1/sqrt q`.
- *Endpoint.* Monotone convergence.
- *Threshold.*
  - The lower bound: `chi^N_p < infinity` plus `N`-invariance.
  - The upper bound: factor each `h ∈ N` uniquely as `u w u^(-1)`, with
    cyclically reduced `w ∈ N`. This gives
    `F_N - 1 = C_N (1-s^2)/(1-q s^2)`, so cyclically reduced elements have the
    same growth rate. Then run a Galton–Watson process of concatenated
    cyclically reduced blocks of one length `m` and one first letter. Their open
    geodesic segments are edge-disjoint, so the process is independent.
  - A zero-one law from mixing under `N`-translations upgrades positive
    probability to probability 1.
- *No sharpness.* The threshold proof does not use Hutchcroft–Pan sharpness.

**Examples** (node `fpbs-relative-susceptibility-divergence-crux-fails`).

| `N` | `Q` | `q` | `p_c(N;T)` | `chi^N` at `p_c(N;T)` | gap | `D(N)` |
| --- | --- | --- | --- | --- | --- | --- |
| `[F_3,F_3]` | `Z^3` | 5 | `1/5 = p_c(T)` | `(4/5) G_(Z^3)(1) ≈ 1.2131` | no | fails |
| `<<a_3>>` | `F_2` | 5 | `≈ 0.232461 > 1/5` | `phi(s_N)(3 + sqrt 3) ≈ 3.5241` | yes | fails |
| `[F_2,F_2]` | `Z^2` | 3 | `1/3 = p_c(T)` | `infinity` | no | holds |

In the second row the quotient walk is `(1/3) delta_e + (2/3)` times simple
random walk on `Cay(F_2)`, with:
- `rho_Q = (1 + sqrt 3)/3`;
- `G_Q(1/rho_Q) = 3 + sqrt 3`;
- `s_N = (2 + 2 sqrt 3 - sqrt(8 sqrt 3 - 4))/10`.

**Consequences for the frontier map.**
- *Critical relative finiteness is not sufficient.* `chi^I_(p_c(G)) < infinity`
  does not imply `p_c(G) < p_c(I;G)`, as the first row shows. The hypothesis of
  `fpbs-relative-gap-along-any-subgroup-separates`, finiteness at some
  `p > p_c(G)`, cannot be weakened to `p = p_c(G)`.
- *`D(I)` is not a general principle.* It fails for every normal subgroup of a
  free group on its tree whose quotient walk is rho-transient and has
  `rho_Q > rho_T`.
- *On trees, `D` and the gap are decoupled.* Along normal subgroups the gap
  comes with a *finite* relative susceptibility at the relative threshold
  whenever the quotient walk is rho-transient.
  - The fourth combination, gap together with `D`, has no normal example here.
    The non-normal `<a_1>` has both.
  - If a Guivarc'h-type rho-transience theorem for nonamenable groups holds
    (unverified import), then on trees `D(N)` implies that there is no gap.

**Computations.** `experiments/fpbs-tree-relative-cogrowth-2026-09-16/`.
- *Exact integer checks of the coefficient identity:* `[F_3,F_3]` for `n <= 22`
  and `<<a_3>>` for `n <= 14`, all agreeing.
- *(A5) in row 2:* `sum_(n<=240) f_n 5^(-n) = 1.800000000 = 9/5`.
- *Closed-form values:* those printed above.

Single-threaded, under 2 seconds, exit code 0.

## 4. Approaches and where each dies

1. **Cite a theorem covering the class.**
   - *Where it dies.* Every cited class misses it by definition: Lyons
     (not fixed price one), Choi–Seo (acylindrically hyperbolic), and
     `fpbs-bs-iff-finite-relative-susceptibility` (amenable wq-normal). The
     literature gate found no newer result.
   - *Status.* Unchanged from the node's Attempts section.

2. **Divergence crux `D(I)` along a normal factor `I = H x 1`** in
   `H x K`, with frontier map 7(d).
   - *Where it dies.* On free-group trees, `D(N)` for normal `N` holds exactly
     when the quotient walk is rho-recurrent (A3).
   - The nonamenable-quotient case, which is the tree analogue of `H x 1` in an
     (R0) product, is row 2 of the table: the gap holds and `D` fails.
   - So a proof through `D(I)` would be proving a statement whose tree analogue
     is false in exactly the relevant regime.
   - *Status.* Dead as a black box. This is recorded in
     `fpbs-relative-susceptibility-divergence-crux-fails`.

3. **Critical relative finiteness alone,** `chi^I_(p_c(G)) < infinity`.
   - *Where it dies.* Row 1 of the table: finite at `p_c(T)`, yet
     `p_c(N;T) = p_c(T)`.
   - Finiteness has to be shown at some `p > p_c(G)`, that is, the relative
     susceptibility has to be continued past `p_c(G)`.
   - *Status.* Dead as stated.

4. **Transfer the tree generating-function method** to a general Cayley graph
   of an (R0) product, along `H x 1`.
   - *Where it dies.* Identity (A1) rests on two tree facts:
     - the two-point function `tau_p(o,h) = p^|h|` is multiplicative along the
       unique geodesic;
     - reduced words satisfy the exact non-backtracking recursion.
   - On a graph with cycles, `tau_p` is not a multiplicative path weight, and
     there is no analogue of the substitution `s -> z(s)`.
   - The branching-process lower bound needs edge-disjoint block segments,
     which is false in general.
   - Replacing reduced words with non-backtracking walks gives only upper bounds
     on `tau_p`, and those count many paths per pair.
   - *Status.* No transfer found.

5. **Path-counting (union) bound** `p_c(N;G) >= 1/(d rho(Q))`, from
   `relative-susceptibility-reduction.md` Section 4.1. It holds on every
   Cayley graph for normal `N`.
   - *Where it dies.* It certifies a gap only when `1/(d rho(Q)) > p_c(G)`. That
     is a perturbative condition, and a Tarski monster factor on an arbitrary
     generating set gives no control over it.
   - On the tree it yields `z_Q = 1/((q+1) rho_Q)`, strictly below the true
     `s_N = z_Q (1 + q s_N^2)`.
   - *Status.* Perturbative only. It is the same kind of input as
     `fpbs-expanding-factor-product-strict-thresholds`.

6. **Single torsion monsters** (candidates in (R0) if they have fixed price
   one).
   - *Where it dies.* No infinite proper subgroups, so the only choice is
     `I = Gamma`, where relative susceptibility is ordinary susceptibility and
     gives nothing new.
   - *Status.* Untouched. Any proof for these needs a genuinely new
     non-uniqueness mechanism.

7. **Almost malnormal hulls in (R1),** along maximal cyclic subgroups.
   - *Where it dies.* Theorem A is about normal subgroups. The non-normal check
     `<a_1>` (artifact 6.4) has `p_c(<a_1>;T) = 1` with `D` holding, which says
     nothing about the regime above `p_c(G)` on graphs with cycles.
   - I found no estimate on `chi^I_p` above `p_c(G)` for almost malnormal `I`.
   - *Status.* As in the node.

## 5. Open question left in the artifact

**Question 7.1** of the artifact is not claimed, and no node was created for
it. Let `G` be a Cayley graph of `Gamma`, and let `N ◁ Gamma` be infinite with
`Gamma/N` nonamenable. Is `p_c(G) < p_c(N;G)`?

- (A4) answers yes for `Gamma = F_d` on its standard tree.
- A yes answer, together with `fpbs-relative-gap-along-any-subgroup-separates`
  (`p_c(N;G) <= p_u(G)`), gives `p_c < p_u` on every Cayley graph of every
  `H x K` with `H` infinite and `K` nonamenable. That covers all the (R0)
  products currently known to be members.
- It would say nothing about single monsters.
- The question is at least as hard as Benjamini–Schramm for all Cayley graphs of
  `Z x F_2`-type groups (take `N = Z x 1`). I did not check whether that case is
  known.

The tree case suggests attacking it by bounding `chi^N_p` directly just above
`p_c(G)`, not through `D(N)`. The mean-field value (A5), `chi^N_(p_c) =`
`((q-1)/q) G_Q(1)`, points to the quotient Green function at 1 as the
controlling quantity. For `K` nonamenable that function is finite, with room to
spare, since `G_Q(w) < infinity` for `w < 1/rho_Q`. A proof would have to show
that this room survives the passage from trees to graphs with cycles.

**For the next agent.**
- A promising test case is a Cayley graph of `F_2 x F_2` on a non-product
  generating set, along `F_2 x 1`. I did not find its relative threshold in the
  repo, and the graph is not a tree.
- A tree-like graph with cycles, for example a free product of finite groups,
  could show whether (A1) survives in some form.

## 6. Files

Created in this session. Nothing was committed, and no existing file was
modified.

- `research/artifacts/fpbs-tree-relative-cogrowth-2026-09-16.md`: full proofs
  of Theorem A and Corollaries B, C and D, the consequences, Question 7.1, and
  references.
- `research/fpbs-tree-normal-relative-threshold-is-inverse-cogrowth.md`: a
  claim, ESTABLISHED.
- `research/fpbs-tree-normal-relative-threshold-is-inverse-cogrowth-proof.md`:
  a direct route, `requires: []`.
- `research/fpbs-relative-susceptibility-divergence-crux-fails.md`: a claim,
  ESTABLISHED.
- `research/fpbs-relative-susceptibility-divergence-crux-fails-proof.md`: a
  route, requiring the claim above.
- `experiments/fpbs-tree-relative-cogrowth-2026-09-16/verify_cogrowth_identity.py`
  and `output.txt`.
- This note.

**Weakest steps,** for a referee to check first:
- *The analytic endpoint argument* (artifact Lemma 2.3). The two Pringsheim
  continuations, with the local inverse of `z` at `s_N`, should be checked
  carefully.
- *The independence and zero-one step* of the branching-process upper bound
  (Proposition 4.3).

## Referee (2026-09-16)

**What was checked.**
- *All eight files, read in full.* I also read the frontier map, Section 7(a)–(d),
  and `relative-susceptibility-reduction.md`, Sections 1 and 4.1–4.2. The
  paraphrases of `D(I)`, of the crux implication, and of Hutchcroft–Pan's
  Definition 1.2 of `p_c(H;G)` match the repo sources.
- *Lemma 2.1 and Lemma 2.2, line by line.* This includes the `n = 1` case
  `A_1 A = A_2 + (q+1) I`, and the domination bound in Step 2 of Lemma 2.3.
- *Lemma 2.3, the solver's flagged weakest step.* It is correct.
  - Step 3: `U` is open and contains `[0, s_N)`, the neighbourhood `V` of the
    compact set `[0, R_N]` is convex, and gluing on `V ∩ D(0,R_N)` contradicts
    Pringsheim's theorem at `R_N > 0`. Here `R_N >= 1/q`, because
    `f_n <= (q+1) q^(n-1)`.
  - Step 6: the local inverse is real on real points near `z_Q`, and
    `V_0 ∩ D(0, z_Q)` is convex, so the identity theorem applies and the
    contradiction with Pringsheim's theorem at `z_Q` is valid.
- *Lemma 4.2.*
  - The conjugator count `(q-1) q^(k-1)` is right: the two excluded letters are
    `first(w)^(-1)` and `last(w)`.
  - The factor `M(s) = (1-s^2)/(1-q s^2)` is right.
  - The radius equality is right.
- *Proposition 4.3, the second flagged step.* It is correct.
  - Blocks with a common first letter concatenate without cancellation.
  - The segments from distinct `g in L_k` are edge-disjoint, because their
    first `km` letters differ.
  - The segments lie outside `F_k`, since every segment edge has an endpoint of
    length `> km`.
  - The offspring law is `xi`, and the zero-one law by cylinder approximation
    and translation by long `n in N` is sound.
- *Examples.*
  - For `Z^3` and `Z^2`: the box and Cauchy–Schwarz bound giving `rho_Q = 1`,
    and the factorizations `(5s-1)(s-1)` and `(3s-1)(s-1)`.
  - For the lazy walk on `F_2`: the tree Green function `6/(2+sqrt(16-12w^2))`,
    the lazy substitution, `rho_Q = (1+sqrt3)/3`, `G_Q(1/rho_Q) = 3+sqrt3`, and
    `s_N`. The root residual is `2e-16`, and
    `chi^N_(s_N) = 3.5241479...`.
  - `phi(1/q) = (q-1)/q` and `(q+1) z(1/q) = 1`.
- *The script.* I re-ran it, and the output is identical to `output.txt`. As an
  independent check, I also wrote a separate brute force for `[F_2,F_2]`
  (`q = 3`, `Q = Z^2`, `n <= 16`). The coefficients agree exactly with (2.2).
- *Duplicates.* `bin/cairn search --similar` on both claims and a keyword
  search for "cogrowth" found no duplicate.
- *Literature.* I fetched the arXiv abstract and HTML of Hutchcroft–Pan
  2409.12283v1: it has no tree or cogrowth computation of `p_c(H;T)` and no
  discussion of divergence at `p_c(H;G)`. The WebSearch budget was exhausted, so
  I could not run a broader novelty search.

**Changes.**
- *Claim `fpbs-tree-normal-relative-threshold-is-inverse-cogrowth`.* Novelty was
  softened. Item 2 is of the same kind as Lyons' `p_c = 1/br` on trees
  (unverified) and is no longer called new, and the absence of the endpoint
  evaluations from the literature is marked as weak evidence.
- *Claim `fpbs-relative-susceptibility-divergence-crux-fails`.*
  - The "gap iff nonamenable quotient" consequence is now stated under
    `rho_Q > rho_T`. That every `N ≠ 1` satisfies this is attributed to Kesten
    and marked not re-verified.
  - The Kesten amenability reading is marked as cited interpretation.
  - The methodological bullet is marked heuristic.
- *The matching route bullet* was updated in the same way.
- *Artifact.*
  - Corollary C: `≈ 3.5242` was corrected to `≈ 3.5241`.
  - Remark 5.1 was softened, and a Lyons attribution was added, marked
    unverified.

**Verdict.** The mathematics is sound. Theorem A is proved as stated, under the
explicit hypothesis `rho_Q > rho_T`. The direct route (`requires: []`) is
complete. It uses only Pringsheim's theorem, the identity theorem and the
inverse function theorem, Galton–Watson survival, and cylinder approximation.
The examples route follows from Theorem A, with a Fourier sketch of Pólya's
theorem for `Z^3` and the classical return probability `p_(2n)` for `Z^2`. The
target `fpbs-residual-price-one-non-ah-class-nonuniqueness` stays OPEN. What
this work shows is only that the `D(I)` route of frontier map 7(d) cannot be
used as a black box, and that critical relative finiteness alone does not give
a relative gap. **Landed with small fixes.**
