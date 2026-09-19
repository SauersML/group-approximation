---
rg: 2
id: thompson-f-32-term-cogrowth-bound-is-the-moment-optimum
kind: claim
title: The 32 published cogrowth terms of Thompson's F certify ||P|| > 0.910677539452 and provably nothing more
distinct_from:
  thompson-f-norm-bound-from-epg-32-term-moments: that establishes the lower bound 0.910677 from the same 32 terms; this proves the matching ceiling (an explicit 16-atom measure with exactly those 32 moments whose support tops out at the same value), gives the exact optimum theta*(N) for every N <= 31, and prices the only competing certificate class (finite windows).
  thompson-f-moment-data-cannot-certify-nonamenability: that shows no finite list of exact counts can prove ||P|| < 1, the upper side of the moment route; this pins the lower side, namely the best lower bound the counts can give at each length.
  thompson-f-random-walk-norm-certified-lower-bound: that is the 0.880541 bound from counts computed in this repository to word length 30; that value is the N = 15 row of the table here, and is shown to be the exact optimum at that length.
artifacts:
  - experiments/thompson-f-cogrowth-2026-09-18/moment_ceiling.py
  - experiments/thompson-f-cogrowth-2026-09-18/moment_ceiling.json
  - experiments/thompson-f-cogrowth-2026-09-18/jacobi_ceiling.py
  - experiments/thompson-f-cogrowth-2026-09-18/jacobi_ceiling.json
  - experiments/thompson-f-cogrowth-2026-09-18/f_elements.py
  - experiments/thompson-f-cogrowth-2026-09-18/f_elements_selftest.json
  - experiments/thompson-f-cogrowth-2026-09-18/ball_eigen.py
  - experiments/thompson-f-cogrowth-2026-09-18/ball_eigen.json
  - experiments/thompson-f-cogrowth-2026-09-18/ball_boundary.py
  - experiments/thompson-f-cogrowth-2026-09-18/isoperimetric.json
  - experiments/thompson-f-cogrowth-2026-09-18/exchange_rate.py
  - experiments/thompson-f-cogrowth-2026-09-18/exchange_rate.json
  - experiments/thompson-f-cogrowth-2026-09-18/schreier_feasibility.py
  - experiments/thompson-f-cogrowth-2026-09-18/schreier_feasibility.json
---

**OPEN** (demoted 2026-09-18 by referee audit, before it was ever landed as established:
lens 2 and lens 3 refuted, lens 1 survived. The headline `N = 31` result below was
reproduced independently by all three referees and none of them doubts it; what was
refuted is the claim's reach — the even-`N` rows rest on an unnamed import, now split out
as the open prerequisite `even-degree-localizing-hankel-attains-truncated-moment-optimum`,
and two Attempts bullets priced their alternatives by inverting an inequality. See
`## Attempts` for the verbatim referee reasons and for what was corrected in place.)

Read everything below with that caveat. Statements marked **(odd-`N` only)** are
unaffected and were confirmed by all three lenses.

Let `P = (x_0 + x_0^{-1} + x_1 + x_1^{-1})/4` on `l^2(F)`, let `c_n` be the
number of words of length `2n` in `x_0^{+-1}, x_1^{+-1}` that are trivial in `F`, and let
`M_n = c_n/16^n`, the moments of the spectral measure `mu_2` of `P^2` at `delta_e`. For
`N <= 31` put

    theta*(N) = min { sup supp nu : nu a positive measure on [0, oo) with moments M_0..M_N }.

1. **Sharp value (odd-`N` only; confirmed by all three referee lenses).**
   `theta*(31) = 14589790647431/17592186044416 + eps` with
   `0 <= eps < 2^-44`; that is, `theta*(31) = 0.8293335808634...`, and

       ||P|| > 227669384863/250000000000 = 0.910677539452,

   while **no bound above `0.910677539453` follows from `c_0, ..., c_31`**: the 16-atom
   measure printed in `jacobi_ceiling.json` (nodes `0.00221..., ..., 0.829333580863`, all
   weights positive) has exactly those 32 moments and support inside `[0, theta*(31)]`.
   The certified value and the ceiling agree to 13 digits, so the moment route on the
   published data is exhausted, not merely unexploited.

2. **The whole cost curve.** A value `theta*(N)` is computed for every `N <= 31`
   (`moment_ceiling.json`). **Odd `N` is exact and optimal; even `N` is a certified lower
   bound whose optimality is open** (prerequisite
   `even-degree-localizing-hankel-attains-truncated-moment-optimum`; the route's step 6
   cited "the classical even-degree Hausdorff condition" with no author, reference or
   statement, and the hypotheses needed are not those of that name). Rows below are marked
   accordingly. In terms of `rho_N = sqrt(theta*(N))`:

   | N (terms) | word length | `rho_N` | `mu >= 16 theta*(N)` | status |
   |---|---|---|---|---|
   | 5 | 10 | 0.797959 | 10.1878 | exact optimum |
   | 10 | 20 | 0.856705 | 11.7431 | lower bound; optimality open |
   | 15 | 30 | 0.880542 | 12.4057 | exact optimum |
   | 20 | 40 | 0.894096 | 12.7905 | lower bound; optimality open |
   | 24 | 48 | 0.901533 | 13.0042 | lower bound; optimality open |
   | 28 | 56 | 0.907207 | 13.1684 | lower bound; optimality open |
   | 31 | 62 | 0.910678 | 13.2693 | exact optimum |

   The three earlier certified values in this graph (`0.880541` at `N = 15`, `0.901532` at
   `N = 24`, `0.910677` at `N = 31`) are reproduced. `N = 15` and `N = 31` are odd and are
   proved optimal at their lengths; `N = 24` is even, so it is certified as a bound but its
   optimality waits on the prerequisite. The increments fall off like `N^{-1.6}`: the last
   term bought `0.0011`.

3. **Extrapolated price (not a theorem).** A three-point power-law fit
   `rho_N = L - c N^{-alpha}` on the exact rows `N = 15, 23, 31` gives `L = 0.96457`,
   `alpha = 0.6119`. Under that law, certifying `||P|| > 0.92` needs about **42** exact
   cogrowth terms, `> 0.93` about **64**, and `> 0.95` about **263**. Elvey Price and
   Guttmann needed a dedicated algorithm to reach 32. The fitted limit `0.96457` is close
   to their extrapolation `mu ~ 15.0`, i.e. `||P|| ~ 0.9682`, which is evidence that the
   certified sequence is converging to the true value and not to something smaller.

4. **The competing class is priced too.** For a finite vertex set `A` of
   `Cay(F, {x_0^{+-1}, x_1^{+-1}})`, `lambda_max(A_A)/4 <= ||P||`; this is the
   NPA/matrix-moment relaxation of the same problem, and it is the standard way to use more
   than the numbers `c_n` (for another, see the Schreier entry under Attempts). On the
   4-regular tree the window bound at radius `r` and the moment bound from `c_0..c_r` agree
   to `10^-13` at `r = 4, 6, 8, 10, 12` (`exchange_rate.json`). The offered reason — the top
   Dirichlet eigenvector of a ball is radial, and the radial subspace is the Krylov space of
   `delta_e`, so the Rayleigh maximum is the largest Gauss node of the moment problem — is
   proved in the route only for *odd* truncation, and all five checked radii are even; at
   even `r` the identification is the same open prerequisite as item 2. So the agreement is
   **measured, not proved**. In `F` the window is better, but only by the measured excess

   | r | \|B_r\| | window | moments at N=r | excess |
   |---|---|---|---|---|
   | 6 | 1381 | 0.816861 | 0.816098 | 0.000763 |
   | 8 | 11237 | 0.841931 | 0.840689 | 0.001242 |
   | 10 | 88253 | 0.858422 | 0.856705 | 0.001717 |
   | 12 | 676061 | 0.870273 | 0.868181 | 0.002092 |

   The excess grows by `0.00022` per unit radius while `|B_r|` grows by a factor `2.76`.
   Extrapolating both, a ball window would first match the 32-term moment bound at radius
   about **27**, i.e. about `3 x 10^12` vertices. *That last sentence is an extrapolation,
   not a measurement* (the measured excess increments are in fact falling, `0.000479`,
   `0.000475`, `0.000375` per two radii, so a linear law over-credits windows and radius 27
   is if anything optimistic for them). Windows are therefore not a cheaper road to the
   same number, let alone a better one.

5. **Sphere sizes** of `Cay(F, {x_0, x_1})`, recomputed here with exact tree-pair normal
   forms cross-checked against exact PL arithmetic: `1, 4, 12, 36, 108, 314, 906, 2576,
   7280, 20352, 56664, 156570, 431238` (growth factor `2.754` at the last step).

**Scope and honesty.**
- Lower bound only, and far from the target: `1 - 0.910678 = 0.0893`, and `||P|| = 1` is
  exactly amenability of `F`. By
  `thompson-f-moment-data-cannot-certify-nonamenability` no finite exact data can prove
  `||P|| < 1`. The two statements bracket the route: finite cogrowth data can only push a
  lower bound up, and this node says how fast and how far, namely `N^{-0.61}` and not far.
- The ceiling in (1) says that *every certificate whose only input is the positivity of a
  measure with the moments `M_0..M_31`* stops at `0.9106775394526`. It does not say that
  no other computation can do better: a certificate that reads the group (more cogrowth
  terms, off-diagonal counts `w_n(g)`, a window, a Schreier graph) is not covered.
- Nothing here bears on which way the amenability question goes.
- Novelty: the number `0.910677` is Elvey Price-Guttmann's `b_31` and was already recorded
  in `thompson-f-norm-bound-from-epg-32-term-moments`. New here are the matching ceiling
  with its explicit extremal measure, the table for all `N` (exact and optimal at odd `N`;
  a certified lower bound at even `N`), and the window/moment exchange rate.
- Status, after the 2026-09-18 referee pass: item 1 and the odd rows of item 2 are
  refereed-sound and were reproduced three times independently; item 2's even rows wait on
  `even-degree-localizing-hankel-attains-truncated-moment-optimum`; item 3 was always
  labelled "not a theorem"; item 4's `F` measurements stand but its tree calibration is
  measured rather than proved and its radius-27 figure is an extrapolation; item 5 stands.

Proof route: `thompson-f-32-term-cogrowth-bound-is-the-moment-optimum-proof` (kept as the
attempt; it now requires the open claim
`even-degree-localizing-hankel-attains-truncated-moment-optimum`).

## Attempts

- **2026-09-18: refereed and demoted (lens 2 and lens 3 refuted; lens 1 survived).** The
  route and all fourteen experiment artifacts are kept. All three lenses independently
  reproduced the headline: `moment_ceiling.py` and `jacobi_ceiling.py` reproduce
  bit-identically against the stored JSON; lens 1 re-verified the load-bearing exact facts
  with a *different* algorithm (leading principal minors by exact-`Fraction` elimination
  rather than the script's `LDL^T`) and rebuilt `J` independently as the matrix of
  `q -> pi(xq)`, confirming `M_0 <J^k e_0, e_0> = M_k` for every `k = 0..31`; lens 3
  confirmed the 16 positive weights, nodes, max relative moment error `7.3e-15`, the
  `f_elements.py` self-test and `ball_eigen.py` to `r = 8`. Nobody disputes
  `||P|| > 0.910677539452` or the matching ceiling. Three failures, by lens:
  - **Lens 2, decisive — reversed import, falsely attributed.** The docstring of
    `experiments/thompson-f-cogrowth-2026-09-18/ball_boundary.py` asserted
    "The Kesten--Dodziuk inequality (proved in the route node of this experiment) gives
    `||P|| >= sqrt(1 - (b(A)/4)^2)`, `mu = 16||P||^2 >= 16 - b(A)^2` ... So a single finite
    set with a small edge boundary is a certificate". Every clause is wrong. Dodziuk gives
    `sup spec P <= sqrt(1 - (h/4)^2)`, i.e. `h <= 4 sqrt(1 - ||P||^2)`: it turns a *lower*
    bound on `h` into an *upper* bound on `||P||`. The docstring flipped the inequality on
    `||P||` and substituted `b(A)`, which is only an upper bound on `h`, into a slot needing
    a lower bound — and cited step 8 of the route, which proves exactly the opposite. Not
    harmless: with the node's own `b = 1.40743` the false formula yields `||P|| >= 0.9361`
    and `mu >= 14.02`, above this node's own certified `0.910677539452` and above its
    ceiling; with Belk-Brown sets (`b -> 1/2`) it would yield `||P|| >= 0.998`. No stored
    JSON was corrupted — the formula never reached the code. **Corrected in place.**
  - **Lens 2, second — unfilled step, undisclosed at claim level.** Route step 6 conceded
    that optimality at even `N` is "the classical even-degree Hausdorff condition, which is
    **not** re-proved here", with no author, reference or statement, while this node
    asserted under the banner "every asserted inequality is exact integer or rational
    arithmetic" that `theta*(N)` is computed exactly for every `N <= 31` and that the
    featured `0.901532` at `N = 24` is "optimal at its length" — `N = 24` is even. The
    hypotheses actually needed differ from the name invoked: truncated Stieltjes/Hausdorff
    on a *moving* interval `[0, theta]`, joint positivity of the Hankel and localizing
    matrices, and closedness of the moment cone on a compact interval (Markov-Lukacs /
    Krein-Nudelman, cited elsewhere in this repository but not there). The same gap carries
    item 4's bolded tree calibration, checked only at `r = 4, 6, 8, 10, 12`, all even.
    **Split out as the open prerequisite
    `even-degree-localizing-hankel-attains-truncated-moment-optimum`**; the even rows are
    restated as lower bounds, the odd rows and the `N = 15, 23, 31` fit are untouched.
  - **Lens 3 — the surviving accelerator was priced by inverting an inequality**, the same
    direction error this node correctly diagnoses for Cheeger one bullet earlier.
    `|Hg cap B_r| <= |H cap B_{2r}|` gives `|Sch_r| >= |B_r|/|H cap B_{2r}|`, a *lower*
    bound; the asserted `1.85` per radius came from dividing by `|H cap B_r|` instead, and
    the measured rates give `2.76/1.48^2 = 1.26`, so "about `10^7` vertices" was
    unsupported and the honest bracket is `10^3` to `10^12`. `schreier_feasibility.json`'s
    own pass criterion also fails (`coset_growth_last = 3.02 > 2.76`), and its sentence
    calling that a bound on Schreier-ball growth is invalid, a ratio of upper bounds
    bounding no ratio. **Corrected in place** in this node, in
    `research/thompson-f-is-not-amenable.md` and in the JSON's `reading` field; the
    Schreier-ball growth rate is now recorded as a second exact blocker alongside the coset
    normal form.
  - **Minor, recorded not repaired.** Route step 2 calls `pi` "the orthogonal projection
    onto `V`", an abuse since `R[x]_{<=16}` carries no complete form (`M_32` is unknown);
    `pi` must be defined by the Riesz pairing `<pi(z), q> = L(zq)`, which is what makes the
    `k = 31` identity legitimate (lens 1, one-line fix, noted here rather than silently
    rewriting the refereed text). Item 1's phrase "no bound above `0.910677539453` follows
    from `c_0, ..., c_31`" is broader than what is proved, though the Scope section does
    restrict it correctly.
  To re-establish: prove or properly cite
  `even-degree-localizing-hankel-attains-truncated-moment-optimum`, or restate the node with
  odd `N` only — the headline `N = 31` needs nothing else, and lens 1 and lens 3 both say so
  explicitly.

- **Isoperimetric (Cheeger) certificates.** For a finite `A`, `b(A) = |dA|/|A|` bounds the
  Cheeger constant `h <= b(A)`, and the Kesten-Dodziuk inequality is
  `h <= 4 sqrt(1 - ||P||^2)`. That runs the wrong way: an upper bound on `h` gives only the
  Dodziuk side `||P|| >= 1 - b(A)/4`, which is the Rayleigh quotient of the indicator of
  `A` and is dominated by `lambda_max(A_A)/4`. Minimising `b` over subsets of a ball is the
  maximum-density-subgraph problem; Charikar peeling plus exact local search inside `B_11`
  (`isoperimetric.json`) finds a 41136-vertex set with `b = 1.40743` (average inner degree
  `2.5926`), hence `h(F, {x_0, x_1}) <= 1.40743` exactly, but only `||P|| >= 0.6481`.
  (Peeling is a `1/2`-approximation, not an exact solver, and `isoperimetric.json` shows it
  was suboptimal here — `41104`/`1.408525`, improved by local search to `41136`/`1.407429`.
  So `41136` is the best set *found*, not the proved maximum-density subgraph; nothing
  depends on that, since `h <= b(A)` and `||P|| >= 1 - b(A)/4` hold for any explicit set.
  The repository's own record is better anyway: Belk-Brown marked-forest sets, cited in
  `thompson-f-norm-bound-from-epg-32-term-moments`, drive average inner degree to `7/2`,
  i.e. `h <= 1/2` and indicator bound `||P|| >= 7/8` — which only sharpens the point that
  the class still dies.) Dies at the direction of the Cheeger inequality: the square-root
  improvement is available only when a *lower* bound on `h` is known, and a lower bound on
  `h` is what non-amenability would supply, not what a finite set gives.
- **Extending the exact counts.** `c_n = sum_g m_n(g)^2` where `m_n` is the distribution of
  the walk after `n` steps, so `c_32` needs the support of `m_32`, about `2.76^32 ~ 10^13`
  elements. Dies on resources, as the previous wave already recorded.
- **The one accelerator that survives, with its price measured.** For `H <= F` the Cayley
  graph covers `Sch(F/H, S)`, so `||P_Sch|| >= ||P||`, and for *amenable* `H` the
  quasi-regular representation is weakly contained in the regular one (Kesten), so
  `||P_Sch|| = ||P||` and a window in `Sch` certifies `||P||` itself — in a graph whose balls
  are exponentially smaller. Take `H = <x_0, h>` with `h` the one-bump element on `[1/2,3/4]`
  (`|h| = 6` in `F`); its `x_0`-conjugates are supported on the disjoint intervals
  `[2^{-n-1}, 2^{-n}]` and `[1-2^{-k}, 1-2^{-k-1}]` (verified in
  `schreier_feasibility.json`), so `H = Z wr Z` is metabelian and amenable. Measured
  (`schreier_feasibility.py`, exact element arithmetic):
  `|H cap B_r|` = `1, 3, 5, 7, 9, 11, 15, 25, 43, 69, 105, 155` for `r = 0..11`, growth ratio
  `1.48` at the last step against `2.774` for `|B_r|`.
  **The saving is not measured, in either direction (corrected 2026-09-18; referee lens 3).**
  A coset meets `B_r` in at most `|H cap B_{2r}|` elements, so
  `|Sch_r| >= |B_r| / |H cap B_{2r}|` — a *lower* bound on the Schreier ball, not an upper
  one. At the measured rates that gives at best `2.76/1.48^2 = 1.26` per radius, so radius
  `27` costs *at least* about `10^3` vertices; the trivial upper bound is the Cayley count
  itself, `2.76^27 ~ 10^12`. The honest bracket is therefore `10^3` to `10^12`, and the
  earlier figures `1.85` per radius and `10^7` vertices were wrong — they came from
  dividing by `|H cap B_r|` where `|H cap B_{2r}|` is required, and nothing in the artifact
  measures them. Nor does `schreier_feasibility.json` settle it from above: its only
  computed quantity, `cosets_meeting_ball_upper_bound` =
  `1, 3, 9, 26, 74, 205, 562, 1523, 4109, 11046, 30276, 91519`, is an upper bound on the
  coset count whose own ratios are `2.7-3.0` (`3.02` at the last step), so that file's
  stated pass criterion — "if it is below the Cayley growth `2.76`" — is **not met**, and a
  ratio of upper bounds bounds no ratio anyway.
  Not attempted here, and there are now two blockers, both exact: **a canonical form for the
  cosets `Hg`**, i.e. a decidable normal form for `Z wr Z` inside `F` that allows a BFS
  directly in `F/H`; and **the growth rate of the Schreier ball itself**, which is the thing
  that would decide whether this is an accelerator at all. Also unknown and not measured:
  whether the window bounds in `Sch` converge at the same rate per radius as in `Cay`; the
  two graphs have the same operator norm but different spectral measures at the base point.
  The mechanism is sound (`Cay` covers `Sch`, so `||P_Sch|| >= ||P||`; `H = Z wr Z` is
  amenable, so Kesten gives equality) — it is only the price that is unpriced.
- **Lower bounds on the unknown higher moments.** Adding constraints `M_{m+n} >= M_m M_n`
  changes nothing: for *any* probability measure on `[0, oo)` that inequality is Chebyshev's
  correlation inequality, so it is implied by the moment data already. Dies: the constraint
  is vacuous. The only supermultiplicativity consequence, Fekete's `mu >= c_31^{1/31}`,
  gives `mu >= 10.56`, far below `13.269`.
