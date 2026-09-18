---
rg: 2
id: rich-2to1-perfect-completeness-conjecture
kind: claim
title: Rich 2-to-1 games are NP-hard to distinguish between satisfiable and near-zero value (Braverman--Khot--Minzer Conjecture 7)
distinct_from:
  rich-2to1-games-conjecture: that is Gap-Rich[1-eps, delta], equivalent to UGC; this is Gap-Rich[1, delta], strictly stronger than UGC, and its YES instances are satisfiable, which is exactly what the tractable-skeleton kill exploits.
  rich-2to1-conjecture-is-equivalent-to-ugc: that equivalence is for the imperfect-completeness conjecture only; nothing converts this perfect-completeness version into UGC or back.
---

**OPEN.** Braverman, Khot and Minzer, *On Rich 2-to-1 Games*, ITCS 2021
(LIPIcs vol. 185, Article 27, doi `10.4230/LIPIcs.ITCS.2021.27`),
Conjecture 7, verbatim:

> "Rich 2-to-1 Games Conjecture with Perfect Completeness. For every constant
> δ>0, there is a sufficiently large integer n such that
> Gap-Rich-2-to-1_n[1, δ] is NP-hard."

Here a 2-to-1 game has left alphabet `[2n]` and right alphabet `[n]`. It is
*rich* when, at every left vertex, the pairing induced by a uniformly random
incident edge is uniform over all perfect pairings of `[2n]` (BKM
Definition 5).

**Relation to the rest of the graph.**

* It implies `rich-2to1-games-conjecture`. The identity map reduces
  Gap-Rich[1, delta] to Gap-Rich[1-eps, delta]. So it implies
  `unique-games-conjecture` through `rich-2to1-conjecture-is-equivalent-to-ugc`.
  The route is `rich-2to1-from-perfect-completeness`.
* It is strictly stronger than UGC as a statement. Braverman, Khot, Lifshitz and
  Minzer, *An invariance principle for the multi-slice, with applications*,
  arXiv:2110.10725, state it as their Conjecture 1.17 and remark: "Conjecture
  1.17 is strictly stronger than the Unique-Games Conjecture, and thus can be
  thought of as a variant of it with perfect completeness."
* It is the hypothesis that the perfect-completeness applications need. BKM
  write that "the additional advantage of using the Rich 2-to-1 Games
  Conjecture could be that this conjecture could hold even with perfect
  completeness", and list coloring 3-colorable graphs with constantly many
  colors and hardness of satisfiable CSPs. Under it, BKLM derive hardness of
  telling 3-colorable graphs from graphs with no independent set of size
  `o(1)`, and satisfiable `r`-CSPs from `(2r+1)/2^r + o(1)`-satisfiable ones.

**What is known to fail.** By
`perfect-completeness-rich-2to1-tractable-skeletons-are-in-p`, no NP-hardness
proof can output YES instances that carry, computably from the reduction's run,
any of the following with edge mass above `delta`:

* a constant-seed forcing closure, which covers every BKM right merge
  `Psi(U)` and partial merges with separating pairings;
* a certified affine-local merge skeleton `U_W(G)`, when
  `delta < 1 - alpha_k`;
* an affine label-cover encoding, which covers an `F_lin`-stage start of the
  BKM `F_j` enrichment chain.

So Theorem 8's direction from UGC to Rich cannot be run with perfect
completeness. The survivors are listed in that node.

## Attempts

* **Run the known rich-producing constructions with perfect completeness.** The
  constructions are right merges `Psi(U)` or partial merges, certified
  affine-local wrappers, and an affine `F_lin`-stage start of the `F_j` chain.
  **Dead (2026-09-17)** -- route
  `rich-2to1-perfect-completeness-via-tractable-skeletons`, killed by
  `perfect-completeness-rich-2to1-tractable-skeletons-are-in-p`.
  - Invariant: tractable skeleton mass.
  - Step: completeness. It makes the skeleton satisfiable, and skeleton search
    is polynomial.
* **Deferred: re-encoding compositions (survivor P1).** A long-code or
  dictatorship-test composition with `o(1)` constant-seed forcing closure and no
  unique-game or affine skeleton is the only shape the kill leaves. Two open
  questions:
  - Which soundness analysis would handle it? The BKLM multi-slice invariance is
    the analytic candidate.
  - What hard satisfiable source would it start from?
* **Evidence question: answered no for the GKOPTW vector universe
  (2026-09-17).** The question was whether the Guruswami--Khot--O'Donnell--
  Popat--Tulsiani--Wu perfect-SDP 2-to-1 gap instances (ICALP 2010) are rich,
  or can be enriched without a merge skeleton.
  - **Not rich.** Every GKOPTW edge pairing is the coset pairing of one `<γ>`,
    so only `K - 1` of the `(K-1)!!` pairings occur at a left vertex.
  - **No enrichment.** By `walsh-frame-rich-2to1-games-have-value-near-one`,
    every rich game whose perfect SDP solution uses Walsh frames
    `f_u chi_c / K` (the GKOPTW universe, any graph, any bijections) has
    `val >= 1 - B(K)`, with `B(512) < 0.011`. So no such game is a gap below
    `delta < 1/128`.
  - Invariant: forcing edge mass.
  - Step: the pair-sum identity forces co-neighbours to share differences. A
    forcing difference set (rich pairings are forcing with probability
    `1 - B(K)`) makes the frame twist a character, and one common vector per
    component labels every forcing edge.
  - Survivor: a basic-SDP gap for Conjecture 7 must use left frames that are not
    twisted Walsh bases in any common coordinate system. The natural candidate
    is the *rotated-frame universe game*:
    - left vertices are orthogonal `2n`-frames with squared norms `1/2n`;
    - right vertices are the `n`-frames of their pair sums;
    - neighbours of a right vertex `v` are the frames `(y_b +- R e'_b)/2`, for
      `R` in the orthogonal group of `span(y)^perp`.

    In the continuum version, label permutations act by Haar-preserving
    orthogonal maps, which is the heuristic reason for richness, and the frames
    themselves are a perfect SDP solution. A finite rich discretisation and its
    integral value are **open**, and nothing here is established.
* **Rotated-frame universe: soundness reduced to one stability bound
  (2026-09-17).**
  - By `rotated-frame-value-reduces-to-partition-stability`
    (ESTABLISHED), the continuum game `U_(n,d)` is rich. Its frames are a perfect
    basic-SDP solution. Every strategy satisfies
    `val^4 <= 4 Stab_T(rho_A)`, where `rho_A` is the `S_2n`-average of the left
    strategy and `T` resamples pair differences for a uniform pairing.
  - The proof squares the right-vertex plurality and realises the second
    neighbour as a relabelled resampling of the first. `T` has a huge invariant
    algebra (functions of the frame sum `s`), but balance makes it contribute
    exactly `1/(2n)`.
  - Remaining premise, OPEN:
    `pair-resampling-walk-balanced-partitions-are-unstable`.
  - Obstruction recorded there: no uniform Ornstein--Uhlenbeck domination, since
    degree-`k` eigenvalues have a floor `1/((2n-1)(2n-3))`.
  - Conditional result (Gaussian model): `lambda_k <= 2^(-k/2) + O(n^(-2))`
    implies stability `<= (2n)^(-0.1716) + O(n^(-2))`.
  - Numerics: `lambda_k ~ 2^(-ceil(k/2))` for `k <= 4`, `n <= 6`. The linear
    strategy's stability decays about like `n^(-0.38)` over `n <= 1024`.
  - Survivors:
    - prove (H1)/(H2) by transplanting global hypercontractivity from the
      multi-slice or `S_n`;
    - then discretise to a finite rich instance.
* 2026-09-17, e-ugc-pull-transplant (transplanter via finite-models): split the
  rotated-frame survivor into prerequisites that can fail separately, and closed
  the discretisation half.
  - Established: `rotated-frame-universe-discretises-to-robust-rich-2to1-sdp-gaps`.
    Pushing `U_n` forward along a fine Borel partition gives, at every fixed
    `n` and every `eta > 0`, a finite rich instance with basic SDP value at
    least `1 - eta` and value at most `val(U_n) + eta`. Richness is exact
    because the pairing is independent of the left frame, and labellings lift
    to Borel strategies.
  - Open, isolated: `rotated-frame-universe-rich-2to1-game-has-vanishing-value`.
    Its decomposition is (A1) small-set expansion of `T_e` modulo the
    `(w, x_a+x_a')` algebra, and (A2) no consistent pair-sum-local selection.
  - Numerics: every argmax-of-potential strategy decays. Linear is best, with
    value 0.18 at `n = 1024` and a local exponent of about `-0.22`.
  - Target question: `rich-2to1-perfect-completeness-has-robust-basic-sdp-gaps`,
    via route `robust-basic-sdp-gaps-from-rotated-frame-universe`. If that
    claim is false, basic SDP with a threshold depending on `n` refutes
    Conjecture 7.
