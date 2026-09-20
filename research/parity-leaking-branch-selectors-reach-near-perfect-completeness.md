---
rg: 2
id: parity-leaking-branch-selectors-reach-near-perfect-completeness
kind: claim
title: Some polynomial-time branch selector with global, parity-leaking views orients the Grassmann 2-to-1 instances of a gap-3LIN source so that YES orientation lifts have value at least 1 - eta' while NO lifts keep value at most delta
distinct_from:
  view-local-branch-selectors-are-gauge-blind: that kills selectors whose views are parity-faithful; this is the surviving global case, and the kill supplies its necessary condition (parity leakage on a 1 - 2 eta' - o(1) fraction of edges).
  unique-games-hard-at-completeness-one-half: that reaches completeness 1/2 obliviously by splitting; this asks for a computed, instance-dependent orientation above 1/2.
  orientation-lift-selectors-need-vanishing-host-gap: that is a necessary condition on every selector route (YES host gap below X(delta) eta'); this is the existence claim it constrains.
---

**OPEN.** This is heretic denial H1.

**Assumption denied (A1).** The HOT families (local-designs, probability-random)
assume hardness is generated edge-locally. Each constraint's accept set is fixed
by a local gadget, such as a long-code or noise test, a local wrapper or a pairing
design, and completeness is oblivious. Every recorded kill of that class
(`unique-constraints-orient-at-most-half-of-a-fiber`,
`grassmann-composed-2to2-coarsenings-are-satisfiable`,
`linear-view-unique-verifiers-collapse-to-quotient-coarsening`) stops at the
one-half wall. The denial is that the branch choice is computed from the whole
instance.

**Claim.** There are a polynomial-time reduction from a gap-3LIN problem to
Grassmann 2-to-1 instances `D(I)` (the DKKMS shape) and a polynomial-time selector
`S` with the following two properties:
- on YES inputs, `val(U_(S(I))) >= 1 - eta'(eta)` with `eta' -> 0`;
- on NO inputs, `val(D(I)) <= delta`.

Every lifted constraint implies the source constraint, so `val(U_o) <= val(G)`
and the NO bound transfers to the lift. This claim therefore implies UGC, through
`ugc-via-parity-leaking-branch-selector`. Worker e-ugc-2to1-reframe also reports
that the right merge of the lift is fully rich, which would give the Rich 2-to-1
form directly. The weaker version with any
constant `c > 1/2` in place of `1 - eta'` would already beat the one-half wall of
`unique-games-hard-at-completeness-one-half`.

**Established necessary condition.** By `view-local-branch-selectors-are-gauge-blind`,
any `S` whose certificate is an honest labelling from an equivariant menu of size
`exp(o(n/s^2))` must have parity leakage `w_bad >= 1 - 2 eta' - o(1)`. On almost every
edge its view must span a parity of window variables outside `H_U`, so it must see
a cycle of equations through the window.

**Falsifiers.**
- (i) Show that a selector as claimed, together with its honest certificate,
  yields a polynomial-time algorithm that beats `1/2 + eps` on the gap-3LIN
  source. That would refute the claim under P != NP.
- (ii) Show that for every selector the lift value is at most
  `1/2 + w_bad/2 + o(1)` on most gauges, for all labellings and not only honest
  ones. Then completeness `1 - eta'` forces `w_bad -> 1`. Combined with (i),
  that closes the case.

## Attempts

* **Bounded parity-faithful views (2026-09-18).** **Dead.** Killed by
  `view-local-branch-selectors-are-gauge-blind`: under the gauge `z`, the branch
  bit is exactly uniform given the view, so honest completeness is at most
  `1/2 + w_bad/2` over subexponential equivariant menus. Only global views,
  unclustered menus or non-honest certificates survive.
* **Near-perfect selectors on DKKMS-form instances in the covering regime
  (2026-09-18).** **Dead under NP not in RP.** Killed by
  `near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp`. When `D(I)` is
  the DKKMS construction, after any polynomial-time 3LIN map, at `(l,k)` with
  `SD* <= 10^(-5)` and Corollary-A admissibility, a selector with any views,
  global or parity-leaking, with or without a certificate, and YES lift value
  `>= 1 - 10^(-5)` puts the source in RP. Falsifier (i) is realised at
  completeness `1 - 10^(-5)` for every selector, not only honest ones. For
  advice dimension `q >= 2` the regime is every admissible point with `l >= 43`.
  Survivors: completeness in `(1/2, 1 - 10^(-5))`; `q = 1` with
  `k_A(l) <= k < k_0(l)`; non-DKKMS `D(I)` (another inner test or outer game).
  The claim stays OPEN for those.
* **Spectral-gap gate on the host (2026-09-18).** **Conditional kill, OPEN.**
  - *What is proved.* Gate (G) of
    `akkstv-rounding-holds-on-all-loop-free-constraint-graphs` is
    ESTABLISHED. On any YES host family with `λ_2 >= X(δ) η'`, a polynomial-time
    selector with lift value `1 − η'` puts the source in P. This holds whatever
    the views or certificates are.
  - *Where the gate lands on DKKMS.* The unfolded DKKMS host has gap `Θ(β)`,
    and `β −> 0`. But the folded host measured in
    `folded-dkkms-hosts-keep-spectral-gap-as-smoothing-vanishes` keeps a gap
    near `1 − sqrt(1 − 4^(−l))` even at `β = 0`, because folding resamples the
    free blocks.
  - *What this gives.* If that OPEN claim holds, this node is false on the
    DKKMS shape under P != NP alone: `η' >= c(l)/X(δ)` with `l = l(δ)`.
  - *Where H1 can still live.* Only on reductions whose folded YES host gap
    tends to 0, or through a failure of (P1)–(P5) there.
* **Spectral host-gap gate (2026-09-18).** **Dead on hosts with gap bounded
  below; the claim stays OPEN.** By `orientation-lift-selectors-need-vanishing-host-gap`
  (through `degree-blow-up-extends-spectral-gap-gate-to-irregular-hosts`), the
  claim implies P = NP unless some YES host has
  `lambda_2 < X(delta) eta' -> 0`. The rule is independent of the view and of the
  witness. The Grassmann containment layer has constant gap, so the vanishing gap
  must come from the outer `U -> V -> U'` smoothing walk or from the 3LIN source.
  This answers need `6166cb1b` with YES.
* **Spectral gate on DKKMS hosts with `l` free (2026-09-18).** **Dead as a
  kill; the claim stays OPEN.** By `folded-dkkms-host-gap-vanishes-as-l-grows`
  (Theorem F), the folded DKKMS host has `lambda_2 <= 2(beta + 6 * 2^(-l))` for
  `l >= 6`. DKKMS soundness (Hypothesis 3.6, Lemmas 3.17, 3.20 and 5.3) needs
  only `l >= l_0(delta)`, so `l` may grow with `eta'`. The conditional kill
  "`eta' >= c(l)/X(delta)` with `l = l(delta)`" in the bullet above therefore
  does not follow. Gate (G) is vacuous on DKKMS once
  `l >= log2(24/(X(delta) eta'))`, at every completeness, including the
  constant-bias cell `(1/2, 1 - 10^(-5))`. On DKKMS this node stays killed
  only by the rigidity route (`near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp`).
  Spectral methods cannot touch the constant-bias cell.
* **Non-DKKMS instances via an instance-free Theorem S (2026-09-18).**
  **Dead under NP not in RP on every rigid doubled LEC; the claim stays OPEN.**
  By `near-perfect-selectors-die-on-every-rigid-doubled-lec` (Theorem S\*), the
  DKKMS kill holds for any reduction `x -> D(x)` into a composed 2-to-1 game.
  The reduction needs four things: a linear read-out `(a_e, x_e, ev_e)` into an
  outer game with `F_2^m` labels and `1/16`-uniform directions; comparable
  marginals; 99% local rigidity (Rig) on YES instances; and NO outer value
  below `p0^2 c1 / 2`. The views, certificate and parity leakage play no part.
  The new ingredient is a bit-free branch identity, so the witness may carry the
  selector's own bits.
  - *The survivor splits.* "Non-DKKMS `D(I)`" becomes four failable
    prerequisites. A realisation of this claim near completeness `1` needs
    (F1) no linear read-out, (F2) marginal blow-up, (F3) outer soundness not
    below `Theta(4^(-l))`, or (F4) YES labellings of value `-> 1` that are far
    from every locally honest labelling.
  - *No second family on record.* By
    `kms-2to2-reduction-is-sound-only-for-colorings`, the KMS TR16-124
    instances are sound only against `(j, delta)`-colorings. Their authors
    attribute value soundness to a constraint-removing modification, which is
    the DKK(M)S line. No value-sound reduction meeting (F1) to (F4) is on record.
  - *Still alive.* The constant-bias cell, 2-to-2 inner games, and new
    constructions. (F4) is the sharpest target. It would be killed by showing
    that 1%-soundness of a Grassmann 2-to-1 test forces 99% local rigidity.
* **2-to-2 inner games presented as dense-link squares (2026-09-18).**
  **Dead under NP not in RP** on every square of a rigid doubled LEC. Killed by
  `dense-link-square-selectors-reduce-to-base-orientations`. Take the 2-to-2
  game `Sq_J(G)`, whose constraint is `pi_(e1)(sigma1) = pi_(e2)(sigma2)` for
  pairs drawn from an alpha-dense link coupling `J_q` at each right vertex. A
  deterministic pivot turns any matching selection of value `1 - xi` into an
  orientation of `G` with lift value `1 - 13 xi / alpha^3` (Theorem Q). Theorem
  S\* then applies to that orientation. The converse costs a factor 2 (Q'). The
  DKKMS derived 2-to-2 game (two members sharing a B-vertex agree on `L'`) is
  the product square, with `alpha = 1`. So 2-to-2 selectors on it with YES value
  at least `1 - 10^(-5)/13` die at every certified point.
  - *Invariant.* A dense-link square presentation whose base satisfies (E),
    (M=), (Rig) and (S). The members die at the pivot step. Every 2-to-2 game is
    an `alpha = 1` square of its edge subdivision, but that base has stars of
    size 2 and fails (E). So the kill does not reach general 2-to-2 games.
  - *Still alive in the 2-to-2 cell.* (T1) sparse or non-uniformly removed
    links, `alpha -> 0` (the KMS Remark 1.11 constraint removal, if it is not
    uniform on links); (T2) families whose only square presentations are thin
    and fail (E); (T3) dense-link bases failing (F1) to (F4). The constant-bias
    cell is untouched.
* **Constant-bias cell via 50% seed structure (2026-09-18).** **Dead under
  NP not in RP for A-side-non-honest witnesses; the claim stays OPEN.** See
  `constant-bias-selectors-need-seed-dishonest-witnesses` (Theorem C, Lemma F).
  - *What is proved.* On any doubled LEC with `gamma'/4`-uniform directions,
    (M), fibre separation `kappa` and outer soundness below
    `Theta(gamma'^6 4^(-l)/K^2)`, consider any selector with YES lift value
    `1/2 + gamma`, at any value in `(1/2, 1)`. It puts the source in RP unless
    some YES labelling of value `>= 1/2 + gamma` has seed-dishonest satisfied
    mass `> gamma - gamma' - r - kappa` against every defect-`r` honest
    reference of every good outer labelling.
  - *Why the old approach missed the cell.* The reading of the selector's own
    bits at the witness's seeds pays only for satisfied ev-dishonest mass, not
    for violated mass. So 99% rigidity is not needed.
  - *What is killed.* A-side non-honesty is worth at most
    `kappa = 1/(2^l - 1)` on Grassmann tests. So zoom-type, mixed and garbage
    A-labellings over honest seeds are dead.
  - *Survivors.* The cell `(1/2, 1 - 10^(-5))` now needs one of four failures:
    - (C1) no read-out;
    - (C2) marginal blow-up;
    - (C3) loose outer soundness;
    - (C4) YES labellings of value `> 1/2` whose satisfied seeds disagree, on
      constant mass, with every honest encoding of every good assignment.

    (C4) is a selector-free statement about B-labels alone. Also still alive:
    2-to-2 inner games.
* **Closing the constant-bias escape by single-reference seed rigidity
  (2026-09-17).** **Dead** as a universal statement. Killed by
  `dkkms-seed-rigidity-fails-on-homogeneous-kernel-mixtures`, which refutes
  (Seed) (need 16613d6f).

  On inputs with a homogeneous kernel `(φ, z)` of rank `l+1` generic on
  tuples, take the mixture that uses `x` where `φ|_(L′)` is injective and
  `y = x + z` elsewhere. It has DKKMS value `0.711`, and its satisfied seed
  labels are dishonest on mass `0.289 > gamma` against every reference.

  The branch is a function of `L′`, not of `V`. The transfer to hard padded
  families is conditional on DKKMS Lemma 5.4 at the padded soundness.

  Still alive: (List-Seed) with `O_gamma(1)` references (need a06a9ee8), or
  (Seed) restricted to inputs with no generic rank-`(l+1)` homogeneous kernel.
* **(List-Seed) with an l-free list, need `a06a9ee8` (2026-09-18,
  swarm-0917-w13-w13-ugc-last1).** **Refuted** in
  `dkkms-list-seed-needs-lists-exponential-in-l` (Theorem LS). On J-instances
  with a homogeneous kernel `Φ = (φ, ζ)` of rank `2l`, the labelling that
  switches to `x + <d, ζ>` on the defect line `c(S) = Φ(S) ∩ (0 x F_2^l) = <(0,d)>`
  has value `>= 0.609`. Its satisfied mass on the defect branches is `>= 0.28`.
  Every per-tuple reference covers at most `9 · 2^(-l)` of it, so every list of
  fewer than `2^(l-6)` references leaves more than `gamma/2` uncovered, for
  all `gamma <= 0.109`. The corrected prerequisites of the constant-bias kill,
  each of which can fail, are:
  - (List-Seed_l) with list size `2^(Theta(l))`, which is not refuted, since
    `2^l` references cover this family;
  - a list-decoding rerun of Theorem C that loses a factor `2^(-Theta(l))`,
    which DKKMS outer soundness `exp(-k/exp(ql))` can afford at large `k`, but
    which is unproved.

  Any rerun that needs one reference of honest mass above `1/2` also fails
  here: the heaviest reference has mass `0.289`.
* **List-decoding rerun of Theorem C, part (b) of need `4a85435f`
  (2026-09-19, swarm-0917-w14-w14-ugc-pull).** **Established; the claim stays
  OPEN.** See `list-reference-constant-bias-decoding-loses-t-squared`
  (Lemma F_t, Theorem C_t).
  - *What is proved.* With a per-seed list of `t` good outer labellings, where
    the index may depend on the seed only, the unchanged seed-guessing decoder
    puts the source in RP at a cost of `t^(-2)` in the outer value. That cost
    enters only through the soundness bound (S_t): `s < c_t0/2` with
    `c_t0 = p^2/(t^2 K^2) - 2 eps`. So `t = 2^(O(l))` is affordable, and part
    (b) is settled.
  - *Seed form.* Lemma F_t gives `D <= beta + t r + kappa_t`. On Grassmann
    tests the collision term is `kappa_t = min(t, 2^l - 1)/(2^l - 1)`, and this
    is exactly sharp: `t` partner references `sigma + psi_j` make `sigma`
    satisfied and ev-dishonest on the `t` hyperplanes `ker psi_j`. So
    (List-Seed_t) implies the kill only for `t < (gamma - gamma')(2^l - 1)`,
    with reference defect below `gamma/t`. For `t >= 2^l - 1` it is vacuous.
  - *Corrected prerequisite (a).* Either (List-Str_t) in ev-form with
    `t = 2^(O(l))`, where A-label honesty is measured against the reference
    chosen at the seed, or (List-Seed_t) with `2^(l-6) <= t < gamma 2^l`.
    The lower end comes from Theorem LS. The full cover of Theorem LS's
    family uses `2^l` references, which is the vacuous end of the seed form.
    Its partial covers need `t ~ 0.026 * 2^l`, which lies inside the window.
* **Ev-form (List-Str_t) plus a list-guessing decoder, need `fb418c25`
  (2026-09-19, swarm-0917-w15-w15-ugc-pull).** **Refuted for every `t`** in
  `dkkms-ev-list-structure-needs-lists-exponential-in-k`. Take the LS
  defect-line labelling on a J-instance with kernel rank `k - 8`. On a
  satisfied defect edge the direction is uniform off the proper subspace
  `phi^(-1)(phi(L'))`, so a reference other than the branch assignment
  agrees with the A-label with probability `<= 1/2` (Lemma A). As a result,
  every t-list with `t < 2^(k-l-11)`, even with an index depending on
  `(U,V,L')`, leaves ev-dishonest satisfied mass `> 0.110` at value `>= 0.605`.
  Every instance has outer value `>= 2^(-k)`, so (S_t) of Theorem C_t (held
  wave-14 node) forces `t < gamma'^3 2^(k/2-l-5/2)`. Any loss `t^(-alpha)`
  with `alpha >= 1` forces `t < 2^(k-2l-5)`. **Where it dies:** the
  list-guessing step, against the `2^(-k)` floor. **Still alive:** sources
  with no near-full-rank kernel (conditional padding transfer), decoders that
  do not lose `1/t`, and `gamma > 0.11`.
* **Value-free star references (2026-09-19, swarm-0917-w15-w15-ugc-last1).**
  **Decomposition established; the counterexample it aimed at is refuted.**
  - *Planned counterexample (refuted).* The aim was a constant-bias witness
    explained only by honest encodings of low-value assignments: domain walls
    on cycle-3LIN padding, and near-kernel encodings. The hope was that these
    escape every list of GOOD references in Theorem CL. They do not. At the
    certified `beta = log log k / k`, the canonical local-fix labelling of `y`
    has value `(1 - beta delta/3)^k = 1 - O(log log k / k)` whenever
    `eps_out(y) = O(1)`, and its star mass is `<= eps_out(y) + z`. So Theorem
    CL already kills these witnesses at large `k` (Check C of
    `experiments/ugc-value-free-star-2026-09-17/check_value_free_star.py`).
  - *What was proved instead.* `value-free-star-list-references-put-np-in-rp`
    (Theorem CLV) deletes the value condition on the references. It charges a
    reference for satisfied edges that break the outer constraint
    `(a_e, b(w_e))`, and gets the outer value from the good stars by
    Cauchy-Schwarz through the seed-to-B marginal `K1`. The price is `1/L^4`,
    with no `eps` term. On DKKMS, `K1 <= 1/(1 - 2^(l-k))` and lists up to
    `exp(k/(4 exp(ql)))` are affordable. The corrected prerequisite of the
    constant-bias cell is now (Star-List^C): lists of ARBITRARY outer
    labellings with small consistency-charged star mass. It is implied by the
    Star-List prerequisite of Theorem CL. So any counterexample must beat
    every outer labelling, good or bad, on average over stars.
  - *Status of (Star-List^C).* It is likely false for `gamma <= 0.11`. The
    parallel lane w15-ugc-pull (node
    `dkkms-ev-list-structure-needs-lists-exponential-in-k`, not on this
    branch) proves a Lemma A that does not use the value of the reference:
    on defect edges, every non-branch linear form predicts at most half. That
    lane gets `t >= 2^(k-l-11)` at value `0.605` and `D > 0.110`, which is far
    above the CLV budget `exp(k/(4 exp(ql)))`. This transfer is unchecked
    here. Together the two results locate the obstruction: it is branch
    multiplicity per A-vertex, not the value of the references.
  - *Exploratory, unproved.* At a GStar pass star, suppose the B-labels are
    honest (`f_W = alpha|W`). Then a dishonest `L` passes only on the single
    hyperplane `ker(phi_L - alpha|L)`, so the dishonest pass mass is
    `<= 1/(2^l - 1)`. What is missing is B-side honesty. The B-side satisfies a
    Grassmann agreement test at acceptance `>= (1/2 + gamma)^2`, and an
    iterated KMS zoom decoding might supply Star-List^C. The obstacle is the
    per-star split ambiguity.
* **(Star-List^C) is circular; splice plus flip orientation (2026-09-19,
  swarm-0917-w15-w15-ugc-follow).** **Class killed** in
  `star-list-structure-is-circular-on-decodable-yes-inputs`. On J-instances
  of rank `n = k - O(log(1/gamma'))`, the solution `x = 0` is found by
  Gaussian elimination. From it one builds the flip orientation `o*`. At the
  branch label, the preferred preimage is the defect-line branch off `W_U`; on
  flat stars it is flipped on the degenerate half `L <= W_U`; everywhere else
  it is balanced. `o*` has lift value `>= 0.605` (Theorem O item 1).
  **Theorem O item 2:** every lift labelling `W'` of `o*` has
  `val <= 1/2 + D^C_L(proj W', Lambda) + E` for every list of `L` ARBITRARY
  references. The argument has three parts:
  - two-sided Lemma A off `W_U^⊥`, where each reference covers one branch of
    mass `< 2^(-s-1)`;
  - the single bit `b_q` against the two halves of a flat star;
  - `1/(2^l - 1) + SD*` for A-labels whose kernel is exactly the seed, by
    Q-uniformity.

  Splicing `o*` into any constant-bias selector `S` (Proposition S) gives a
  constant-bias selector `S'` that violates (Star-List^C) for every
  `L <= gamma'^2 2^(k-l-16)`. This range contains the whole Corollary DK^C
  budget. So, for `2^(2-l) <= gamma' < gamma <= 0.105`, "(Star-List^C) for
  every selector" is equivalent to "no selector exists", and it implies
  `P != NP` (Corollary PNP). This also settles the transfer that the CLV bullet
  left unchecked (Corollary TR). It survives noisy YES inputs of value `< 1`
  (Corollary N).
  **Where it dies:** the step "every constant-bias selector's witness admits a
  short star list". The same kill applies to the exploratory GStar/KMS-zoom
  plan above, and to any other route that would prove (Star-List^C) for all
  selectors on all YES inputs.
  **Still alive:** structure hypotheses restricted to YES inputs that the
  decoder can test are non-decodable (for example PCP images with spanning
  equation vectors), `gamma > 0.105`, `gamma' < 2^(2-l)`, and hypotheses that
  use the selector's behaviour across inputs.
* **Every per-input witness hypothesis collapses to its selector-free form
  (2026-09-19, swarm-0917-w16-w16-ugc-pull, finite-models).** **Class killed
  and decomposed** in
  `selector-witness-hypotheses-collapse-to-selector-free-form` (ESTABLISHED).
  The results:
  - **Theorem X.** For ANY predicate `Hyp(x, o)` and ANY class `P` of YES
    inputs, "every constant-bias selector satisfies `Hyp` with probability
    `>= theta` on `P`" is equivalent to "every good orientation on `P`
    satisfies `Hyp`", or else to "no selector exists". The proof hardcodes a
    single violator `(x_0, o_0)` into any selector.
  - **Theorem A.** If `Hyp` is an NP relation (as Star-List^C is, Lemma NP),
    the almost-every form implies the almost-every selector-free form or
    `P != NP`. The patch is found by Sigma_2 self-reduction under P = NP.
  - **Answer to need 8842dd02.** Testability or decodability of `P` is
    irrelevant. What matters is only whether violators exist in `P`. One
    J-instance in `P` kills the exact form, with no Gaussian elimination.
  - **Decomposition.** The CLV kill of the constant-bias cell now rests on
    exactly one selector-free prerequisite,
    `good-dkkms-orientations-admit-short-star-lists-on-hard-inputs` (OPEN).
    It asks for star-list decoding of every good orientation on an NP-hard
    low-kernel-rank sub-promise (P2), together with the NP-hardness of that
    sub-promise (P1).

  **Where it dies:** the per-selector hypothesis, applied to the patched
  selector.
  **Still alive:** cross-input and global hypotheses, average-case
  hypotheses (only in their exact form), and decoders that query `S` on
  other inputs.
* **Alphabet price from CMM low-value rounding (2026-09-20,
  swarm-0917-w23-w23-ugc-pull, transplanter).** **A kill on alphabet-efficient
  reductions only; the claim stays OPEN.** See
  `selector-bias-is-capped-by-the-cmm-alphabet-soundness-exponent`
  (ESTABLISHED). It uses `cmm-unique-games-low-value-rounding`, a new import of
  CMM Theorem 3.1.
  - **Theorem K.** It is instance-free and witness-free. Take any 2-to-1
    reduction with left alphabet `K` and soundness `delta`, and any selector
    with YES lift value `c`. If `delta < K^(-(1-c)/(1+c) - o(1))`, then the
    source is in RP. The proof runs CMM on the lift, pulls the labelling back
    through the sandwich, and accepts iff its value is above `delta`.
  - **The price.** Bias `c` needs `K >= delta^(-(1+c)/(1-c) + o(1))`.
  - **The trivial orientation.** It sits at exponent `1/3`, which is CMM's
    d-to-1 bound at `d = 2`. So on a 2-to-1 family with `s >= 1/3`, no bias
    above `1/2` survives.
  **Where it dies:** the YES lift is CMM-roundable above `delta` whenever
  `log(1/delta)/log K > (1-c)/(1+c)`.
  **Still alive:** DKKMS, and every family where `l` can grow at fixed `delta`.
  There `s -> 0` and the price is vacuous at every bias, which is the same
  escape as for the spectral gate. The constant-bias cell must therefore live
  on alphabet-inefficient instances, with `s <= (1-c)/(1+c)`.
