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
