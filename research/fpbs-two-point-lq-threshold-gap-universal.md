---
rg: 2
id: fpbs-two-point-lq-threshold-gap-universal
kind: claim
title: On every nonamenable Cayley graph the two-point function stays l^q summable slightly above p_c for every q above 2
distinct_from:
  fpbs-nonamenability-bounds-critical-connectivity-operator: that asks for operator boundedness p_c < p_{2->2}, which implies this; this asks only that the single vector tau_p(o,.) lie in l^q for p slightly above p_c, for each q > 2, and it tolerates tau_p(o,.) not in l^2 for all p > p_c.
  fpbs-sphere-two-point-rate-right-continuous-universal: that asks the sphere-mass growth rate g(p) to vanish as p decreases to p_c; this controls sums of tau^q, which may converge while sphere masses grow exponentially, and the two hypotheses are incomparable a priori.
artifacts:
  - research/artifacts/fpbs/docs/lq-two-point-walk-rate-2026-09-17.md
  - research/artifacts/fpbs/docs/lq-threshold-power-monotonicity-2026-09-17.md
---

**OPEN.** Let `G` be a nonamenable Cayley graph and set
`p_q = sup{p : sum_x tau_p(o,x)^q < infinity}`.

**[Q].** `p_c < p_q` for every `q > 2`.

**What it gives.** Combined with `fpbs-lq-two-point-bounds-walk-rate`,
`lambda(p) <= rho^(2/q)` just above `p_c` for every `q > 2`. Hence
`lambda(p) -> rho`, which is (IS) (route
`fpbs-integrated-sensitivity-via-lq-two-point`).

**Known cases.**

- Every class with `p_c < p_{2->2}`, since `p_{2->2} <= p_2 <= p_q`.
- Regular trees, where `p_q = (d-1)^(-1/q) > 1/(d-1)`.

**Failure mode.** [Q] fails iff some `q_0 > 2` has
`inf{q : Z_q(p) < infinity} >= q_0` for every `p > p_c`. Section 6 of the
artifact shows that a failure of [Q] would not by itself refute (IS).

## Attempts

* **Russo-BK openness (swarm-0917-w5).** The derivative of `Z_q` is majorized
  by a mixed `(q-1,1,1)` convolution sum.
  **Where it dies:** closing it needs a triangle or operator bound. That bound
  is infinite above `p_c` (`chi_p = infinity`). This is the obstruction of
  `fpbs-bk-majorant-integrated-sensitivity-is-critical-l2`.
* **Critical import.** Take `Z_q(p_c) < infinity` from critical decay.
  **Where it dies:** arXiv:1605.05301v1, thm:pcconnectivitydecay, bounds only
  the infimum `kappa_{p_c}(n)`, not typical `tau_{p_c}(o,x)`. It would also
  still leave openness through `p_c`. See Section 7 of the artifact.
* **Operator-algebra transplant: Fourier algebra and noncommutative L^r
  (swarm-0917-w7).**
  - *Proved* (`fpbs-two-point-fourier-algebra-criterion`, established):
    - `tau_p` is in `A(Gamma)` iff the cluster form
      `f -> E sum_C |f(C)|^2` is closable in `l^2`;
    - `A`-membership gives `a_n <= rho^n` with constant one, and
      nonuniqueness if `p > p_c`;
    - `tau^fin_p` is always in `A`, `tau_(p_c)` is in `A`, and
      `dist_B(tau_p, A) <= theta(p) -> 0`.
  - *Where it dies for [Q]:* at the step from `B`-norm information at `p_c` to
    `l^q` summability above it.
    - `l^q` is neither `B`-closed nor `B`-open.
    - `A`-membership carries no summability exponent: `A(Gamma)^+` contains
      functions in no `l^q` whenever `Gamma` has an element of infinite order.
    - The collapse witness `f_p` of `fpbs-two-point-state-axioms-admit-collapse`
      satisfies `f_(p_c)` in `A` and `dist_B(f_p, A) <= theta^2 -> 0`, yet it is
      in no `l^q` for `p > p_c`.
    - Noncommutative Hausdorff–Young (`T_p` in `L^r(L Gamma)` with `r < 2`
      gives `tau` in `l^(r')`) needs the same unavailable critical input.
  - *What it gives instead:* an incomparable sibling hole [A],
    `fpbs-two-point-in-fourier-algebra-near-pc-universal`. It also implies (IS)
    and BS (route
    `fpbs-integrated-sensitivity-via-fourier-algebra-two-point`).
  - *Calibration:* on trees both holes hold, and `p_A = p_2` lies strictly
    below `p_q` and `p_u`.
* **Thinning power-coupling (swarm-0917-w8, transplanter).**
  - *Proved* (`fpbs-lq-threshold-power-monotonicity`, established):
    - `tau_(p^g) >= tau_p^g`, proved self-contained;
    - `p_(q') <= p_q^(q/q')`, `p_1 = p_c`, `p_2 <= sqrt(p_c)`, and
      `q -> p_q` is continuous;
    - `{q : p_q > p_c} = (q_0, infinity)` for one invariant `q_0 in [1, infinity]`.
      So [Q] iff `q_0 <= 2`, and `p_c < p_2` iff `q_0 < 2`. Trees have
      `q_0 = 1`, with equality throughout.
  - *Where it dies:* at the exponent `log p/log p'`. Transporting
    `Z_q(p') < infinity` down to `(p_c, p')` gives exactly
    `q_0 <= q log(1/p')/log(1/p_c)`. The input `(p')^q > p_c^2` that this
    transport needs is equivalent to `q_0 < 2`, which is the conclusion.
    Thinning is an equality on trees, so no monotone parameter coupling can
    improve the exponent. New information is needed at `p_c + 0`.
    See Section 5 of `lq-threshold-power-monotonicity-2026-09-17.md`.
* **Infinite-cluster reduction and intersection moments (swarm-0917-w9,
  reframing).**
  - *Proved* (`fpbs-lq-two-point-infinite-cluster-reduction`, established; it
    uses Hermon–Hutchcroft through `fpbs-supercritical-finite-susceptibility`):
    - `sum_x (tau^fin_p)^q <= chi^fin(p) < infinity` for every `p > p_c` and
      every `q >= 1`. So every `p_q`, `q_0` and [Q] itself depend only on
      `tau^inf`.
    - `Z^inf_k` is the expected intersection of `k` independent infinite
      clusters of `o`.
    - `Z_q(p) < infinity` at one `p` gives `gamma(p) >= log(gr)/q` (kernel
      (K)), infinite-cluster ball growth at most `(1-1/q) log gr`, and
      nonuniqueness.
  - *New hole:* [Q_fin], `fpbs-two-point-some-lq-above-pc-universal`, which is
    `q_0 < infinity`. It gives the chain
    `[Q] => [Q_fin] => (K) => p_c < p_u`, with routes
    `fpbs-some-lq-from-lq-threshold-gap` and
    `fpbs-worst-pair-kernel-via-some-lq-two-point`.
  - *Consequence for methods:*
    - The collapse families H2/H5 have Bernoulli `tau^fin` and `theta` but
      `q_0 = infinity`.
    - So no argument from finite-cluster observables, `theta` or local laws
      proves [Q] or [Q_fin].
  - *Where Russo–BK with the pivotal split dies* (Section 5 of
    `lq-infinite-cluster-reduction-2026-09-18.md`):
    - The finite-side pivotal terms are at most `C chi^fin(p) Z_q(p)`.
    - Closing by Gronwall then needs `int chi^fin dp < infinity` at `p_c+`,
      which fails on `T_d`. Replacing it by an `l^r` bound is circular.
    - The pivotal term with both sides infinite is left uncontrolled.
* **Local-limit / compactness transplant (swarm-0917-w10, logic-computability,
  obstruction).** The approach proves [Q] on a dense or generating set of
  marked groups and passes to limits, or else certifies it from ball data.
  - *Where it dies:* the gap `p_q - p_c` is not lower semicontinuous in the
    marked-group topology. Take `S_k = F_2/F_2^(k)`, which converges to
    `F_2 = T_4`. Each `S_k` is amenable, so `p_u = p_c` there. Since
    `Z_q(p) < infinity` forces `tau_p -> 0` and hence nonuniqueness, we get
    `p_c <= p_q <= p_u`, so `p_q(S_k) = p_c(S_k)`. By Easo–Hutchcroft
    (`fpbs-easo-hutchcroft-pc-locality`), `p_c(S_k) -> 1/3`. But
    `p_q(T_4) = 3^(-1/q) > 1/3`. So the gap is 0 along the sequence and
    positive at the limit, and `{p_q > p_c}` is not open.
  - This is `fpbs-pu-open-certificates-pinned-at-pc` specialised to `p_q`.
    Every ball-local certificate of `Z_q(p_c + delta) < infinity` must fail at
    `F_2`. Only a closed hypothesis can gate it, such as `rho <= r < 1`.
  - *What survives:* on `K_r = {rho <= r}`, which is compact, the set
    `U^q_(delta,C) = {Z_q(G, p_c(G)+delta) <= C}` is closed. The reasons are
    that `Z_q` is lower semicontinuous in `G` (Fatou over ball-restricted
    connection events), left-continuous in `p`, and `p_c` is continuous.
    So [Q] restricted to `K_r` is `F_sigma`.
  - Since `p_(2->2) <= p_2` (item 3 of `fpbs-lq-threshold-power-monotonicity`)
    and `p_2 <= p_q` for `q >= 2` (because `tau <= 1`), every failure of [Q]
    is also a failure of the l2 gap. Every [Q] failure in `X_(k,eta)`
    therefore lies in the derived kernel of `fpbs-l2-gap-baire-dichotomy`,
    and the Baire dichotomy there transfers verbatim with `Z_q` in place of
    `||T||`.
  - *Net:* this gives no new certificate and no counterexample. A
    compactness proof of [Q] needs a uniform `Z_q` bound on an open subset of
    every closed `Y ⊆ K_r`, which is exactly as hard as the l2 kernel
    problem.
* **Stability-approximation transplant, then a certified test case
  (swarm-0917-w11, 2026-09-18).**
  - *Transplant.* Approximate `tau_p` in the Fell topology by positive
    definite functions whose GNS representations are weakly contained in
    `lambda` (sofic / finite-quotient approximants, or the thinned family
    `tau_(p^g)`), and pass `l^q` bounds to the limit. **Where it dies:**
    weak containment in `lambda` carries no `l^q` exponent. On
    `F_2 x Z`, `phi(g,z) = 3^(-|g|/2)` is tempered, because
    `lambda_(F_2) ⊗ 1_Z` is weakly contained in `lambda_(F_2 x Z)`, since `Z`
    is amenable. Yet `phi` is constant along `Z`, so it lies in no `l^q`.
    Temperedness is Fell-closed and `l^q` bounds are not. So the transplant proves at most
    the weak-containment statement [W] (`[A] => [W] => [F]`), which is too weak
    to give an exponent. This is the operator-algebra obstruction above,
    reached from the approximation side.
  - *Pivot, a computation on the canonical case.*
    `fpbs-t4xz-certified-critical-l2-gap` (ESTABLISHED, exact certificates)
    gives `p_c <= 0.236 < 0.241 <= p_{2->2}` on `T_4 x Z = Cay(F_2 x Z, std)`,
    and `p_c < p_{2->2}` on every `T_{2k} x Z`, `k >= 2`. Hence [Q] holds there,
    with `q_0 < 2`. This is the first unimodular product case of the tree-anchor
    table (`fpbs-weighted-surface-continuity-reduces-to-uniform-floor`) that
    was not already covered.
    - Monte Carlo gives `p_c(T_4 x Z)` near `0.212`, so the tree anchor
      `0.21085` really fails there.
    - A 4-cycle-avoiding Busemann Schur test reaches `0.2412`. The mechanism is
      short-cycle avoidance plus a Busemann tilt, and it has no universal
      analogue yet.
* **Calibration transplant (swarm-0917-w12, transplanter, calibration;
  obstruction, dies on arrival).** The idea was to import the calibration
  worlds of the goal and find the step at which each [Q] tool fails there.
  - *Proved, on every transitive graph and at every root of a.e. realization
    of a unimodular random graph:* if `Z_q(p) < infinity` for one `q`, then `p`
    does not have a unique infinite cluster. Suppose `p` has a unique infinite
    cluster. Then Harris gives
    `tau_p(o,x) >= theta_p(o) theta_p(x)`, and `theta_p(x) >= p^(d(o,x)) theta_p(o)`
    gives `theta_p(o) > 0`. On a transitive graph `theta_p` is constant. On an
    infinite unimodular random graph, the
    invariantly defined set `{x : theta_p(x) >= c}` is, for small `c > 0`,
    a.s. empty or infinite. The standard mass-transport argument rules out a
    finite nonempty invariant set. So `Z_q(p) = infinity` for every `q`. Hence
    `q_0 = infinity` on every world with uniqueness throughout `(p_c, 1)`.
    This is quenched, at every root of a.e. realization.
  - *Consequence.* On the Angel--Hutchcroft graph `H~(M)`
    (`fpbs-walk-rate-holes-fail-on-unimodular-random-graphs`, which quotes
    arXiv:1710.03003v1, Proposition 4.2 and the proof of Lemma 4.3, verbatim)
    there is a unique infinite cluster for every `p > p_c`. So [Q] and [Q_fin]
    fail there, quenched and at every root. This avoids the root-averaging
    objection that referees raised against the class-kill on that node,
    because `Z_q(p)` is a per-root quantity. The following survive on each
    realization, since they use no group structure:
    - the thinning inequality `tau_(p^g) >= tau_p^g` of
      `fpbs-lq-threshold-power-monotonicity`;
    - the Russo--BK majorant;
    - `p_c <= p_q <= p_u`.

    So none of these proves [Q] without an input that `H~` lacks.
  - *Where it dies: the vacuity step.* This is not a [Q]-specific
    obstruction. By the first bullet, [Q] implies nonuniqueness on each such
    graph. So every calibration world that refutes BS also refutes [Q]
    automatically, whether it is transitive or a unimodular random graph.
    Calibration by BS counterexamples (URGs, amenable
    reservoirs) therefore carries no information that separates [Q] from BS.
    The invariant is the `theta^2` floor: every calibration world with
    `p_c = p_u` hits it at the first `p > p_c`, before any [Q] tool is used.
  - *Where a real calibration would have to live.* It needs a world with a
    nonuniqueness window `(p_c, p_u)` and `q_0 > 2`. Such a world would show
    that the route `[Q] => (IS) => BS` loses information.
    - Transitive graphs cannot supply one with current knowledge. Every
      transitive class where `p_c < p_u` is proved has `p_c < p_{2->2}`, and
      so `q_0 < 2`: trees, hyperbolic, nonunimodular, highly nonamenable.
    - "Amenable reservoir" URGs cannot supply one either. These carry the
      near-critical infinite cluster on infinite invariantly amenable pieces.
      That is what makes `q_0` large, since `tau >= theta^2` inside a piece.
      But the Lemma 4.3 gluing then forces uniqueness.
    - Trees of finite fat blobs give `q_0 = 1` heuristically. Blob size
      enters `Z_q` only linearly.

    Any candidate must get `q_0 > 1` from heterogeneity at `p_c`: `chi = infinity`
    is carried by few pairs with large `tau`, while `Z_q` is carried by many
    pairs with small `tau`. This is recorded as a spark, not proved.
* **Qualitative replica meet (swarm-0917-w13, transplanter, reframing).**
  The idea replaces the mean `Z_k = E|K^1 ∩ ... ∩ K^k|` by a.s. finiteness of
  the meet `M_k(o)`.
  - *Proved* (`fpbs-replica-meet-threshold-sandwich`, established):
    - `p_k <= p_cap^(k) <= min(p_u, p_c^(1/k))`, with `p_cap^(k)` increasing
      in `k`;
    - the bound `p_cap^(k) <= p_u` comes from an invariant-finite-set lemma
      applied to the intersection of unique infinite clusters;
    - on `T_d`, `p_cap^(k) = p_k = (d-1)^(-1/k)`, which tends to `p_u = 1`.
  - *New hole:* [cap_fin], `fpbs-replica-meet-threshold-gap-universal`. It
    is qualitative, and the chain is `[Q] => [Q_fin] => [cap_fin] => BS`
    (routes `fpbs-replica-meet-gap-from-some-lq` and
    `fpbs-bs-via-replica-meet-threshold`).
  - *Where it dies for [Q]:*
    - An a.s.-finite meet does not upgrade to a finite mean, and the mean is
      exactly `Z_k`. [Q] allows `q_0 = 2`, so it gives `p_cap^(3) > p_c` but
      not `p_cap^(2) > p_c`.
    - The a.s.-finite set contains `[0, p_c]` (BLPS), and openness at `p_c` is
      again the whole content.
    - On trees the meet is exactly the Bernoulli(`p^k`) cluster. The non-tree
      multi-path part `M_k \ K_(∧omega)` at `p_c + 0` is what any proof must
      control.
    - See Section 3 of `replica-meet-threshold-2026-09-18.md`.
