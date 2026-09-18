---
rg: 2
id: efficient-branch-selector-on-proved-2to1-instances
kind: claim
title: The proved imperfect-completeness 2-to-1 Grassmann instances admit a polynomial-time orientation whose YES lifts have value near 1
distinct_from:
  unique-games-conjecture: that asks for some reduction to near-1 versus near-0 unique games; this fixes the vertex set, constraint graph and soundness proof to those of the proved Khot--Minzer--Safra 2-to-1 instances and asks only for a per-edge branch bit, so it can fail while UGC holds.
  rich-2to1-games-conjecture: that demands a rich pairing law; this mentions no pairing law at all, since by orientation-lifts-sandwich-2to1-game-values richness and soundness are supplied for free once a selector exists.
  smooth-design-rich-2to1-hardness: that asks an outer PCP to realize t-wise uniform smooth pairing laws; this keeps the F_lin pairings of the proved instances and moves all open content into the completeness of a right bit.
  finite-moment-pairing-2to1-hardness: that bounds an average overlap count of sampled matchings; this is a completeness statement about branch statistics of YES labellings, and it implies that claim through the smooth-design route.
  unique-constraints-orient-at-most-half-of-a-fiber: that caps local unique gadgets at completeness one half; this asks for a globally computed orientation on a doubled right alphabet, where item (1) of the sandwich proves the random-bit floor one half and nothing caps it.
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that kills affine-view verifiers with oblivious completeness; an orientation lift has no honest right label that is a view of one outer label, since its right bit depends on the edge, so it lies outside that theorem's hypotheses.
  grassmann-composed-2to2-coarsenings-are-satisfiable: that evaluates the branch-blind coarsening on these instances; a selector must read exactly the branch information that coarsening discards.
  grassmann-restriction-test-is-99-percent-rigid: that is a structure theorem for the plain Grassmann restriction test and mentions no reduction, no orientation and no complexity assumption; this asks for a polynomial-time orientation of one fixed instance family, and that structure theorem bears on it only through a transfer to the smoothed DKKMS game which its six-flag proof does not survive.
  dkkms-smoothing-leaves-the-branch-coordinate-untested: that is a weight computation on the DKKMS edge law, showing which hyperplanes of an A-space carry seed mass and obstructing one named proof strategy for the rigidity node; this is the completeness question for an orientation, and the weight computation only says where its remaining freedom lives.
artifacts:
  - experiments/orientation-lift-2026-09-17/check_orientation_lift.py
  - experiments/grassmann-99-rigidity-2026-09-18/seed_spread_dkkms.py
---

**OPEN.**

*Instances.* For `eta > 0` let `R_eta` be the polynomial-time reduction behind the
2-to-1 form of `two-to-two-games-theorem` (source footnote 2). It maps a 3LIN
instance to a bipartite 2-to-1 game `G = R_eta(x)` with `Gap-2-to-1[1-eta, eta]`.
Concretely these are the folded Dinur--Khot--Kindler--Minzer--Safra Grassmann
games described in `grassmann-composed-2to2-coarsenings-are-satisfiable`. An
A-class `(U, L)` with `dim L = l` joins a B-vertex `(V, L')` with `L' < L` of
codimension 1, and the constraint is restriction of the unfolded functional.

*Statement.* There is a function `eta'(eta) -> 0` as `eta -> 0` such that for every
`eta > 0` there is a polynomial-time orientation `o` of the edges of `R_eta(x)`
(item 5 of `orientation-lifts-sandwich-2to1-game-values`) with

```text
val( U_o(R_eta(x)) ) >= 1 - eta'(eta)      for every YES input x.
```

By item (5) of the sandwich, every orientation has the form
`o_e(s) = u_e(s)(x_e) xor g_e(u_e(s)|_(L'))`. Here `x_e in L \ L'` is fixed,
`u_e` is unfolding and `g_e` is arbitrary. So the statement asks this: on YES
instances, some near-satisfying labelling has, at the typical B-vertex, its
values on the **new directions** `x_e` of the neighbouring `l`-spaces predictable
up to one bit per B-vertex, by a polynomial-time rule `g_e` of what the B-vertex
sees.

**Why this is a genuine prerequisite.**

* **Sufficient.** Route `rich-2to1-via-branch-selector-on-proved-2to1-instances`
  derives `rich-2to1-games-conjecture` from this claim together with two
  established nodes. Route `smooth-design-rich-2to1-via-branch-selector` derives
  `smooth-design-rich-2to1-hardness`, and through the existing
  `finite-moment-hardness-from-smooth-design` it derives
  `finite-moment-pairing-2to1-hardness`.
* **Can fail on its own.** It concerns one fixed instance family. UGC could hold
  through a different outer construction while every polynomial-time `g_e` on
  these instances leaves the minority-branch mass bounded below. The selector
  must use the 3LIN right-hand sides only through `g_e`. By item (3) of the
  sandwich, the lift loses exactly that minority mass.
* **Graded.** Item (1) of the sandwich gives `val(U_o) >= (1 - eta)/2` for every
  `o`. A selector with YES lift value `>= c > 1/2`, uniformly in `eta`, already
  proves `Gap-UG[c, eta]` and `Gap-Rich-2-to-1[c, 2 eta]` NP-hard (consequence
  (a)). That is past the best recorded unique games gap
  `unique-games-hard-at-completeness-one-half`. So the first falsifiable
  milestone is any constant bias above `1/2`.

**Not already killed.**

* `linear-view-unique-verifiers-collapse-to-quotient-coarsening` and
  `grassmann-composed-2to2-coarsenings-are-satisfiable` kill affine-view
  verifiers with oblivious completeness. Its right bit changes with the edge, so
  it is not a view of the B-label or of any single A-label, and the collapse
  hypotheses fail.
* `left-preserving-local-richness-wrappers-are-affine-ug-merges` covers
  wrappers that add rich right vertices under affine local certificates. Here
  the richness comes from `Psi` after the lift, and the certificate question is
  replaced by the branch statistic.
* `perfect-completeness-rich-2to1-tractable-skeletons-are-in-p` is silent, since
  completeness is `1 - eta'`.
* Caution. On the honest YES labelling from DKKMS completeness, the branch at
  `e` is `A(x_e) xor g_e(A|_(L'))`. For `x_e` outside `L' + H_U`, `A(x_e)` is not
  determined by the B-label and the folding offsets. If `A` is drawn uniformly
  among linear maps consistent with those data, the new-direction values at
  neighbours with independent `x_e` are independent uniform bits. So their
  branch bias is `0` for every `g_e`. YES instances carry one specific
  assignment, not a random one. A selector must therefore exploit the structure
  of the actual satisfying assignments, the 3LIN right-hand sides, or non-honest
  YES labellings. This is a heuristic warning, not a kill.

## Attempts

* **Random or lexicographic orientation (2026-09-17).** It gives lift value
  `>= (1-eta)/2` and fully rich hardness at completeness one half
  (`rich-2to1-hard-at-completeness-one-half`). By item (1) of the sandwich it
  cannot exceed the floor on instances whose YES branches are balanced. Not a
  solution.
* **High-advantage decoding (2026-09-18).** This attempt is recorded in
  `high-advantage-selector-witnesses-decode-good-outer-labellings`, which is
  ESTABLISHED. At lift value near 1, Markov gives a uniform list-decoding rate
  `2^(-l)/192` at all but `O(xi + zeta + d)` of the target mass. So any outer
  labelling of value `>= 15/16` with a near-honest witness decodes.
  - Corollary A: on DKKMS instances, a polynomial-time orientation whose YES
    lift witnesses are `1/64`-close to a locally honest patchwork of dirt
    `<= 1/64` gives `NP in RP`.
  - Corollary B: this claim together with
    `dkkms-grassmann-2to1-test-is-locally-99-percent-rigid` (OPEN) gives
    `NP in RP`.

  Under `NP not in RP`, this claim therefore requires the local rigidity node
  to fail. That means YES labellings of value arbitrarily close to 1 that are
  far from every patchwork. Not a solution. It is a decomposition into two
  prerequisites that cannot both hold.

* **Planted/NO-coset coupling (2026-09-18).** This attempt is recorded in
  `locally-read-witnesses-are-sound-on-planted-2to1-inputs`, which is
  ESTABLISHED. Take any witness map `Lambda` (orientation plus lift labelling,
  efficient or not) with read sets `S_e`, and any sound right-hand side `b0`.
  Then `E_t val(Lambda(Ht)) <= eta + mu_(b0)`, where `mu_(b0)` is the weight of
  the constraints whose read set `b0` locally refutes (`b0|S_e notin
  Im H_(S_e)`). A YES witness of value `>= 1 - eta'` must therefore read
  `b0`-refuting parity cycles on `>= 1 - eta' - eta` of the mass, for every
  sound `b0`. Tree-like reads are capped at `eta + w_cyc`. Need `207b4529` is
  reduced, not refuted: any class labelling realising it must encode
  cross-member parity cycles on its class read sets. Not a solution.
* **Regime closure (2026-09-17).** This attempt is recorded in
  `dkkms-certified-parameters-lie-in-the-selector-kill-regime`, which is
  ESTABLISHED. The inequalities that the DKKMS Lemma 5.3 soundness proof
  imposes on its own parameter point are:
  - smooth-advice mass `sqrt(beta sqrt k) <= alpha(l)/2`, with
    `alpha(l) = delta1 2^(-l^2-2)`;
  - outer margin `eps_k < delta alpha(l)/4`;
  - soundness `delta >= 2^(1-l)`.

  Together these force the Theorem S regime (R)+(A) at every certified point
  with soundness below `1/16`, for every advice dimension `q`. Corollary S1 of
  Theorem S therefore holds with no parameter window: this claim implies
  `NP in RP`, with `R_eta` read as the DKKMS TR16-198 family as defined above.
  The claim stays OPEN, and is conditionally refuted under `NP not in RP`.
  Two things survive:
  - lift completeness in `(1/2, 1 - 10^(-5))`;
  - other instance families, including the TR16-124 A-A Grassmann reduction if
    that is what the 2-to-2 theorem actually uses.

  Not a solution.

* **Building the selector from parities of the right-hand sides
  (2026-09-18).** **Mechanism found and checked; the kill is not yet
  established.** Recorded in
  `bounded-rank-parity-selectors-pay-representation-weight`, which was posted
  ESTABLISHED and demoted to **OPEN** the same day by referee audit: Lemma 3
  ("`W_(ef) > N`") is false for *collapsing* pairs, since its proof never
  excludes `T = empty`, and the Corollary's hypothesis ("all pairs have
  `W_(ef), g_(ef) > W`") is then met by no B-vertex at all — every constraint has
  `2^k - 1` collapsing same-window partners — so `rho = 1` and the Corollary,
  the only place the "tends to `1/2`" conclusion is delivered, reads vacuous.
  The repair looks like one clause ("`W_(ef) = 0` or `W_(ef) > N`", and `rho`
  over non-collapsing pairs only, collapse already being priced by `kappa`) and
  leaves the numeric bound unchanged, but it has not been made or re-refereed.
  Read the rest of this entry as the *shape* of the attempt, not as a settled
  kill. `view-local-branch-selectors-are-gauge-blind` leaves *parity
  leaking or global* selectors alive, so the natural next attempt is to let the
  selector read arbitrary parities `<c, b>` of the right-hand sides. The
  arithmetic is exact and encouraging at first: if `M^T c = x_e + y + h` with
  `y in L'` and `h in H_(U_e)`, then

  ```text
  o_e(tau) := <c, b> xor tau(y) xor h_(U_e)(h)
  ```

  predicts the honest branch bit `<t, x_e>` **perfectly**, except that it is off
  by the parity `<c, Viol(t)>` of the violated equations it combines. That is
  where it dies. The gauge of the blindness kill cannot randomise `Viol`, but
  the planted ensemble `b = M t + v` can, and then the bias of the prediction is
  exactly `(1 - 2 eta)^(|c|)`. Two consequences:

  - **Short representations do not exist.** On a locally sparse source, a set
    `T` of equations summing into `x_e + x_f + L' + H_(U_e) + H_(U_f)` has all
    its degree-one variables inside `vars(U_e) union vars(U_f)`, which
    unique-neighbour expansion forbids for `|T| > 6k` and local isolation
    forbids for `|T| <= 6k`; the artifact finds none with `|T| <= 3` at
    `n = 400` (at 95% of windows).
  - **So the price should be paid in full** — this is the part the audit
    stopped. The intended conclusion is that every selector whose per-edge bit
    function factors through at most `R` arbitrary parities of `b`, beyond its
    window's own offsets, has honest lift value at most
    `1/2 + k eta + (1/2) sqrt(1/D + kappa + rho + 2^(2R+1)(1-2eta)^W)`, tending
    to `1/2` on DKKMS-shape neighbourhoods (in the limit order `k`, then
    `eta ~ delta/k`, then `n`; the order stated in the node does not work). The
    bound would be on the lift value, not on the agreement rate `hon_t(o)`; the
    second moment over each B-vertex needs the *pair* invariant, the
    representation weight of `x_e + x_f`. As posted, `rho = 1` identically and
    the bound is vacuous. It is also an *average* over the planted ensemble, not
    a per-instance statement — harmless here, since one bad YES instance
    suffices, but the node's per-instance phrasing overstates it.

  Two concrete global selectors were measured on small Grassmann instances:
  Gaussian elimination on the whole system (`0.510`) and solving the window plus
  the seed label (`0.524`), against an oracle control at `1.000`.

  Survivors after this attempt: everything, pending the Lemma 3 / Corollary
  repair. If that repair goes through, the survivors would be rank above
  `eta W(n)`, which is decoding and not leaking, and is exactly the regime of
  `efficient-branch-selectors-list-decode-honest-outer-labels` under
  `NP not in RP`; and non-honest witnesses, which no kill on this node reaches
  at any rank. Note also that the bounded-rank class does **not** subsume
  `view-local-branch-selectors-are-gauge-blind`, whose faithful views may have
  rank `Theta(m)`: the two kills are incomparable, so neither closes the other's
  survivors.

* **Obstruction mining on the rigidity branch (2026-09-18, agent
  `e2-w2-ugc-selector-kill`, family stability-approximation, signature "seed
  BLR recovers one global linear label"). Refuted in part at the wave's referee
  stage; both nodes land OPEN.** Attacked the hole from the opposite sign: try
  to *prove* the rigidity node `dkkms-grassmann-2to1-test-is-locally-99-percent-rigid`
  and so refute this claim under `NP not in RP`, via Corollary B of
  `high-advantage-selector-witnesses-decode-good-outer-labellings`. **This hole
  survives** — all three referee lenses agreed, and the reason is simple: what
  the lane proved is the *plain*-test statement
  `grassmann-restriction-test-is-99-percent-rigid`, which is a different node
  from the DKKMS rigidity node Corollary B needs. That node stays OPEN, so
  Corollary B never fires. Two nodes were written; both are now OPEN with their
  proofs kept as attempt artifacts.

  1. `grassmann-restriction-test-is-99-percent-rigid` (OPEN; **no referee found
     an error**, demoted because the lane's referee stage refuted its companion).
     For the plain linear Grassmann restriction test, value `1 - eta` forces a
     single global linear functional on all but `800 eta` of the `l`-spaces,
     with an absolute constant. The proof is a six-flag gadget: from a seed
     `Q`, a hyperplane `P < Q` and two directions `x,y`, the `l`-space
     `N = P + <x,y>` shares the hyperplane `P + <u>` with `Q + <u>` for each
     `u in {x, y, x+y}`, and `sigma_N` is linear, so the seed prediction
     function `F_Q(x) = sigma_(Q+<x>)(x)` is an approximate homomorphism with
     defect `6 eta`. BLR gives one linear `A_Q` per seed, and the down-up walk
     on `Gr(X,l-1)`, whose non-trivial eigenvalues are at most `1/2` in
     modulus, glues them into one `A`. No step pays a `2^l`, so the `2^l` loss
     that the rigidity node feared from zoom structures does not occur. All
     three lenses audited it line by line and it held; the final budget is
     `784.4 eta` against the claimed `800 eta`.
  2. `dkkms-smoothing-leaves-the-branch-coordinate-untested` (OPEN;
     **refuted at Corollary 3** by lens 2, the same step named by lens 1). Its
     correct content: seeds of `G_multi` are `(V'', R)` with `R <= X_(V'')` for
     a smoothed tuple, and a fresh smoothing contains a prescribed uniform
     direction with probability exactly `(1 - 3 beta / 4)^k`, so the six-flag
     gadget — whose three auxiliary flags sit at `N != L` — transfers only with
     `eta` replaced by `eta (1 - 3 beta / 4)^(-k)`, vacuous at every admissible
     parameter point. An exact computation of the conditional seed law is
     consistent: `E_L max_R w(R|L)` at `l = 3`, where uniform spread is `1/7`,
     rises from `0.478` at `k = 2` to `0.840` at `k = 8` for `beta = 1/2`, and
     the dominant hyperplane is the generating seed for `0.90` of the A-mass
     there (`experiments/grassmann-99-rigidity-2026-09-18/seed_spread_dkkms.py`).
     Its **overclaim**, which was refuted: that *every* proof importing a 99
     percent Grassmann agreement theorem must pay that factor. Lemma 1 is about
     one constraint; two constraints at the *same* A-vertex have distinct
     hyperplane seeds `R1, R2` with `R1 + R2 = L`, so they pin the A-label at
     every direction at `O(1)` cost, and lens 2's measurement of the
     same-A-vertex quantity (`0.29 ... 0.13` for `k = 2..8`, against
     `(1 - 3 beta / 4)^k = 0.39 ... 0.023`) decays far more slowly than the
     asserted rate.

  **What this leaves for this claim.** Proposition 4 of the second node is
  *conditional* on folding-compatibility of the dominant seed germ
  `L |-> D(L)`, which is posted as an open sub-statement and is not settled. If
  it held, `G_multi` would have a labelling of value `1 - o(1)` that is
  `1 - 2^(1-l)`-far from every locally honest patchwork, and the **constant**
  orientation `g_e := 1` with right bits `0` would lift it with the same value
  — so that much of this hole would be a combinatorial question about folding
  classes with no algorithmic content. That is a conditional reading, not a
  result. It is **not** recorded that the Grassmann-import lane is dead: only
  the six-flag member of it is blocked, and whether some other Grassmann
  agreement argument transfers to `G_multi` is open. The attempt artifacts are
  `research/artifacts/grassmann-restriction-99-percent-rigidity-proof-2026-09-18.md`
  and `research/artifacts/dkkms-branch-coordinate-untested-proof-2026-09-18.md`.
