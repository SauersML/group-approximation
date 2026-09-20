---
rg: 2
id: dkkms-grassmann-2to1-test-is-locally-99-percent-rigid
kind: claim
title: Every labelling of the DKKMS multi-edge 2-to-1 game of value close to 1 agrees on almost all constraint mass with the locally honest patchwork of some outer labelling of value 15/16 and dirt 1/64
distinct_from:
  high-advantage-selector-witnesses-decode-good-outer-labellings: that proves that near-honest selector witnesses decode; this is the rigidity statement that would make every near-1 selector witness near-honest, and it concerns the plain 2-to-1 game with no orientation.
  dkkms-2to1-instances-satisfy-selector-decoding-hypotheses: that verifies the list-decoding hypotheses (E) and (M=) for honest encodings of global assignments; this asks for a structure theorem about arbitrary labellings of value near 1.
  two-to-two-games-theorem: that is the 1 percent soundness statement of Khot--Minzer--Safra, which decodes labellings of value delta to a list; this is a 99 percent statement asking for agreement on all but zeta_1 of the mass with one patchwork, with explicit constant outer value 15/16.
  efficient-branch-selector-on-proved-2to1-instances: that asks for a polynomial-time orientation with YES lift value near 1; by Corollary B of the high-advantage node, this claim together with that one gives NP in RP.
artifacts:
  - experiments/dkkms-sound-point-rigidity-2026-09-17/check_density_comparison.py
---

**OPEN.**

*Setting.* The notation is that of
`high-advantage-selector-witnesses-decode-good-outer-labellings`. `G_multi` is
the unfolded DKKMS 2-to-1 game on a regular 3LIN input: one copy per member
`(U,L)` of each folding class `C` and each B-vertex `(V,L')` with `L' < L`.
`Phi_k` is its outer k-tuple game. `hon_kappa(lambda)` is the patchwork of an
outer labelling `lambda`, read at canonical members `kappa(C)`, and
`d_kappa(lambda)` is its dirt.

*Statement.* There are absolute constants `eta_1, zeta_1 <= 1/128` and `l_0`
such that the following holds for all `l >= l_0` and all `k` admissible for
Corollary A (`2^(l-1-2k) <= 1/16`, `eps_k <= p0^2/4`). On every 3LIN input,
every labelling `(A, sigma')` of `G_multi` with value `>= 1 - eta_1` agrees,
outside constraint mass `zeta_1`, with `hon_kappa(lambda)` for some outer
labelling `lambda` with

```text
val_(Phi_k)(lambda) >= 15/16      and      d_kappa(lambda) <= 1/64.
```

**Why this is a genuine prerequisite.**

* **Consequence.** By Corollary B of the high-advantage node, this claim and
  `efficient-branch-selector-on-proved-2to1-instances` together give `NP in RP`.
  So under `NP not in RP`, at least one of the two fails. If this claim holds,
  the selector route to UGC through the proved instances is closed.
* **Can fail on its own.** The claim uses no orientation and no complexity
  assumption, so it is a combinatorial statement about one test. It fails if
  some near-1 labelling is `zeta_1`-far from every patchwork of every good outer
  labelling. The selector hole says nothing about that.
* **Weaker than global rigidity, on purpose.** Agreement with `hon(a)` for one
  global assignment `a` is false at rate `Omega(beta)`, where `beta` is the
  fraction of k-tuples that can be relabelled consistently. Dictator patchworks,
  which use different satisfying assignments on different k-tuples, are
  heuristic evidence for this. They are locally honest, so they satisfy this
  claim by construction.

**Evidence for.**

* Each k-tuple `U` is tested only through moves `U -> V -> U'` and through
  `L' = L meet X_V`. So near-1 value forces per-`U` consistency on most of the
  Grassmannian of `U`. That is the regime of the known 99 percent agreement
  theorems for Grassmann tests.
* Folding makes the unfolded label `lambda_U` satisfy the equations of `U`
  automatically. So an outer labelling read off per `U` is honest for `Phi_k` on
  most tuples.

**Evidence against, or difficulty.**

* Folding classes span several `U`. A class label is read at one
  representative, so the patchwork can pay dirt wherever the members disagree.
  The claim needs this dirt to be `<= 1/64` for some choice of `kappa` and
  `lambda`.
* Zoom-in and zoom-out sets of the Grassmann test have measure about `2^(-l)`.
  Near-1 structure theorems that go through them may lose factors of `2^l` in
  `zeta_1`. The claim needs `zeta_1` to be absolute.
* Nothing recorded yet proves any 99 percent statement for the folded 2-to-1
  test at constant `eta_1` uniformly in `l`.

## Attempts

* **Global rigidity (2026-09-18).** The first formulation asked for agreement
  with `hon(a)` for one global assignment. Dictator patchworks suggest that it
  fails at rate `beta`. It was replaced by the local statement above, which
  Theorem 3 of the high-advantage node can use because it decodes any outer
  labelling of value `>= 15/16`, with no global gluing. Not a proof of either
  form.
* **Split at the covering window (2026-09-19).**
  `dkkms-seed-law-is-uniform-in-regime-and-far-in-window` splits this claim
  into two parts.
  - `T1` is the admissible points with `SD* <= 10^(-5)`. It is proved there by
    Corollary N of `dkkms-near-perfect-labellings-are-outer-honest`, and it
    contains every DKKMS-certified point with `l >= 5`, by Theorem C of
    `dkkms-certified-parameters-lie-in-the-selector-kill-regime`.
  - `T2` is the remaining admissible points. It contains no certified point,
    and this claim is equivalent to `T2`.

  At `q = 1`, the window `[k_A(l), 4^(l-1)/12]` lies in `T2` and is non-empty
  for every `l >= 20`. On it the DKKMS seed law is at total variation
  `>= 3/4 - 1/ln k` from every transitive law, so step (2) of the outer-honest
  route loses more than `1/2`. So no covering or coupling transfer from a
  uniform Grassmann test proves `T2`. Whether `T2` is true stays OPEN.
  Suggestion: narrow the quantifier to certified points, which is all the DKKMS
  soundness chain uses, and post `T2` separately if anything needs it.
* **Density comparison (2026-09-19, swarm-0917-w17-w17-ugc-follow).** This
  attempt tried to move `T1` into `T2` by comparing the DKKMS per-tuple
  B-subspace law `P0` with the uniform law `U` on `Gr(F_2^(3k), l-1)`, using the
  density `rho = dP0/dU` instead of total variation. The approach is DEAD. What
  was checked:
  - **Pointwise sandwich.** `phi <= rho <= K0 phi`, where
    `phi(Q) = prod_i ((1-beta) + (beta/3) 4^(l-1) N_i(Q))`,
    `N_i(Q) = #{v : pi_i(Q) <= <e_v>}` takes values in `{0,1,3}`, and
    `K0 = prod_j (1 - 2^-(n-2m-j))^-1`. The bounds come from the
    Gaussian-binomial ratio `[3k, l-1] / [3k-2m, l-1]`, which lies in
    `[4^(m(l-1)), K0 4^(m(l-1))]`.
  - **Law of `N_i`.** `P(N=3) = 8^(1-l)` and `P(N=1) = 3(2^(l-1)-1) 8^(1-l)`.
    So `E N = 3 * 4^(1-l)`, `E N^2 = 3 * 4^(1-l) + 6 * 8^(1-l)`, and each factor
    of `phi` has mean exactly `1`.
  - **Second moment.** For iid blocks,
    `E phi^2 = (1 + beta^2 (4^(l-1)(1+2^(2-l))/3 - 1))^k`, which is about
    `e^S`. The invariant is `S = k beta^2 4^(l-1)/3 = SD1^2/768`, where
    `SD1 = beta sqrt(k) 2^(l+3)`. `E rho^2 >= E phi^2` holds exactly on every
    enumerated case.
  - **Why it fails.** A Cauchy–Schwarz transfer of a bad event from `U` to `P0`
    loses `||rho||_2`, which is about `e^(S/2)`. A reverse transfer through
    `min rho >= (1-beta)^k`, about `1/ln k`, is not uniform. At `q = 1`,
    `beta = ln ln k / k`, the script gives:

    | `l` | `S` at `k_A` | `S` at `k_T = 4^(l-1)/12` | `S = 1` at | `k_0` |
    |---|---|---|---|---|
    | 20 | 47.7 | 40.2 | `k ~ 2^39.9` | `k ~ 2^83.3` |
    | 60 | 1.8e8 | 76.5 | `k ~ 2^120.7` | `k ~ 2^163.7` |

    Corollary SC of `dkkms-2to1-value-is-at-least-seed-concentration` bounds
    only `k beta^2 = O(l)`, so `S` is unbounded there. So `S` is the invariant
    that separates `T1` from `T2`: every coupling, covering or density transfer
    from a uniform Grassmann test dies at the step where it pays `e^(S/2)`, on
    `{S >> 1}`.
  - **Side remark, not established.** The comparison would extend `T1` from
    `SD* <= 10^(-5)` to `{S <= S_0}`, about `k >~ 4^l (ln ln k)^2`, which is a
    factor of about `2^43` below `k_0`. That shrinks `T2` to about
    `[k_A, polylog * k_T]`, matching Theorem W of
    `dkkms-seed-law-is-uniform-in-regime-and-far-in-window` up to polylog
    factors. It closes nothing load-bearing: `T2` contains no certified point,
    and certified points (`k >= 2^(4l^2+12)`) have `log10 S <= -468` at
    `l = 20`, where `T1` already applies.
  - **Artifact.**
    `experiments/dkkms-sound-point-rigidity-2026-09-17/check_density_comparison.py`
    prints ALL PASS. It checks the law of `N_i` for `l = 2..6` and the
    Gaussian-binomial sandwich exactly for `k = 2..8`. It also enumerates `rho`
    exactly at six tiny `(k,l,beta)`, checking `E rho = 1`, `rho >= phi` and
    `E rho^2 >= E phi^2`, and it tabulates `S` on the window for
    `l = 20, 25, 30, 40, 60`.
* **Quotient covering (2026-09-20).** Route
  `dkkms-local-rigidity-via-quotient-covering` through
  `dkkms-quotient-covering-proves-99-percent-rigidity` proves this claim, and
  so `T2`, with `eta_1 = 10^(-5)`, `zeta_1 = 1/128` and `l_0 = 66`. This holds
  for every `q >= 1`, both log readings and every smoothing law. The **OPEN**
  line above is superseded by that route.
  - Every event of the per-tuple argument is `H_U`-invariant: the rejection of
    two extensions and the disagreement with `lambda_U`. So the class labels
    descend to a linear table on `Gr(X_U/H_U, l)`.
  - There the image of the seed law has
    `chi^2 <= (1 - 2^(l-1-k))^(-2) exp(k beta^2 (2^(l-1) - 1)) - 1`.
    That goes to `0` on the whole window, because `k_A ~ e^l` beats `2^l`.
  - The "no covering transfer" conclusion of the previous entry holds only
    for transitive tests on `Gr(X_U, .)`. The class kill of the seed-law node
    is exactly that class, and the quotient test lies outside it.
  - Still not covered: `3 <= l <= 65` at the admissible points with
    `SD^cl > 10^(-5)`.
