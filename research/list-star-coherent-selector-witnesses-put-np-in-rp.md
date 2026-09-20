---
rg: 2
id: list-star-coherent-selector-witnesses-put-np-in-rp
kind: claim
title: Theorem C of the constant-bias node reruns with a list -- if at a typical seed star the satisfied ev-dishonest mass is small against SOME member of a list of L good outer labellings (chosen per star), the unchanged seed-guessing decoder puts the source in RP at a loss of 1/L^2, which on DKKMS affords L up to exp(k/(2exp(ql))); both recorded (Seed)/(List-Seed) counterexamples (the rank-split and defect-line kernel mixtures) have star-list mass O(2^-l) and die as selector witnesses, and the seed-form prerequisite is vacuous past L ~ gamma 2^l
distinct_from:
  constant-bias-selectors-need-seed-dishonest-witnesses: that is Theorem C with ONE global reference (condition Str); this allows a list, with the reference chosen separately at every seed star (w,a), and shows the loss is only the factor 1/L in the pigeonhole step, which the single-reference and seed forms cannot express.
  efficient-branch-selectors-list-decode-honest-outer-labels: that decodes from one honest witness; this reuses its decoder verbatim but lets different stars be explained by different good outer labellings.
  dkkms-seed-rigidity-fails-on-homogeneous-kernel-mixtures: that refutes single-reference (Seed); this shows the refuting mixture does not escape the decoder (star-list mass <= 2^(1-l), and even single-reference Str holds with the y branch at lift values above 0.645).
  few-patch-witnesses-above-half-decode-outer-labels: that asks for a single form to agree on more than half of the seed star; this needs only that the satisfied ev-dishonest part of each star be small against one list member, with list sizes up to exp(Theta(k)) at fixed l.
artifacts:
  - experiments/ugc-list-star-2026-09-17/check_list_star.py
---

**ESTABLISHED** (Theorem CL and Corollaries DK, SF, MIX, LS\*, M1).
Route: `list-star-coherent-selector-witnesses-put-np-in-rp-proof`.
The consequences are conditional on `NP not in RP`, as for Theorem C.

## What was asked

Two wave-12/13 results left the constant-bias cell of H1
(`parity-leaking-branch-selectors-reach-near-perfect-completeness`) with a
two-part prerequisite:

* (a) a list-seed statement on DKKMS;
* (b) a rerun of Theorem C of
  `constant-bias-selectors-need-seed-dishonest-witnesses` with a list of
  references.

Single-reference (Seed) is refuted by the rank-split mixture of
`dkkms-seed-rigidity-fails-on-homogeneous-kernel-mixtures` (Theorem M). A
parallel wave-13 lane (w13-ugc-last1, node `dkkms-list-seed-needs-lists-exponential-in-l`,
not on this branch) refutes List-Seed with list size independent of `l` by a
defect-line mixture (Theorem LS, value `0.61`). It records (b) as "affordable
against `exp(-k/exp(ql))` at large `k`, but it has to be proved".

This node proves (b) in the strongest form available: the *star* form. It then
shows that the seed-form prerequisite (a) is the wrong target, and that both
recorded counterexamples die under the star form.

## Setting

The notation is that of `constant-bias-selectors-need-seed-dishonest-witnesses`:
* a doubled LEC `x -> D(x)`, with outer game `Phi = (A, B, rho, pi)` and inner
  2-to-1 game `G` with law `mu`;
* annotations `(a_e, x_e, ev_e)` and seed `w_e = q_e`, with seed alphabet
  `|Sigma_q x {0,1}| <= 2^l`;
* the lift `U_o` of an orientation `o`, with bit function `G_e`;
* for a labelling `H = (sigma, tau)` of `G`, the set
  `Sat(H) = { e : pi_e(sigma_(p_e)) = tau_(q_e) }`.

Let `nu` be the `mu`-law of the **star** `(w_e, a_e)`. For an outer labelling
`lambda`, put

```text
X(H, lambda) := { e in Sat(H) : ev_e(sigma_(p_e)) != <lambda_(a_e), x_e> }.
```

For a list `Lambda = (lambda^1, ..., lambda^L)` of outer labellings, the
**star-list dishonest mass** is

```text
D_L(H, Lambda) := E_((w,a) ~ nu)  min_j  mu( X(H, lambda^j) | w_e = w, a_e = a ).
```

The reference may change from star to star. For `L = 1` this is the
`D(H, lambda)` of Theorem C, since `E_nu mu(X | w, a) = mu(X)`.

Hypotheses (E_tau) and (M) are those of Theorem C. The list form of (S) is:

* **(S_L)** on NO inputs `val(Phi) <= s < c0_L/2`, where
  `p = gamma'^3 2^(-l-2)` and `c0_L := p^2/(K^2 L^2) - 2 eps`.

## Statements

**Theorem CL (star-list decoding).** Let `x -> D(x)` be a doubled LEC for a
promise problem `Lang`, satisfying (E_tau) with `tau <= gamma'/4`, (M), and
(S_L). Let `S` be a randomized polynomial-time algorithm that outputs an
orientation of `G(x)`. Suppose that on every YES input `x`, with probability
`>= theta(|x|) >= 1/poly(|x|)` over the coins of `S`, the orientation
`o = S(x)` has the following two properties:
* a lift labelling `W` with `val(U_o, W) >= 1/2 + gamma`;
* a list `Lambda` of at most `L` outer labellings, each with
  `val_Phi >= 1 - eps`, such that the projection `H` of `W` has
  `D_L(H, Lambda) <= gamma - gamma'`.

Then `Lang in RP`, with one-sided success `>= theta c0_L/2` per trial.

The decoder is the Step 0 decoder of
`efficient-branch-selectors-list-decode-honest-outer-labels`, run as in
Theorem C:
* guess `s` uniform in `Sigma_q x {0,1}`;
* use threshold `gamma'/2`.

It does not know `Lambda`, `W` or `L`. Only the acceptance threshold `c0_L/2`
depends on `L`.

**Corollary DK (DKKMS list budget).** On the DKKMS instances in the form of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`, that is
`(Phi_k, G_multi)` with seed `(V, L')`, target `U` and direction `x_e`:
* (E_tau) holds with `tau = 2^(l-1-2k)`;
* (M) holds with `K = 1`;
* (S_L) holds as soon as the Lemma 5.4 soundness satisfies
  `eps_k = exp(-k/exp(ql)) < p^2/(8 L^2)` and `eps <= p^2/(8 L^2)`.

Fix `l`, `gamma` and `gamma'`. Then Theorem CL holds with lists of any size

```text
L  <  (p / 3) exp( k / (2 exp(ql)) ),       p = gamma'^3 2^(-l-2),
```

once `k` is large. So a list size `2^(O(l))` costs nothing in the parameter
order (`l`, then `k`, then `eps_3`), and neither does any
`L = exp(o(k))` at fixed `l`.

**Corollary SF (seed form, and its vacuity).** Assume (Sep_kappa) of Theorem C.
Let `H^j` be a `lambda^j`-reference of defect `r_j`, for `j = 1..L`. Let
`beta_L(H)` be the mass of `e in Sat(H)` with `tau_(q_e)` not in
`{ tau^j_(q_e) : j }`, the satisfied seed mass left uncovered. Then

```text
D_L(H, Lambda)  <=  beta_L(H) + sum_j r_j + L kappa.
```

So the seed form (List-Seed with `t = L`) implies the star hypothesis only
when `L kappa < gamma`, that is `L < gamma (2^l - 1)`. Past that point it
carries no information.

Conversely, take an input with a generic kernel `Phi` of rank `n`, with a good
`x`. Its `2^n` kernel branches `x + c∘Phi` restrict on `L'` to every functional
on `L'` wherever `Phi` is injective on `L'` (check D). That covers all seeds
but a `2^(l-1-n)` fraction of every surjective `V`. So on such inputs,
List-Seed with `t = 2^n` holds for every labelling, with uncovered mass
`<= 2^(l-1-n) + delta_sur`. Once `n >= l + log2(4/gamma)` this is within
`gamma/4`, and it is useless, because `t kappa > 2^(n-l) > 1`.

**Proposition MIX (vertexwise mixtures).** Assume (Sep_kappa). Let `H^j` be a
`lambda^j`-reference of defect `r_j`, for `j = 1..L`. Let `H` be a vertexwise
mixture: `sigma_p = sigma^(i(p))_p` and `tau_q = tau^(i(q))_q` for arbitrary
index maps `i`. Then

```text
D_L(H, Lambda)  <=  sum_j r_j + (L - 1) kappa.
```

No seed-level agreement with any single `H^j` is assumed. The reference at the
star `(w, a)` is `lambda^(i(w))`.

**Proposition LS\* (image-determined kernel mixtures).** Let the input carry a
generic kernel `Phi = (phi, zeta) : F_2^X -> F_2^l x F_2^s`, as in Theorem M
(vanishing on every `x_e`, surjective on `X_V` outside mass `delta_sur`), and
let `x` satisfy every equation. Put `n = l + s` and
`K0 := 0 x F_2^s <= F_2^n`. For a subspace `S <= F_2^n` let
`c(S) := S ∩ K0`. The **defect-line rule** gives a vertex with image
`S = Phi(L)` (A-side) or `S = Phi(L')` (B-side) the branch

* `y_d := x + <d, zeta(.)>` if `c(S) = <(0, d)>` is one-dimensional;
* `x` otherwise.

Every branch is a good assignment. Let `h` be the labelling this rule defines
(the rule reads `L` only through `Phi(L)`, and `Phi(H_U) = 0`). Let `Lambda`
be the `2^s` outer labellings `x` and `y_d`, `d != 0`. Then:

1. *Image model.* If `u_1, ..., u_l` are iid uniform in `F_2^n`, with B-image
   `W = span(u_1..u_(l-1))` and A-image `W~ = W + <u_l>`, the cross mass
   `chi := Pr[satisfied and the A-branch differs from the B-branch at u_l]`
   obeys
   ```text
   chi  <=  (2^s - 1)(2^l - 1) 2^-(2l+s-2)  <  2^(2-l).
   ```
2. *DKKMS.* On clean surjective tuples with `d' := dim X_V/H' >= k`,
   ```text
   D_(2^s)(h, Lambda)  <=  2^(2-l) + 2^(l-k) + delta_sur .
   ```

So the defect-line mixture has star-list mass `O(2^-l)` with the `2^s`
references read off at each seed, although it is `2^s`-list-seed-dishonest.
With `s = l` that is a list of size `2^l = exp(O(l))`, well inside the budget of
Corollary DK. Monte Carlo (check C2) indicates that no single one of the `2^s`
kernel-form references meets Str at `l = 7`: `min_d D ~ 0.143` against
`val - 1/2 ~ 0.122`. That is numerical only, and other references are not
searched.

**Remark M1 (Theorem M is not a Theorem C escape above 0.645).** Take the
rank-split mixture `h` of Theorem M: branch `x` iff `phi` is injective on the
vertex's subspace, and `y = x + z`. On every clean surjective `V`:

1. The only ev-dishonest satisfied edges against `lambda_y := y` are x-x edges
   with `z(x_e) = 1`. Exactly,
   ```text
   D_V(h, lambda_y) = b (1 - c) / 2 ,
   ```
   with `b, c` as in Theorem M. Since `val_V(h) >= 1 - bc`,
   ```text
   (val_V(h) - 1/2) - D_V(h, lambda_y)  >=  1/2 - b(1+c)/2  >  1/2 - 3b/4 ,
   ```
   which is positive for `l >= 4` and `d' >= l + 3`. At `k = d' = 4l` the left
   side is `0.0385` at `l = 4` and `0.0634` at `l = 7`, and it tends to
   `0.0668`. In the limit `D -> P_1/4 = 0.1444`. So h meets
   single-reference Str for every `gamma` in `(0.1444 + gamma', 0.2112 - o(1)]`,
   that is, at lift values above about `0.645`.
2. With `L = 2` and the reference read off the B-branch,
   `D_2(h, (x, y)) <= Pr[z|_(L') = 0] <= 2^(1-l)`, plus the unclean and
   non-surjective mass.

So (Seed) fails for `h`, as Theorem M says. Still, both theorems apply to any
selector whose witnesses project to `h`:
* Theorem C, above lift value `0.645`;
* Theorem CL with `L = 2`, at every `gamma > 2^(1-l) + gamma' + delta_sur`.

The quantity bounded below in item 3 of Theorem M is the *seed-form* mass
(B-labels against `hon(lambda)`). Item 1 here is the *ev-form* mass `D` of
Theorem C's actual hypothesis Str. The two differ because a y-labelled seed
with an x-labelled A-neighbour is seed-dishonest against `y` but can still be
ev-honest, and Lemma F only bounds ev-form by seed-form plus `kappa`, not
conversely.

## What this kills

**Class killed (under `NP not in RP`, on DKKMS at fixed `l` and large `k`).**
Every selector whose YES witnesses project to a *kernel-branch mixture*: a
labelling each of whose vertices uses the honest encoding of one of at most
`L < (p/3) exp(k/(2 exp(ql)))` good outer labellings, with the branch at an
A-vertex agreeing, on satisfied edges, with the branch read at its seed except
on mass `gamma - gamma'`. This includes:
* the rank-split mixture of Theorem M (star-list mass `<= 2^(1-l)`);
* the defect-line rule of LS\* (star-list mass `< 2^(2-l)`), which is this
  node's reading of the mixture of Theorem LS; that node is not on this branch,
  so the match is not checked line by line;
* every vertexwise mixture of `L` low-defect references (Proposition MIX,
  `sum r_j + (L-1) kappa`);
* every seed-covered labelling with `L < gamma(2^l - 1)` (Corollary SF).

It also kills, as a closing strategy, every attempt to close the
constant-bias cell through a *seed-form* list statement (List-Seed): by
Corollary SF it carries no information once the list exceeds `gamma 2^l`, and
by its converse it holds trivially with `2^n` kernel branches on every input
with a generic kernel of rank `n`.

**Invariant.** The star-list dishonest mass `D_L`, and for mixtures the cross
mass `chi`: satisfied edges whose A-branch disagrees with the branch read at
the seed, evaluated at the direction `x_e`.

**Where every member dies.**
* The decoder dies nowhere. Only the pigeonhole of Step 3 of Theorem CL sees
  `L`, and it costs a factor `1/L` in `E q`, hence `1/L^2` in `c0_L`.
* Mixtures die at the fibre count: a cross edge is either a defect edge or a
  collision `pi_e(sigma) = pi_e(sigma')` between two branch labels at the same
  A-vertex, which has mass `<= kappa` per pair (MIX).
* For image-determined mixtures they die at the rank count: a cross edge
  forces a kernel vector `(0, d)` into `W~` orthogonal to the B-image, an
  affine system of rank `>= n + l - 2` in the images (LS\*).

## What survives

The whole constant-bias cell of H1 on DKKMS, under `NP not in RP`, now reduces
to the failure of one 50 percent statement about the inner game.

> **(Star-List)** On DKKMS YES instances, every labelling `H` with value
> `>= 1/2 + gamma` has a list of at most `L_max(k) = exp(o(k))` good outer
> labellings with `D_L(H, Lambda) <= gamma - gamma'`.

A witness type escaping Theorem CL must have, at a constant fraction of seed
stars, satisfied ev-dishonest mass against *every* good outer labelling. The
reference may even be chosen after seeing the star. So it cannot be a mixture
of boundedly many good assignments of any kind recorded so far.

The image-determined subcase, with kernel-form lists, is a clean Grassmann
statement:

> **(GStar_n)** Let `F` assign to every subspace `S <= F_2^n` of dimension
> `l-1` or `l` a linear functional `F(S)` on `S`. Let `W` be a uniform
> `(l-1)`-space and `u` uniform, and suppose
> `Pr[u notin W, F(W+u)|_W = F(W)] >= 1/2 + gamma`. Then some list `Psi` of at
> most `L_max` linear functionals on `F_2^n` has
> `E_W min_(psi in Psi) Pr_u[u notin W, F(W+u)|_W = F(W), F(W+u)(u) != psi(u)] <= gamma - gamma'`.

Pulled back through a surjective `Phi`, with outer labellings `x + psi o Phi`,
(GStar_n) gives (Star-List) for image-determined labellings of J-instances, up
to `2^(l-k) + delta_sur`, by the transfer in the proof of LS\*. When
`2^n <= L_max`, `Psi` may be all functionals, and (GStar_n) says only that
`u -> F(W+u)(u)`, on the satisfied `u` at a typical `W`, is within
`gamma - gamma'` of a linear function. Nothing recorded implies it: compare
Lemma A of `few-patch-witnesses-above-half-decode-outer-labels`, whose
equality case is realised by an arbitrary function. It is OPEN here.

This neither proves nor refutes UGC.

## Checks

`experiments/ugc-list-star-2026-09-17/check_list_star.py` runs in about ten
seconds and exits 0. It has four parts:
* **Part A (Theorem CL):** 400 random stars for the Step 1 star inequality
  (minimum slack 0), then 60 toy runs of the unchanged decoder against planted
  lists (`L = 1..4`, `eps > 0`, decoy branches), with exact output laws. Every
  trial checks `P >= gamma'`, `E Q >= p`, the union bound, the pigeonhole
  `max_j E q^j >= p/(KL)` and `E val >= (E q^(j*))^2 - 2 eps`.
* **Part B (Theorem M):** B1, the exact law `Pr[z|_(L') = 0] <= 2^(1-l)` for
  `l = 2..12` and `d' = l-1..39`. B2, exact image-model enumeration for
  `l = 2, 3, 4`; at `l = 4` it gives value `0.7308`, single-reference mass
  `0.1538`, and star mass `D_2 = chi = 0.0192`. B3, the exact identity
  `D_V(h, lambda_y) = b(1-c)/2` and the margin table of Remark M1.
* **Part C (defect-line rule, LS\*):** C1, exact enumeration for
  `(l, s) = (3,1), (3,2), (3,3), (4,1)`, checking `D_star <= chi <= bound < 2^(2-l)`.
  C2, seeded Monte Carlo (30000 samples) for `s = l = 5, 6, 7`, which gives
  `chi 2^(l-2) ~ 0.1` and the single-reference escape at `l = 7`.
* **Part D (Corollary SF converse):** for `n = l + 1`, `l = 2, 3, 4`, every
  generic seed is covered by the `2^(l+1)` kernel branches (7/7, 210/210,
  26040/26040), while `t kappa > 2`.

## Attempts

* 2026-09-18 (swarm-0917-w13-w13-ugc-follow): proved Theorem CL,
  Corollaries DK and SF, Propositions MIX and LS\*, and Remark M1. The route
  does not use the parallel node `dkkms-list-seed-needs-lists-exponential-in-l`
  (not on this branch): LS\* is stated and proved here for the defect-line rule
  as defined above. Not attempted: (Star-List) and (GStar_n) themselves; 2-to-2
  inner games; whether Remark P padding preserves Lemma 5.4 soundness.
* 2026-09-19 (swarm-0917-w14-w14-ugc-follow): (GStar_n) calibrated in
  `codim-one-gstar-threshold-is-two-to-minus-half-l`. At `n = l+1` the bias
  threshold is `Theta(2^(-l/2))`: with the full list GStar holds for every
  `gamma > delta(l) <= (2/3) 2^(-l/2)` (spectral triangle cap), and an
  APN-Sidon rainbow graph gives violators at `gamma ~ 2^(-l/2)/16`. A
  projection lift carries violators to every `n >= l+1` at
  `>= 2^(-l/2)/43`, for every list size. So any proof of GStar_n with loss
  `O(2^(-l))` is impossible. Still open: an upper bound `D <= C 2^(-l/2)`
  for `n >= l+2`, where twisted families other than triangles appear once
  `dim K >= 2`.
