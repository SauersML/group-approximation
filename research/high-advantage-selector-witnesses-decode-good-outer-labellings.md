---
rg: 2
id: high-advantage-selector-witnesses-decode-good-outer-labellings
kind: claim
title: A polynomial-time branch selector whose orientation lift gives a near-honest labelling of some outer labelling of value 15/16 a lift value 1 - 1/64 decodes that outer labelling at a uniform rate 2^(-l)/192, so on DKKMS instances every near-1 selector witness must be far from every locally honest patchwork unless NP is in RP
distinct_from:
  efficient-branch-selectors-list-decode-honest-outer-labels: that decodes at completeness 1/2 + gamma but needs outer violation eps below p^2/2 ~ 2^(-2l), so it only reaches honest encodings of near-perfect outer labellings; this trades the low completeness for lift value near 1 and then tolerates any outer violation eps < 1/2 - 4(xi + zeta + d), with witness distance zeta and a per-constraint dirt d, so it reaches non-global patchwork outer labellings.
  dkkms-2to1-instances-satisfy-selector-decoding-hypotheses: that kills honest encodings a|_R of global 3LIN assignments with eps_out(a) <= p^2/8; this kills, at lift value near 1, every locally honest patchwork of any outer labelling of value 15/16, which is the class that global 99% rigidity cannot reach.
  efficient-branch-selector-on-proved-2to1-instances: that is the open selector hole; this proves that the hole implies NP in RP unless the DKKMS test fails the local 99% rigidity dkkms-grassmann-2to1-test-is-locally-99-percent-rigid.
artifacts:
  - experiments/ugc-selector-rigidity-2026-09-17/check_high_advantage_decoder.py
---

**ESTABLISHED.** Route: `high-advantage-selector-witnesses-decode-proof`.

This is a sharpening of Theorem 1 of
`efficient-branch-selectors-list-decode-honest-outer-labels` for the regime the
selector hole actually needs: YES lift value `1 - eta'` with `eta' -> 0`. It
turns the hole into a statement about 99%-regime structure of the DKKMS test
(Corollary B).

## Setting

Use the LEC setting of `efficient-branch-selectors-list-decode-honest-outer-labels`
(outer game `Phi = (A, B, rho, pi)` with `A`-labels in `F_2^m`, inner game `G`
with `|Sigma_w| <= 2^l`, constraint law `mu`, annotations `(w_e, a_e, x_e)`,
bit functions `g_e`, lift `G_g`, hypothesis (E)). Two hypotheses change.

* **(M=) two-sided marginals.** `nu_A(a) <= K rho_A(a)` and
  `rho_A(a) <= K' nu_A(a)` for every `a`. The DKKMS instances have `nu_A = rho_A`,
  so `K = K' = 1` (item 4 of `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`).
* **(B_d) branch identity with dirt.** A labelling `H` of `V_G` is *honest for*
  an outer labelling `lambda` *with dirt* `d` if there is a set `Cl` of
  constraints with `mu(Cl) >= 1 - d` such that, for every `g` and every
  `e in Cl`: if `H` satisfies the oriented constraint of `e` in `G_g`, then
  `g_e(H_(w_e)) = <lambda_(a_e), x_e>`. Hypothesis (B) of the parent is the case
  `H = hon(lambda)`, `d = 0`.

A *witness* for `lambda` at *distance* `zeta` is a lift labelling `W` and a
labelling `H` honest for `lambda` with dirt `<= d`, such that `W` and `H` agree
at both endpoints of every constraint outside a set of `mu`-mass `<= zeta`.

## Statements

**Theorem 3 (high-advantage selectors decode).** Let `R` be an LEC with (E) at
`tau <= 1/16`, (M=) and (B_d). Put

```text
p0 = 2^(-l) / 192,       c1 = 1 - 2 eps - 8 K' (xi + zeta + d).
```

Suppose that `c1 > 0` and:

* `x notin Lang` implies `val(Phi) <= s` with `s < p0^2 c1 / 2`;
* a randomized polynomial-time selector `S` has the following property for every
  `x in Lang`: with probability `>= theta` over its coins there is an outer
  labelling `lambda` with `val_Phi(lambda) >= 1 - eps` and a witness for
  `lambda` (dirt `<= d`, distance `<= zeta`) of lift value `val_(G_g) >= 1 - xi`.

Then `Lang in RP`, with one-sided success probability `>= theta p0^2 c1 / 2`
per trial.

The decoder is the one of the parent's Step 0 with the list threshold `gamma/2`
replaced by the absolute constant `1/8`. It never uses `lambda`, `h` or the
witness.

**What changed.** Theorem 1 needs `eps < p^2 / (2K^2)` with
`p = gamma^3 2^(-l-2)`, so its outer labelling must be `2^(-2l)`-close to
perfect. Theorem 3 needs only `2 eps + 8K'(xi + zeta + d) < 1`, with no
dependence on `l`. The price is lift value near `1` instead of `1/2 + gamma`,
which is exactly what the selector hole promises. The toy check shows the
difference is real: in 30 of 59 non-trivial trials Theorem 1's bound
`p^2 - 2 eps` is negative while Theorem 3's bound holds.

## The DKKMS instances

Notation is that of `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`
(`G_folded`, `G_multi`, the copies `e` with seed `(V,L')`, target `U`,
direction `x_e`, the outer game `Phi_k`, Lemma 5.4 soundness `eps_k`).

**The lift is the doubled-alphabet lift.** The selector hole speaks of
`U_o(G_folded)` from `orientation-lifts-sandwich-2to1-game-values`, whose right
label at `(V,L')` is a pair `(sigma', b)` with `b in {0,1}`. Treat it as an LEC
lift with `Sigma_w = Fun(L') x {0,1}`, so `|Sigma_w| = 2^l`. Its bit function
`G_e(sigma', b)` is the value at `x_e` of the unfolding at the member `(U,L)` of
the unique class label that the bijection of `e` sends to `(sigma', b)`.

**Locally honest patchworks.** Let `lambda` be any outer labelling of `Phi_k`
(an `A`-label `lambda_U in F_2^(vars U)` per k-tuple and a `B`-label `lambda_V`
per smoothed tuple). Let `kappa` pick one member `(U_C, L_C)` of every class
`C`, and let `b` be any bit per `B`-vertex. Define

```text
hon_kappa(lambda)_C       := the sigma in Fun(R_C) whose unfolding at (U_C, L_C) is lambda_(U_C)|_(L_C),
hon_kappa(lambda,b)_(V,L') := (lambda_V|_(L'), b_(V,L')).
```

The first is well defined because unfolding `Fun(R_C) -> Fun(L)` is a bijection
(item 1 of the membership node). A copy `e` with member `(U,L)` is *clean* if
the unfolding of `hon_kappa(lambda)_C` at `(U,L)` is `lambda_U|_L`. The *dirt*
`d_kappa(lambda)` is the `mu`-mass of unclean copies.

* When `lambda = lambda^a` is the honest outer labelling of a global assignment
  `a` and `kappa` picks clean members, `hon_kappa(lambda^a)` is `hon(a)` on the
  `A`-side and `d_kappa(lambda^a) <= eps_out(a)`.
* When `lambda` is honest per k-tuple but its assignments vary from tuple to
  tuple, `hon_kappa(lambda)` is a *patchwork*: dirt is paid only at members
  whose class representative carries a different assignment.

**Corollary A (patchworks decode).** Fix `l >= 2` and `k` with
`2^(l-1-2k) <= 1/16` and `eps_k <= p0^2 / 4`, `p0 = 2^(-l)/192`. Assume
`NP not in RP`. Then no randomized polynomial-time orientation `o` of
`G_folded` has the following property with confidence `theta` on every YES
instance of regular `Gap3Lin(1 - eps_3, s*)`: some labelling of `U_o(G_folded)`
of value `>= 1 - xi` agrees, outside constraint mass `zeta`, with some
`hon_kappa(lambda, b)` for an outer labelling with
`val_(Phi_k)(lambda) >= 15/16` and `d_kappa(lambda) <= 1/64`, where
`xi + zeta <= 1/64`.

With these numbers `c1 >= 1 - 1/8 - 8(1/64 + 1/64) = 5/8`, so
`p0^2 c1 / 2 >= 5 p0^2 / 16 > eps_k`.

**Corollary B (the selector hole needs non-rigid witnesses).** Let
`dkkms-grassmann-2to1-test-is-locally-99-percent-rigid` hold with constants
`eta_1, zeta_1 <= 1/128` for parameters `(l, k)` as in Corollary A. If a
polynomial-time orientation `o` of `G_folded` has YES lift value
`val(U_o) >= 1 - eta'` with `eta' <= eta_1`, then `NP in RP`.

So on every DKKMS parameter point admissible for Corollary A,

```text
efficient-branch-selector-on-proved-2to1-instances   ==>   NP in RP   or   not (local 99% rigidity).
```

The hole asks for `eta'(eta) -> 0`, so it eventually undercuts any fixed
`eta_1`. Under `NP not in RP`, the selector route to UGC therefore needs the
DKKMS test to have YES labellings of value arbitrarily close to `1` that are
`zeta_1`-far from every locally honest patchwork of every outer labelling of
value `15/16` and dirt `1/64`.

## Consequences

* **Survivor (H2) sharpened to (H2-loc).** The previous survivor was "YES lift
  witnesses far from every honest encoding `hon(a)` of every good global
  assignment". Corollary A removes, at lift value `>= 1 - (1/64 - zeta)`, every
  witness within `zeta` of a locally honest patchwork `hon_kappa(lambda, b)` of an
  outer labelling of value `15/16` and dirt `1/64`. The patchwork labels may use
  a different 3LIN assignment on every k-tuple, and the right bits `b` are free.
  What survives must be non-honest *inside* the Grassmann layer of a constant
  fraction of k-tuples: class labels on the `l`-spaces of one `U` that are not
  restrictions of one functional.
* **Why global rigidity was the wrong target (heuristic, not established).** On
  YES instances with two near-satisfying assignments `a^1, a^2` that differ on a
  large nearly homogeneous set, colour each k-tuple by a balanced function of its
  first equation and use `a^(colour)`. Only the roughly `beta k`-coordinate
  resampling of `U -> V -> U'` changes the colour, so the patchwork has
  `G_multi` value about `1 - O(beta)`, yet it stays a constant distance from
  every `hon(a)`. It is locally honest, so Corollary A covers it. Any
  99%-rigidity statement that lands on global assignments must therefore lose at
  rate `beta`. The local statement need not.
* **A new prerequisite that can fail on its own.** The selector route now
  splits:
  1. `dkkms-grassmann-2to1-test-is-locally-99-percent-rigid` must **fail**, a
     99%-regime structure question about the DKKMS test alone. It mentions no
     selector and no complexity assumption.
  2. The failure must be witnessed on YES instances by labellings a
     polynomial-time selector can orient toward. That is the old hole restricted
     to the (H2-loc) class.
  If (1) holds, the route is dead under `NP not in RP`, independently of UGC.

This neither proves nor refutes UGC, the Rich 2-to-1 Games Conjecture, or the
selector hole.

## Not covered

* **Parameter points.** Corollaries A and B need `2^(l-1-2k) <= 1/16` and
  `eps_k <= p0^2/4`. The same regime ("take `k` so large") is used by the
  corollary of `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`. It
  is not checked here that the parameters DKKMS fix for `R_eta` lie in it.
* **Moderate completeness.** Selectors with YES lift value between
  `1/2 + gamma` and `1 - 1/64` are handled only by Theorem 1, that is only for
  near-perfect global honest witnesses.
* **Other instances.** The KMS 2-to-2 instances are not treated.

## Artifact

`check_high_advantage_decoder.py` builds 60 random toy composed instances:
* an outer projection game with planted violation up to about `1/6`;
* `nu_A = rho_A`, and direction laws missing up to `1/16` of `F_2^5`;
* predictor tables that are noisy at the honest seed label and adversarial
  decoys at every other seed label, with about 15% of the `A`-vertices random.

It runs the threshold-`1/8` decoder exactly, with no sampling of its coins, and
asserts three things:
* list size `<= 64`;
* `q_a >= p0` at every vertex whose predictions are correct with probability
  `>= 3/4`;
* `E val >= E[q_a q_a' 1{good, good, C, D}] >= p0^2 (1 - 2 eps - 2 rho_A(Bad))`.

Output: all 60 trials pass; 59 have a positive bound, and in 30 of those
Theorem 1's bound is negative.
