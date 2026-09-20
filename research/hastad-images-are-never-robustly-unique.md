---
rg: 2
id: hastad-images-are-never-robustly-unique
kind: claim
title: Håstad 3LIN images of satisfiable formulas are never robustly unique at scale 1/k -- replacing a long-code dictator B_W by the odd character chi of sigma_W together with a product set Q of one-variable flip pairs on m private clauses costs only 2^m eps + 3^(-m)/2 per touched equation (Q is invisible to the projection except with probability 3^(-m)) but moves the table by distance 1/2, so 2^(r0)+1 disjoint such modifications are near-optimal and pairwise 1/(6k)-far, and RU fails for every x*, every C of dimension r0 and every rho < 1/(12k)
distinct_from:
  good-dkkms-orientations-admit-short-star-lists-on-hard-inputs: that is (SF_P), a hardness-plus-star-list statement on exact kernel rank; this is a source-side obstruction showing that the standard Håstad YES images lie outside the robust-uniqueness promise that replaced (P1).
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is the selector hole H1; this kills one family of routes to the hardness half of its constant-bias kill and does not mention selectors.
  exact-kernel-rank-does-not-exclude-flip-violators: that builds near-solution families on J-instances by swapping lines; this builds them on every Håstad test instance from projection-invisible label sets, independently of the outer Label Cover.
artifacts:
  - experiments/ugc-hastad-ru-2026-09-17/check_hastad_invisible_sets.py
---

**ESTABLISHED.** Route: `hastad-images-are-never-robustly-unique-proof`.

## Setting

This node is about the robust-uniqueness hardness prerequisite (P1^RU),
`gap3lin-hard-with-robustly-unique-yes-solutions`, and the notions of
`robust-uniqueness-bounds-robust-kernel-rank` (both live on the main line).
Here is the self-contained version.

* A 3LIN instance is a probability law `omega` on equations
  `x_a + x_b + x_c = c_e` over F_2. `val_omega(a)` is the probability that an
  equation drawn from `omega` is satisfied by `a`.
* `nu(v) = (1/3) sum_e omega(e) |e ∩ {v}|` is the variable-slot mass.
  `dist_nu(a, b)` is the `nu`-mass of `{v : a_v != b_v}`. This is a
  pseudometric.
* **(RU_(kappa, rho, r0)).** There are `x*` and a linear subspace `C` with
  `dim C <= r0` such that every `a` with `val_omega(a) >= 1 - kappa` has
  `dist_nu(a, x* + C) <= rho`.
* (P1^RU) asks for NP-hardness of regular Gap3Lin with completeness
  `1 - eps` on YES instances satisfying RU with
  `kappa = eps + gamma'/(4k)`, `rho < (1 - beta0)/(12k) <= 1/(12k)` and
  `r0 <= l + 1`. Here `0 < gamma' < gamma <= 0.105`, and `(k, l)` are
  DKKMS parameters with `k >> 2^l`.

**The Håstad test.** Start from a projection Label Cover with question sets
`U`, `W`, a law on pairs `(W, U)`, label sets `[L_U]` and `SAT(W)`, and
projections `pi = pi_(W->U)`. The 3LIN instance `H_eps` has:

* folded long-code tables `A_U` on functions `[L_U] -> {±1}`;
* folded tables `B_W` on functions `SAT(W) -> {±1}`.

An equation is sampled as follows. Draw `(W, U)`, uniform `f`, uniform `g`,
and `mu` with independent entries of `-1`-bias `eps`. Put
`h = (f∘pi) g mu`. The equation is `A_U(f) B_W(g) B_W(h) = 1`.

`omega` is this test law, with equations duplicated to make it uniform.
Write `q_W` for the probability of `W`.

## Statement

**Theorem G (invisible label sets).** Suppose a labelling `sigma` satisfies
every constraint. Suppose further that for a set `𝒲_0` of questions `W`
there are:

* a nonempty set `Q_W ⊆ SAT(W) \ {sigma_W}` of even size `<= M`, such that
* `Pr_(U | W)[pi_2(Q_W) != ∅] <= theta`, where `pi_2` is the set of points
  of odd multiplicity in the multiset image.

Put `Delta := M eps + theta/2`. Let `S_1, ..., S_N` be disjoint subsets of
`𝒲_0` with `q(S_i) := sum over W in S_i of q_W` lying in `[q_lo, q_hi]`.

Then there are assignments `a_1, ..., a_N` of `H_eps` such that:

1. `val(a_i) >= 1 - eps - q_hi Delta`;
2. `dist_nu(a_i, a_j) >= (2/3)(1 - zeta/2) q_lo` for `i != j`.

Here `zeta` is the largest probability, over `W`, of a degenerate equation
(`h = ±g`). It is `0` if slots are counted with multiplicity.

Hence, if `q_hi Delta <= gamma'/(4k)`, `(2/3)(1 - zeta/2) q_lo > 2 rho` and
`N >= 2^(r0) + 1`, then `H_eps` fails
`RU_(eps + gamma'/(4k), rho, r0)` for **every** `x*` and every `C`.

**Corollary H (Håstad's instances).** Take Håstad's source: the `t`-fold
parallel repetition of Gap-3SAT-5, with `U` one uniformly and independently
chosen variable of each of the `t` clauses of `W`. Fix `gamma' in (0, 1)`
and put `m = ⌈log_3(2/gamma')⌉`. Assume:

* `t >= m`;
* `eps <= gamma' 2^(-m-2)`;
* `k >= 2^(r0+1) + 1`;
* the formula has enough clauses (`n >= n_0(t, k)`).

Then `H_eps(phi)` fails `RU_(eps + gamma'/(4k), rho, r0)` for every
`rho < 1/(12k)`, every `x*` and every `C` with `dim C <= r0`.
This holds for every satisfiable formula `phi` with at least `n_0` clauses,
whatever its number of satisfying assignments.

In the DKKMS regime (`eps = eps_3 <= eps/(2k) -> 0`, `r0 <= l + 1`,
`k >> 2^l`) every hypothesis holds. At `gamma' = 0.105` the choices are
`m = 3`, `t >= 3` and `eps <= 0.0032`.

**Remark P (padding and regularization).** Suppose a later step places the
test law with share `s0 > 0` inside a larger law. The other equations must
be satisfied by a lift that is linear on the copies, for example a copy
blow-up with consistency equations. Then the same conclusion holds with
`q(S_i) ≈ 1/(4 k s0)`, provided `k s0 >= 2^(r0+1) + 2`. This improves on the
constant-share dilution bound of the "gadget padding" bullet of
`gap3lin-hard-with-robustly-unique-yes-solutions`.

## Consequences

* **Class kill.** No proof of (P1^RU) can have YES images that are Håstad
  test instances over a parallel-repeated (or any "collapsing") Label Cover.
  This is true whatever the Label Cover YES promise is: uniqueness,
  Valiant–Vazirani isolation or robust uniqueness of labellings. The "Håstad-format images"
  heuristic of `gap3lin-hard-with-robustly-unique-yes-solutions` is therefore
  wrong. There, RU does *not* reduce to near-uniqueness of Label Cover
  labellings. The obstruction lives inside a single long-code table, not in
  the choice between labellings.
* **The invariant, and where it dies.** The invariant is the *testing ratio*
  of the inner test, deficit per unit `nu`-distance, measured on the
  character modifications `chi_(sigma_W) -> chi_({sigma_W} ∪ Q)`. It is
  `3 Delta <= 3(M eps + theta/2)`, which is made arbitrarily small.
  Proposition T of `robust-uniqueness-bounds-robust-kernel-rank` needs
  ratio `eps0 > (3 gamma' + 24 k eps)/(1 - beta0)`, about `0.36`. So RU
  dies at the first step, robust testability of each inner table at distance
  `1/2`.
* **What survives.** Theorem G needs label sets that the projections collapse
  with probability `1 - theta`. Smooth Label Cover makes every small label
  set visible with probability `1 - delta_s`, and so evades it. Any
  (P1^RU) proof therefore needs a 3LIN hardness with an inner test of
  constant testing ratio at every scale, over a smooth or otherwise
  non-collapsing outer PCP. No such hardness is recorded.

## Spark (not claimed)

Take `m ≈ log_3(4k/gamma')` and `eps << k^(-1.63)`. The `W`-local
modifications `y_W = chi_(sigma_W) chi_T` then give a huge family of
near-solutions, of order `|𝒲_0|` independent directions. Each has dirty mass
`<= Delta` per touched equation. They look like approximate
homogeneous-kernel directions of rank far above `l + 2` on every Håstad
image. If the Theorem O' machinery of
`exact-kernel-rank-does-not-exclude-flip-violators` accepts such
non-`Phi(v) = v` approximate kernels, then the flip orientation violates
(P2^rob) on Håstad images as well. This has not been checked.

## Attempts

* **2026-09-20, swarm-0917-w21-w21-ugc-pull (finite-models / transplanter).**
  Tried to confirm the "Håstad-format images" heuristic, namely that RU on
  Håstad images reduces to Label Cover near-uniqueness. Found instead the
  in-table invisible-set family of Theorem G, which refutes it for every
  source formula. The runnable check verifies the Fourier acceptance formula
  against a direct Monte Carlo of the test, the invisibility probability
  `3^(-m)` by enumeration, and the distance `1/2`.
