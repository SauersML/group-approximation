---
rg: 2
id: hadamard-crossing-needs-folding-gap
kind: claim
title: Folding-repair lemma - R*(k) <= K z_U(k) + eta_k, where z_U is the auxiliary-unfolded (Wiman-relaxed) adversary value and eta_k the least max edge mass inside the non-folded locus of an optimal relaxed adversary, so a Hadamard gadget crosses 2 only if every optimal relaxed adversary puts mass > R*(k) - 2 on some edge of its locus
distinct_from:
  hadamard-gadget-deletion-ratio-window: that bounds R*(k) by explicit decoded adversaries and imports the cap K z_U <= 2 on relaxed soundness; this bounds R*(k) - K z_U, the folding gap, by one quantity computed from the relaxed optimum, turning "true soundness is required" into a measurable prerequisite.
  hadamard-gadget-crosses-padding-line: that is the open statement R*(k) > 2; this gives a necessary condition, eta_k > R*(k) - 2 > 0, for it.
artifacts:
  - experiments/ugc-hadamard-gadget-k4-2026-09-17/hadk_mincut.py
  - experiments/ugc-hadamard-gadget-k4-2026-09-17/hadk_fold_ub2.py
  - experiments/ugc-hadamard-gadget-k4-2026-09-17/results-2026-09-19.txt
---

**ESTABLISHED.** Items 1 and 2 are proved below in full. Item 3 adds
Martinsson's Proposition 49(c), imported verbatim through
`hadamard-gadget-deletion-ratio-window` item 5.

## Setting

The notation is that of `hadamard-gadget-deletion-ratio-window`: `K = 2^k`,
`Q = {-1,1}^K`, primaries `P = {chi_a}`, and length-one edges
`e = (x, x + e_j)`, where `j = dir(e)`. `R*(k) = K z*(P)`.

* **Relaxed adversaries.** A *relaxed assignment* for a pattern
  `xi in {-1,1}^P` is any `f : Q -> {-1,1}` with `f(chi_a) = xi_a` and
  `f(-chi_a) = -xi_a`. It need not be folded anywhere else.
* **The relaxed value.** `z_U(k)` is the minimum over distributions `mu` of
  relaxed assignments with `xi` uniform of `max_e Pr_mu[f cuts e]`. Here
  `-e` is the edge `(-x, -y)`.
* **The non-folded locus.** For `f`, put `D_f = {x : f(x) = f(-x)}`. It is
  symmetric and contains no `±chi_a`.
* **The locus mass.** `eta_k` is the minimum, over optimal `mu` for `z_U`,
  of `max_e Pr_mu[e ⊂ D_f]`.
* For `k >= 2` the minimum over the optimal `mu` is attained, by
  compactness of the optimal face.

## Theorem

1. **Folding repair.** For every relaxed distribution `mu` with `xi`
   uniform, there is a folded distribution `nu` random on `P` such that, on
   every length-one edge,
   `Pr_nu[cut e] <= (Pr_mu[cut e] + Pr_mu[cut -e])/2 + (1/K) Pr_mu[e ⊂ D_f]`.
2. **Gap bound.** `z_U(k) <= z*(k)`, and `R*(k) <= K z_U(k) + eta_k`.
3. **Crossing needs a folding gap.** `K z_U(k) <= 2`, so `R*(k) <= 2 + eta_k`.
   A witness for `hadamard-gadget-crosses-padding-line` at `k` exists only if
   `eta_k > R*(k) - 2 > 0`. That is, every optimal relaxed adversary must
   place mass above `R*(k) - 2` on some edge lying entirely in its non-folded
   locus.

## Proof

**Item 1.**

* **The folded pieces.** Given `f`, let `S = {f = +1}` and let
  `f~(x) = -f(-x)`, with `S~ = {f~ = +1} = -(S^c)`.
  * `f~` has the same pins as `f`, since `f~(chi_a) = -f(-chi_a) = xi_a`.
  * Put `T = S ∩ S~` and `U = S ∪ S~`.
  * Since `-S~ = S^c`, we get `-T = (-S) ∩ S^c = (S~)^c ∩ S^c = U^c`.
  * So `Q` is the disjoint union of `T`, `-T` and `D = U \ T = S Δ S~`,
    and `D = D_f`.
* **The folded assignment.** Define `g = +1` on `T`, `g = -1` on `-T`, and
  `g(x) = sigma x_i` on `D`, with `sigma = ±1` and `i in F_2^k` uniform and
  independent of each other and of `f`.
  * `g` is folded, because `D` is symmetric and `x -> sigma x_i` is odd.
  * Every `±chi_a` lies in `T ∪ -T`, so `g(chi_a) = xi_a`. Since `xi` is
    uniform under `mu`, the law `nu` of `g` is random on `P`.
* **Per-edge accounting.** Take an edge `e = (x, y)`.
  * If `e` joins `T` to `-T`, then `g` cuts it, and `cut_T(e) = cut_U(e) = 1`.
  * If `e` joins `T` or `-T` to `D`, then `g` cuts it with probability
    `1/2`, and `cut_T(e) + cut_U(e) = 1`.
  * If `e` lies inside `T` or inside `-T`, both sides are `0`.
  * If `e ⊂ D`, then `g` cuts it iff `i = dir(e)`, which has probability
    `1/K`, while `cut_T(e) = cut_U(e) = 0`.
  * Hence `Pr_{sigma,i}[g cuts e] = (cut_T(e) + cut_U(e))/2 + (1/K)[e ⊂ D]`.
* **Submodularity.** Per edge, `cut_{S∩S~}(e) + cut_{S∪S~}(e) <= cut_S(e) + cut_{S~}(e)`
  holds, as a check of the four cases for which ends lie in `S` and in
  `S~` shows. Also `cut_{S~}(e) = cut_f(-e)`. Averaging over `mu` gives
  item 1.

**Item 2.** The first inequality holds because folded assignments are relaxed.

* Take `mu` optimal for `z_U`, attaining `eta_k`.
* The map `e -> -e` permutes length-one edges, so both `Pr_mu[cut e]` and
  `Pr_mu[cut -e]` are at most `z_U`.
* Item 1 then gives `z* <= max_e Pr_nu[cut e] <= z_U + eta_k/K`.

**Item 3.** `z_U(k)` is Wiman's relaxed soundness in minimax form.

* By LP duality, exactly as in item 1 of `hadamard-gadget-deletion-ratio-window`,
  `K z_U` equals the largest `K min_mu E_w[cut]` over weightings `w` of
  length-one equality edges.
* The relaxed feasible set is invariant under the affine group on
  coordinates and under negation. So an optimal `w` can be averaged to be
  invariant, which makes it direction-balanced.
* Such a `w` has dictator violation exactly `1/K`, that is, completeness
  `1 - 2^(-k)`. Its best relaxed adversary is, per pattern, an assignment
  folded on the primaries and unconstrained on the auxiliary variables,
  which is Martinsson's Definition 28 of `rs`.
* Proposition 49(c) then gives `K z_U = (1 - rs)/(1 - c) <= 2`.
* Combining this with item 2 gives the rest.

## What this changes

`hadamard-gadget-crosses-padding-line` now needs a positive folding gap
`Delta(k) = R*(k) - K z_U(k) > 0`, and in fact a gap above `2 - K z_U(k)`.
This is a prerequisite with its own ways to fail:

* **Show the gap vanishes.** It suffices to show that some optimal relaxed
  adversary has a non-folded locus containing no edge of large mass, that
  is, `eta_k -> 0`. That would kill the family.
* **Measured values.** In `results-2026-09-19.txt`:
  * `k = 3`: `Delta(3) = 0`. Both values equal `11/8`, each certified exactly.
  * `k = 4`: `K z_U(4) >= 331440289/227504128 ~ 1.45685`, which is Wiman's
    value. Floating-point LP optimality says this is an equality. It is set
    against a certified `R*(4) <= 1.534727` from
    `hadamard-gadget-ratio-k4-sandwich`.
  * So `Delta(4) in [0, 0.078]`, and whether it is positive is
    `hadamard-gadget-k4-true-soundness-beats-wiman`.
