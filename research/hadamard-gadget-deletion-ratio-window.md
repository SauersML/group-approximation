---
rg: 2
id: hadamard-gadget-deletion-ratio-window
kind: claim
title: The best deletion ratio R*(k) of a Hadamard Had_k -> Max-2Lin(2) gadget is K min_A max_e Pr[A cuts e], is at most 5/2 - 2^(1-k) for every k and at most 1 + delta_k(3 - 2^(2-k)) with delta_k the mean normalized distance to RM(1,k), so it is below 2 for every k <= 5 -- no Hadamard gadget of arity at most 32 crosses the padding line
distinct_from:
  unique-games-np-hard-below-the-padding-line: that is the open milestone R > 2 for some unique-games point; this bounds one proof family for it (Hadamard gadgets into Max-2Lin(2), a 2-label unique game) and kills it for k <= 5, leaving it open.
  ug-hardness-deficit-ratio-padding-line: that caps padded proper splits of d-to-d games at the one-branch count; this caps gadget reductions from Hadamard predicates, whose outputs are genuine 2-label unique games, dying at the soundness step against a decoded threshold adversary.
  twin-mixture-caps-deficit-ratio-of-local-amplifiers: that caps black-box maps whose input is already a unique game; this caps reductions whose input is a Hadamard CSP, which that node lists as a survivor ("direct reductions from 3LIN or label cover with non-split outputs").
  hadamard-gadget-crosses-padding-line: that is the open statement R*(k) > 2 for some k; this proves it fails for every k <= 5 and that it can only hold with ratio below 5/2.
artifacts:
  - experiments/ugc-hadamard-gadget-window-2026-09-17/check_five_halves_adversary.py
  - experiments/ugc-hadamard-gadget-window-2026-09-17/check_decoder_adversary.py
  - experiments/ugc-hadamard-gadget-window-2026-09-17/rm1_mean_distance.c
  - experiments/ugc-hadamard-gadget-window-2026-09-17/minimax_gadget_value.py
  - experiments/ugc-hadamard-gadget-window-2026-09-17/results-2026-09-18.txt
---

**ESTABLISHED (upper-bound window and class kill for k <= 5).** Proof:
`hadamard-gadget-deletion-ratio-window-proof`. Items 1 to 4 are elementary
plus a finite exact enumeration. Item 5 imports Martinsson verbatim.

## Setting

This follows Håstad, Huang, Manokaran, O'Donnell and Wright (HHM+15, below). Fix `k >= 2` and put
`K = 2^k`. Coordinates are `i in F_2^k`, and the cube is `Q = {-1,1}^K`. For
`a in F_2^k`, the character `chi_a in Q` is `chi_a(i) = (-1)^(a.i)`.

* A *primary set* is `P = {chi_a : a in F_2^k}`, the setting of HHM+15
  Definitions 2.21 to 2.24, or `P' = {chi_a : a != 0}`, the generic primaries
  of the `(2^k - 1)`-ary predicate `Had'_k`.
* A *gadget* is a finite probability distribution `G` on Max-2Lin(2)
  constraints `x = y` or `x != y` between variables `x, y in Q`.
* `uval(A; G)` is the probability that `A : Q -> {-1,1}` violates a random
  constraint. For a distribution `A` over assignments, it is the average.
* The dictators are `d_i(x) = x_i`.
* `A` is *folded* if `A(-x) = -A(x)`. A distribution is *random on* `P` if
  `(A(y))_(y in P)` is uniform on `{-1,1}^P`.
* A `(c, s)`-gadget for `P` has `uval(d_i; G) <= c` for all `i`, and
  `uval(A; G) >= s` for every distribution `A` of folded assignments random
  on `P`. For `P` this is HHM+15 Definition 2.24 verbatim. For `P'` it is the
  folded form, via HHM+15 Proposition 2.19, of a generic `Had'_k` gadget
  (HHM+15 Definition 2.16).
* The **best deletion ratio** is `R*(k) = sup s/c` over `(c, s)`-gadgets for
  `P` with `c > 0`. `R*'(k)` is the same for `P'`.
* `z*(P) = min_A max_e Pr_A[A(x) != A(y)]`. Here `A` ranges over folded
  distributions random on `P`, and `e = (x, y)` over length-one edges of `Q`
  (Hamming distance one). The minimum exists because the feasible set is a
  polytope.
* `delta_k` is the mean distance from a uniform `xi in {-1,1}^P` to the
  signed dictator code `C = {(tau chi_a(i))_(a) : i in F_2^k, tau = +-1}`,
  divided by `|P|`. For `P`, `C` is the first-order Reed--Muller code
  `RM(1,k)`, and `delta_k = 1/2 - E max_i |W_i| / 2^(k+1)` with
  `W_i = sum_a xi_a chi_a(i)`. For `P'`, `C` is its puncturing at `0`, and
  the quantity is written `delta'_k`.

## Theorem

1. **Minimax identity.** `R*(k) = K z*(P)` and `R*'(k) = K z*(P')`. The
   supremum is attained, by a gadget on length-one equality edges with
   `c = 1/K` exactly.
2. **Five-halves cap.** `R*(k) <= 5/2 - 2^(1-k)` and
   `R*'(k) <= 5/2 - 2^(1-k)` for every `k`. This improves HHM+15 Theorem 6.1,
   which gives `1/(1 - e^(-1/2)) ~ 2.54`.
3. **Decoded threshold adversary.** Suppose `(i, tau)` is chosen jointly with
   a uniform `xi in {-1,1}^P` so that `i` is uniform, and
   `Pr[xi_a != tau chi_a(i) | i] = delta` for every `i` and every `a`.
   * Then the distribution `A` of the proof is folded, is random on `P`, and
     has `K Pr[A cuts e] = 1 + delta (3 - 4/K)` on every length-one edge with
     an endpoint `x` of `m(x) > 3K/4`. Every other length-one edge has cost
     exactly `1`.
   * So `R*(k) <= 1 + delta (3 - 4/K)`.
   * Taking `(i, tau)` a uniformly random nearest codeword of `C` achieves
     `delta = delta_k`. So `R*(k) <= 1 + delta_k (3 - 2^(2-k))`, and likewise
     for `P'` with `delta'_k`.
   * The choice `tau = +1` with `i` uniform and independent of `xi` gives
     `delta = 1/2`, which is item 2.
4. **Exact values and the class kill.** These are exact rationals computed by
   exhaustive enumeration.

   | `k` | `delta_k` | bound on `R*(k)` | `delta'_k` | bound on `R*'(k)` |
   |---|---|---|---|---|
   | 2 | `1/8` | `5/4` | `0` | `1` |
   | 3 | `11/64` | `183/128 ~ 1.4297` | `1/8` | `21/16` |
   | 4 | `1961/8192` | `~ 1.6583` | `341/1536` | `~ 1.6105` |
   | 5 | `78015813/2^28` | `~ 1.8356` | `2381339/2^23` | `~ 1.8161` |

   Hence **`R*(k) < 2` and `R*'(k) < 2` for every `k <= 5`**. No Hadamard gadget
   reduction of arity at most `32` into Max-2Lin(2) reaches deletion ratio `2`.
   * The same holds for any sequence of such gadgets, since ratios
     `<= 1.8356` are bounded away from `2`.
   * Two values are tight. `R*'(3) = 21/16` holds by a column-generation LP
     together with the bound. `R*(3) = 11/8` is HHM+15 Theorems 3.1 and 1.8,
     and the LP reproduces it. The LP is floating point, so only the upper
     bounds are claimed as proved.
5. **Relaxed soundness is capped at exactly 2 (imported).** Martinsson,
   Proposition 49(c): any `Had_k`-to-Max-2Lin(2) gadget with completeness
   `1 - 2^(-k)` has `(1 - rs)/(1 - c) <= 2`, where `rs >= s` is Wiman's relaxed
   soundness. By his Proposition 49(b), reducing to that completeness does
   not decrease the relaxed ratio. So no certificate built on relaxed
   soundness, which is the method behind the best known point `1.48969`,
   can show that a Hadamard gadget crosses the padding line.
6. **Erratum to HHM+15 Proposition 2.25, direction (1) => (2).** HHM+15
   Theorem 3.1 gives a `(1/8, 11/64)` `Had_3` gadget, with ratio `11/8`. By
   items 1 and 3 with `P'`, every generic `Had'_3` gadget has ratio at most
   `21/16 < 11/8`. So `(1) => (2)` fails at `k = 3` with `(c, s) = (1/8, 11/64)`.
   * The step that fails: the mixture of `A` and `-A` is random on
     `P' ∪ {chi_0}` only when the law of `A(chi_0)` given `xi` is even in `xi`.
   * HHM+15 Corollary 2.26 remains true. The proof embeds a Definition 2.24
     gadget as a generic gadget for the `2^k`-ary predicate `Had_k` of their
     Definition 2.22, whose satisfying set `{+- chi(i)}` is a balanced
     pairwise-independent subgroup, and then applies their Proposition 2.17
     directly. So their `11/8` hardness stands.

## What this changes

* `ug-hardness-deficit-ratio-padding-line` and
  `twin-mixture-caps-deficit-ratio-of-local-amplifiers` listed direct
  reductions into genuine unique games as survivors.
  * Hadamard gadgets into Max-2Lin(2) are the best-developed such family.
    They are the source of every record inapproximability for
    Min-2Lin(2)-deletion: `11/8`, then `1.48969`.
  * A gadget with `s/c > 2` would give `unique-games-np-hard-below-the-padding-line`
    through `padding-line-hardness-from-hadamard-gadget`.
  * This node shows that the family is dead for `k <= 5`, that it has a hard
    ceiling below `5/2` for every `k`, and that its only certificate technique
    for large `k` (relaxed soundness) is capped at exactly `2`.
* **What survives, sharply.** `hadamard-gadget-crosses-padding-line` needs
  `k >= 6` and a true-soundness analysis.
  * At `k = 6` the decoder bound estimates to `1.9889` by Monte Carlo, below
    `2` but not proved.
  * From `k = 7` the decoder adversary has `delta_7 ~ 0.3745 > 0.3368`, so it
    no longer rules out a crossing.
  * The heuristic "optimal Hadamard gadgets approach the Min-2Lin(2)-deletion
    constant as `k` grows" is thus pinned to a window
    `R*(k) in [11/8, 5/2 - 2^(1-k)]`.
    * The lower end `11/8` for `k >= 3` holds by Martinsson's lifting, which
      he describes as "the completeness stays the same and the soundness does
      not decrease". It is not used here.
    * For `k <= 5` the window closes below `2`.

## Sources

* HHM+15. J. Håstad, S. Huang, R. Manokaran, R. O'Donnell, J. Wright,
  "Improved NP-inapproximability for 2-variable linear equations" (version
  dated December 23, 2015). Verbatim quotes and the verification date are
  in `hadamard-gadget-deletion-ratio-window-proof`.
* Björn Martinsson, arXiv:2408.04832. Verbatim quotes are in the proof route.
