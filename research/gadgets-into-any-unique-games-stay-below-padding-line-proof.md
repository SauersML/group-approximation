---
rg: 2
id: gadgets-into-any-unique-games-stay-below-padding-line-proof
kind: route
title: Canonicalize the gadget, walk a Hamming path, and pay each step against a relabelling-invariant fibre-plurality switch between two uniform reading points
target: gadgets-into-any-unique-games-stay-below-padding-line
requires: []
artifacts:
  - experiments/ugc-fiber-switch-adversary-2026-09-17/check_fiber_switch_adversary.py
  - experiments/ugc-fiber-switch-adversary-2026-09-17/results-2026-09-20.txt
---

Notation is as in the target claim. Nothing is imported. Step 1 is the
path-bound argument of item 1 of `three-lin-gadgets-stay-below-padding-line`,
rewritten for an output alphabet `[L]`. It is repeated here so this route is
self-contained.

Write `-j` for `[r] \ {j}`. Put `P_i = e ∘ p_i : H -> [L]`, where `p_i` is the
`i`-th coordinate projection.

## Step 1: canonical form and the path bound

**Canonical form.**
* For each `h ∈ H`, fix a completion `C_h` attaining `best(h)`: the primaries
  get `e(h)`, the references their intended values, and the auxiliaries are
  optimal.
* Send each variable `v` to the function `φ(v) : H -> [L]`,
  `φ(v)(h) = C_h(v)`.
  * A primary `x_i` goes to `P_i`.
  * A reference with intended value `a` goes to the constant function `a`.
* For a constraint `e = (v, v', γ)`, meaning `v' = γ(v)`, put
  `y_e = γ ∘ φ(v)` and `z_e = φ(v')`. Then `C_h` violates `e` iff
  `y_e(h) != z_e(h)`.
* Averaging over `h` uniform on `H`,
  `E_h best(h) = E_e [d(y_e, z_e)] / N`, where `d` is Hamming distance on
  `[L]^H`. Since `c = max_h best(h) >= E_h best(h)`,

  (1.1) `E_e d(y_e, z_e) <= N c`.

**Pull-back.** Let `A` be a random map `[L]^H -> [L]` with three properties:
* it is equivariant, `A(γ ∘ y) = γ(A(y))` for all `γ ∈ Sym([L])`;
* it fixes constant functions;
* it satisfies `A(P_i) = e(ξ_i)` for all `i`, where `ξ` is uniform on `G^r`.

Then `v -> A(φ(v))` is a random assignment of the gadget. Its primaries are
`e(ξ)`, uniform, and its references are at their intended values. So its
expected violated fraction is at least `E_ξ best(ξ) = s_rand`. That fraction
is `E_e Pr[A(z_e) != γ(A(φ(v)))] = E_e Pr[A(z_e) != A(y_e)]`, by equivariance.

**Path bound.** Put `M(A) = max Pr[A(y) != A(y')]`, over pairs at Hamming
distance `1`. All `A(y)` are defined on one probability space. So
`Pr[A(y) != A(z)] <= d(y, z) M(A)`, by the union bound along a Hamming path
from `y` to `z`. With (1.1),

  (1.2) `s_cert <= s_rand <= E_e d(y_e, z_e) M(A) <= N M(A) c`.

`s_cert <= s_rand` holds because `ξ ∈ H` with probability exactly `1/q`, by
(L1). So `E_ξ best(ξ) >= (1 - 1/q) min_(ξ ∉ H) best + (1/q) min_(ξ ∈ H) best`.

It remains to build `A` with `N M(A) <= 2 - 1/N`.

## Step 2: the two reading points

Draw `ξ` uniform on `G^r` and fresh randomness `ω`, independently.
* `h*` is the point with `h*_(-j) = ξ_(-j)`. It exists and is unique by (L1).
* Let `D` be the event `ξ_j != h*_j`.
* On `not D`, put `h' = h*`. On `D`, let `h'` be uniform in the fibre
  `F_(ξ_j)`, chosen with `ω`.

**Facts.**
* (F1) `h*` is uniform on `H` and independent of `D`. First, `ξ_(-j)` is
  uniform and determines `h*` bijectively. Second, `ξ_j` is independent of
  `h*`, so `Pr[D | h*] = 1 - 1/q`.
* (F2) `h'` is uniform on `H` and independent of `D`.
  * By (L2), `h*_j` is uniform on `G`, and every fibre has `|F_g| = N/q`.
  * Take `x ∈ F_g`. On `D`, `ξ_j = g` and `h*_j != g`, which has probability
    `(1/q)(1 - 1/q)`. So `Pr[D, h' = x] = (1/q)(1 - 1/q)(q/N) = (1 - 1/q)/N`.
  * Hence `Pr[h' = x | D] = 1/N`. On `not D`, `h' = h*` is uniform by (F1).
* (F3) `h*_i = ξ_i` for `i != j`, and `h'_j = ξ_j`. On `not D` this is
  because `h*_j = ξ_j`.

## Step 3: the switch and the three adversary properties

* **Score.** The score is
  `σ(y) = (1/N) sum_(g ∈ G) max_(a ∈ [L]) |{h ∈ F_g : y(h) = a}|`.
  * `σ(γ ∘ y) = σ(y)` for every permutation `γ` of `[L]`, since relabelling
    permutes the counts inside each fibre.
  * If `y, y'` differ only at a point `x ∈ F_g`, only the counts of fibre `g`
    change, each by at most `1`. So the maximum changes by at most `1`, and
    `|σ(y) - σ(y')| <= 1/N`.
  * `σ(P_j) = 1`, since `P_j` is constant on every fibre.
  * For `i != j`, (L2) makes `P_i` take each value `N/q^2` times on each fibre.
    So `σ(P_i) = q (N/q^2)/N = 1/q`.
* **Threshold.** Draw `t` uniform on `(1/q, 1)`, independent of `(ξ, ω)`.
  Put `A(y) = y(h')` if `σ(y) > t`, and `A(y) = y(h*)` otherwise.
* **Equivariance.** `A(γ ∘ y) = γ(y(·))` at the same reading point, because
  `σ` is invariant. So `A(γ ∘ y) = γ(A(y))`.
* **Constants.** `A` fixes constants, since both readings return the
  constant.
* **Primaries.** Since `t < 1 = σ(P_j)`, `A(P_j) = e(h'_j) = e(ξ_j)`. For
  `i != j`, `σ(P_i) = 1/q < t`, so `A(P_i) = e(h*_i) = e(ξ_i)`. Both use (F3).
  So `A(P) = e(ξ)`, which is uniform on `e(G)^r`.

## Step 4: the edge bound

Fix `y, y'` differing only at `x`.
* Let `S` be the event that `t` lies between `σ(y)` and `σ(y')`, where the two
  functions read different points.
* `Pr[S] <= |σ(y) - σ(y')|/(1 - 1/q) <= 1/(N(1 - 1/q))`.
* `S` depends only on `t`, so it is independent of `(ξ, ω)`, hence of `D`,
  `h*` and `h'`.

If `A(y) != A(y')`, then one of three events holds:
* (a) `not D` and `h* = x`, since on `not D` both functions read `h*`;
* (b) `D`, `not S` and the common reading point is `x`, since off `S` both
  read `h*` or both read `h'`, and they differ only at `x`;
* (c) `D` and `S`.

Their probabilities:
* (a) has probability `(1/q)(1/N)`, by (F1).
* (b): condition on `t`. Off `S` the common reading point is `h*` or `h'`,
  fixed by `t`. By (F1) and (F2), each satisfies `Pr[D, point = x] = (1 - 1/q)/N`.
  So (b) has probability `(1 - Pr[S])(1 - 1/q)/N`.
* (c) has probability `(1 - 1/q) Pr[S]`.

Summing,

`Pr[A(y) != A(y')] <= 1/(qN) + (1 - 1/q)/N + (1 - 1/q)(1 - 1/N) Pr[S]`
`<= 1/N + (1 - 1/q)(1 - 1/N)/(N(1 - 1/q)) = (2 - 1/N)/N`.

So `N M(A) <= 2 - 1/N`. With (1.2) this gives
`s_cert <= s_rand <= (2 - 1/N) c`, which is item 2 of the target.

**Item 3 (without L2).**
* (F1) and (F3) use only (L1).
* (F2) needs `h*_j` uniform and fibres of equal size. Both follow from (L1)
  when `j`'s marginal is uniform. That holds for every `H` in the examples.
  In general the fibres may be unequal, and we do not treat that case.
* So we state item 3 only when `h_j` is uniform on `G` for `h` uniform on `H`.
* Replace the window by `(σ_0, 1)`. The primaries still read correctly.
* `Pr[S] <= 1/(N(1 - σ_0))`, and Step 4 gives
  `N M <= 1 + (1 - 1/q)(1 - 1/N)/(1 - σ_0)`.
