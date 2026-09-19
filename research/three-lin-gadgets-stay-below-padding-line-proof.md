---
rg: 2
id: three-lin-gadgets-stay-below-padding-line-proof
kind: route
title: Canonicalize the gadget, walk a Hamming path, and pay each step against an anchored threshold adversary decoded from an information set
target: three-lin-gadgets-stay-below-padding-line
requires: []
artifacts:
  - experiments/ugc-affine-gadget-cap-2026-09-17/check_anchored_adversary.py
  - experiments/ugc-affine-gadget-cap-2026-09-17/results-2026-09-18.txt
---

Notation is as in the target claim. No premise is imported. Every step uses
only the definitions.

## Item 1 (path bound)

**Canonical form.**
* For each `h ∈ H`, fix a completion `C_h` attaining `best(h)`: primaries
  equal to `h`, and references at their intended values.
* Send each variable `v` of the gadget to the function `φ(v) : H -> G`,
  `φ(v)(h) = C_h(v)`.
  * A primary `x_j` goes to the projection `p_j`.
  * A reference with intended value `c` goes to the constant function `c`.
* Given an assignment `B : G^H -> G`, the pull-back `v -> B(φ(v))` is an
  assignment of the gadget. It violates the constraint `v' = γ(v)` iff
  `B(φ(v')) != γ(B(φ(v)))`.
* For the dictator `B = d_h`, `d_h(y) = y(h)`, the pull-back is `C_h`. So
  `best(h) = Pr_e[φ(v')(h) != γ(φ(v)(h))]` over the gadget's random
  constraint `e = (v, v', γ)`.

**Pull back `A`.** The pull-back of `A` gives the primaries the uniform values
`A(p_j)` and the references their intended values. It is therefore a
distribution admissible for `s_rand`. Every assignment with primaries `ξ`
costs at least `best(ξ)`, so
`s_rand >= E_ξ best(ξ) >= s_cert`, with `|H|/q^r = Pr[ξ ∈ H]`.

**Walk a Hamming path.** Fix a constraint `e = (v, v', γ)` and put
`y = γ ∘ φ(v)` and `z = φ(v')`.
* By equivariance, `γ(A(φ(v))) = A(y)`. So the pull-back of `A` violates `e`
  iff `A(z) != A(y)`.
* Let `d(e)` be the number of points of `H` where `y` and `z` differ. Walking
  from `y` to `z` one point at a time takes `d(e)` steps, each through
  functions in `G^H`.
* By the union bound, `Pr[A(z) != A(y)] <= d(e) M(A)`.
* Also `d(e) = N Pr_h[z(h) != γ(φ(v)(h))]` for `h` uniform on `H`.

Averaging over `e`:

```text
s_rand <= uval(A) <= M(A) N E_h best(h) <= N M(A) c.
```

## Item 2 (anchors)

**Distinct anchors meet rarely.**
* Same primary: `γ ∘ p_j` and `γ' ∘ p_j` with `γ != γ'` agree exactly where
  `h_j` is a fixed point of `γ^{-1} γ'`. Since `h_j` is uniform on `G`, that
  is at most `f N/q` points.
* Different primaries: `γ ∘ p_j` and `γ' ∘ p_k` with `j != k` agree on
  exactly `N/q` points, because `(h_j, h_k)` is uniform on `G^2`.
* So two distinct anchors agree on at most `ρ N` points.

**Uniqueness above `α0 N`.**
* Suppose `y` agrees with distinct anchors `g_1`, `g_2` on `a_1` and `a_2`
  points. Every point lies in at most one of the two agreement sets, unless
  `g_1` and `g_2` agree there. So `a_1 + a_2 <= N + ρ N <= 2 α0 N`.
* Hence at most one anchor has more than `α0 N` agreements with `y`.

**Neighbours share the anchor.**
* Let `y, y'` differ at one point, with `y` agreeing with its anchor `g` on
  `a > α0 N` points. Suppose `y'` agrees with some anchor `g'` on more than
  `α0 N` points.
* Then `y'` agrees with `g` on at least `a - 1 >= α0 N` points. If `g' != g`,
  the two counts sum to more than `2 α0 N >= N + ρ N`, which is impossible.
  So `g' = g`.

## Item 3 (anchored threshold adversary)

**Well defined.** A near `y` has more than `t N >= α0 N` agreements with its
anchor. By item 2 that anchor is unique.

**Hypotheses of item 1.**
* *Equivariance.* The anchor set is closed under `Γ`, and
  `agree(γ' ∘ y, γ' ∘ g) = agree(y, g)`. So `γ' ∘ y` is near iff `y` is,
  with anchor `γ' ∘ g`.
  * The near value becomes `γ' γ (ξ_j) = γ'(A(y))`.
  * The far value becomes `(γ' ∘ y)(h*) = γ'(A(y))`.
* *Random on the primaries.* An anchor `γ ∘ p_j` agrees with itself on
  `N > t N` points, so it is near.
  * Under `D_j` it gets `γ(ξ_j)`.
  * Under `not D_j` it gets `γ(h*_j) = γ(ξ_j)`.
  * So `A(γ ∘ p_j) = γ(ξ_j)` always, and `(A(p_j))_j = ξ` is uniform.
* *Constants.* A constant function agrees with every anchor on exactly `N/q`
  points, because `h_j` is uniform. Since `N/q < α0 N`, it is far, so
  `A(c) = c(h*) = c`.

**Cost of one edge.** Let `y, y'` differ exactly at `h_0`.
* *Neither endpoint above `α0 N`.* Both are far for every `t`, and
  `A(y) != A(y')` iff `h* = h_0`. Since `h*` is uniform, `N Pr[cut] = 1`.
* *Otherwise.* By symmetry, `y` has the larger top agreement `a`, with
  `a > α0 N`, at the anchor `g = γ ∘ p_j`. Put `b = agree(y', g)`.
  * `b ∈ {a - 1, a}`. It cannot exceed `a`, because `y'`'s top agreement is
    at most `a`.
  * By item 2, `y'` is near iff `b > t N`. If `y'`'s top agreement exceeds
    `α0 N`, its anchor is `g`. Otherwise `b <= α0 N <= t N`, and `y'` is
    never near.
* *Under `not D_j`*, the rule never uses the near value, so the endpoints get
  `y(h*)` and `y'(h*)`. The cut is `[h* = h_0]`.
* *Under `D_j`*, split on `t`:
  * `t < b/N`: both near, both `γ(ξ_j)`, no cut.
  * `b/N <= t < a/N`: only `y` near. This needs `b = a - 1`, and has
    `t`-measure `(1/N)/(1 - α0)`. The cut is `[y'(h*) != γ(ξ_j)]`.
  * `t >= a/N`: both far, cut `[h* = h_0]`. The `t`-measure is
    `(1 - a/N)/(1 - α0)`.
* *Averaging.* By (H1), `h*` is uniform and independent of `D_j`. By (H2),
  given `h*` and `D_j`, `γ(ξ_j)` is uniform on `G \ {g(h*)}`.
  * `Pr[y'(h*) != γ(ξ_j) | D_j] = b/N + (1 - b/N)(1 - 1/(q-1))`. On the `b`
    points where `y'(h*) = g(h*)` the cut is certain; elsewhere it has
    probability `1 - 1/(q-1)`.
  * This equals `1 - (1 - b/N)/(q - 1)`.

Hence, for `b = a - 1`,

```text
N Pr[cut] = (1 - δ_j) + δ_j [ (1 - a/N) + 1 - (1 - (a-1)/N)/(q-1) ] / (1 - α0),
```

and for `b = a` the middle band is empty, so
`N Pr[cut] = 1 - δ_j + δ_j (1 - a/N)/(1 - α0) <= 1`.

**Maximising.**
* In `a`, the bracket has slope `(-1 + 1/(q-1))/N <= 0`. So it is largest at
  the smallest admissible `a = α0 N + 1`.
* There it equals
  `(1 - α0)(1 - 1/(q-1)) + (1 - 1/N)`, since
  `(1 - α0 - 1/N) + 1 - (1 - α0)/(q - 1)` rearranges to that.
* Dividing by `1 - α0` gives `Y = 1 + (1 - 1/N)/(1 - α0) - 1/(q - 1)`.
* `Y >= 1`, because `1 - α0 <= 1/2` makes `(1 - 1/N)/(1 - α0) >= 1 >= 1/(q-1)`.
  So the cost `1 - δ_j + δ_j Y` is increasing in `δ_j`, and is at most `λ`
  with `δ = max_j δ_j`.
* `α0 N + 1 <= N` holds because `max(1, f) <= q - 1` gives
  `N(1 - ρ)/2 >= N/(2q) >= q/2 >= 1`. So the edge exists, and the script
  finds `λ` attained.

## Item 4 (decoders)

**Trivial decoder.** Here `ξ` is independent of `h*`.
* `Pr[D_j | h*] = 1 - 1/q`, which is (H1).
* Given `h*` and `D_j`, `ξ_j` is uniform on `G \ {h*_j}`, which is (H2).

**Information-set decoder.** `I` is drawn independently of `ξ`.
* Given `I`, the map `h -> h_I` is a bijection and `ξ_I` is uniform, so `h*`
  is uniform on `H` and independent of `I`.
* For `j ∈ I`, `ξ_j = h*_j`, so `D_j` fails.
* For `j ∉ I`, `ξ_j` is uniform and independent of `(I, ξ_I)`, so it is
  independent of `h*`.
* Hence `Pr[D_j | h*] = (1 - θ_j)(1 - 1/q)`, which is (H1), and (H2) holds.

## Item 5 (consequences for `f <= 1`)

**`α0` is exact.** Pairwise uniformity gives `q^2 | N`. Then
`N(1 + 1/q)/2 = (N/q)(q + 1)/2` is an integer:
* for `q` odd, `(q + 1)/2` is an integer;
* for `q` even, `N/q` is even.

So `α0 = (q + 1)/(2q)`, `1 - α0 = (q - 1)/(2q)`, and
`λ = 1 + δ (2q - 1 - 2q/N)/(q - 1)`.

**The four cases.**
* (a) The trivial decoder has `δ = 1 - 1/q`, which gives
  `λ = 3 - 1/q - 2/N`.
* (b) For `H_b` (a coset, still pairwise uniform), every 2-subset of
  `{1, 2, 3}` is an information set. A uniform one has `θ_j = 2/3`, so
  `δ = (q - 1)/(3q)`. With `N = q^2`, `λ = 1 + (2q^2 - q - 2)/(3q^2)`.
  * Translations have `f = 0`, and the affine group has `f = 1`.
  * `S_3` is the affine group of `F_3`.
* (c) For `k >= 3`, `{x_1 + ... + x_k = b}` is pairwise uniform with
  `N = q^(k-1)`. Every `(k-1)`-subset is an information set, so
  `δ = (1 - 1/q)/k` and `λ = 1 + (2q - 1 - 2q/N)/(kq)`.
* (d) With `δ = (1 - 1/q)(1 - θ)` and `1 - θ <= q/(2q - 1)`,
  `λ - 1 <= (2q - 1 - 2q/N)/(2q - 1) < 1`.

## Item 6 (more fixed points)

Apply item 3 with the 3Lin information-set decoder, `δ = (q - 1)/(3q)`, and
`N = q^2`.

| `Γ` | `f` | `ρ` | `α0` | `λ` |
|---|---|---|---|---|
| `S_4` | 2 | `1/2` | `3/4` | `89/48 ~ 1.854` |
| `A_5` | 2 | `2/5` | `18/25` | `194/105 ~ 1.848` |
| `S_5` | 3 | `3/5` | `4/5` | `166/75 ~ 2.213` |
| `S_6` | 4 | `2/3` | `5/6` | `277/108 ~ 2.565` |

* `A_5` has `f = 2`: its 3-cycles fix 2 points, its double transpositions
  fix 1 and its 5-cycles fix none.
* The `S_4` row is checked by the script on 300 random edges, with the
  maximum equal to `89/48`.

