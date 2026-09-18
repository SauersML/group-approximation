---
rg: 2
id: pl-line-hosts-bound-dilation-rank-proof
kind: route
title: Direct proof from the derivative images of finitely generated groups
target: pl-line-hosts-bound-dilation-rank
requires:
  - fg-groups-have-fg-derivative-images
---

Direct proof; the required node is used only for Corollary 2. Notation as in the target.
Identify `H` with its image in `PL_S(R)` and write `m d m^-1 = q_m d` (additively in `D`)
for `m in M`, where `m -> q_m` is the inclusion `M <= Q^x_{>0}`.

**Step 1 (unbounded roots).** `D` is a countable torsion-free group of rank 1, hence the
union of a chain `<g_1> <= <g_2> <= ...` of cyclic groups. The chain does not stabilize,
since `D` is not cyclic, so the indices `[<g_j> : <g_k>]` are unbounded in `j`. So every
`d in D` has an `n`-th root in `D` for infinitely many `n`.

**Step 2 (`D` acts freely).** Suppose `d in D`, `d != 0`, has a fixed point. Its fixed
set `F` is closed, nonempty and not all of `R`. So some component of `R \ F` has a finite
endpoint. Say it is `(u, v)` with `u` finite; the case of a finite right endpoint `v`
is the mirror image, with left slopes.

- Near `u`, on `[u, u + eps)`, `d` is linear with slope `lambda_d in S`.
- `lambda_d != 1`, since otherwise `d` fixes points of `(u, v)`.
- Let `e in D` with `e^n = d`. If `e(u) > u` then `e^n(u) > u`, because `e` is
  increasing; likewise if `e(u) < u`. So `e(u) = u`.
- Near `u`, `e` is linear with slope `lambda_e in S`, and `lambda_e^n = lambda_d`.

By Step 1 this holds for infinitely many `n`. In the free abelian group `S` of finite rank,
an element with `n`-th roots for infinitely many `n` is trivial. So `lambda_d = 1`,
a contradiction. Hence every nonzero element of `D` acts without fixed points.

**Step 3 (Hölder semiconjugacy).** For `d != 0`, either `d(x) > x` for all `x` or
`d(x) < x` for all `x`. Declare `d > 0` in the first case.

- This is a translation-invariant total order on the abelian group `D`.
- It is Archimedean: if `0 < d` and `d^k(x_0) < d'(x_0)` for all `k`, the increasing
  bounded sequence `d^k(x_0)` converges to a fixed point of `d`.
- By Hölder's theorem there is an order-preserving injective homomorphism
  `tau: D -> (R,+)`. Its image is non-cyclic, hence dense.

Fix `x_0` and put `pi(x) = sup{ tau(d) : d(x_0) <= x }`. The set is nonempty and bounded
above, because the orbit of `x_0` is unbounded in both directions: a bounded monotone
orbit would converge to a fixed point. Then:

- `pi` is nondecreasing and `pi(d x) = pi(x) + tau(d)`;
- `pi(e x_0) = tau(e)`, so the image of `pi` contains the dense set `tau(D)`. A
  nondecreasing map with dense image in `R` is continuous and onto `R`;
- for any `y`, `sup{ tau(d) : d(y) <= x } = pi(x) - pi(y)`:
  - `<=` holds because `d(y) <= x` gives `pi(y) + tau(d) <= pi(x)`;
  - `>=` holds because, for `t < pi(x) - pi(y)`, density gives `d` with
    `t < tau(d) < pi(x) - pi(y)`. Then `pi(d y) < pi(x)`, so `d(y) < x`.

(This is the standard Hölder argument, e.g. A. Navas, *Groups of circle
diffeomorphisms*, 2011, §2.2.)

**Step 4 (dilations descend to affine maps).** Let `m in M` and `y = m^-1(x_0)`. The
substitution `d = m d' m^-1` is a bijection of `D`, and `tau(m d' m^-1) = q_m tau(d')`.
So

```text
pi(m x) = sup{ tau(d) : d(x_0) <= m x } = sup{ q_m tau(d') : d'(y) <= x }
        = q_m (pi(x) - pi(y)).
```

Thus `pi ∘ m = A_m ∘ pi`, with `A_m(t) = q_m t + b_m` affine of slope `q_m`.

**Step 5 (a common fixed point, and the germ map).** The maps `A_m` commute. Affine maps
of slope `!= 1` that commute have the same fixed point. So all `A_m`, `m != 1`, fix one
`y_0`.

`J = pi^-1(y_0)` is a compact interval, since `pi` is continuous, nondecreasing and onto.
From `pi ∘ m = A_m ∘ pi` we get `m(J) = J`. So every `m in M` fixes `e = max J`. Let
`lambda(m) in S` be the slope of `m` on `[e, e + eps)`. Composing right germs at the
common fixed point makes `lambda: M -> S` a homomorphism.

It is injective. If `lambda(m) = 1`, then `m` is the identity on some `(e, e + eps)`.
For `x` there, `pi(x) > y_0`, since `x` is not in `J`. Then
`pi(x) = pi(m x) = q_m (pi(x) - y_0) + y_0`, so `q_m = 1` and `m = 1`. Hence `M` embeds
in `S`. This proves the Statement.

**Corollary 1.** For `n >= 2`, put the following matrices in the upper left corner,
with `I_{n-2}` below:

| Subgroup | Matrices | Contained in |
|---|---|---|
| `Q x| Q^x_{>0}` | `[[a, b], [0, 1]]`, `a > 0` | `GL_n(Q)` (and `Aff(Q)`) |
| `Q x| {a^2}` | `[[a, b], [0, a^-1]]`, `a > 0` | `SL_n(Q)`, `B_2(Q)` |

In the second subgroup, conjugating `[[1, b], [0, 1]]` by `diag(a, a^-1)` gives
`[[1, a^2 b], [0, 1]]`, so `M = {a^2}`. Neither subgroup meets the scalars
nontrivially: a scalar of this form has `b = 0` and `a = a^-1 > 0`, so it is `1`. So
both embed in `PGL_n(Q)` and `PSL_n(Q)`. Their `M` has infinite rank.
`Z[1/6] x| <2,3>` is a subgroup of the first with `M ~ Z^2`.

**Corollary 2.** Let `c(f, x)` be the right derivative of `f` at `x`. The chain rule for
increasing PL maps gives `c(f g, x) = c(f, g x) c(g, x)`. Each generator, and hence each
inverse of a generator, takes finitely many values of `c`. By
`fg-groups-have-fg-derivative-images`, all slopes of `Gamma` lie in a finitely generated,
hence free abelian of finite rank, subgroup `S <= R_{>0}`. Apply Corollary 1 in
`PL_S(R)`.

**Corollary 3 (sharpness).**

- **The map.** Choose `s` with `2^s >= q`. Write `q 2^s` as a sum of exactly `2^s`
  powers of two `2^(k_i)`, `k_i >= 0`. This is possible: split terms of the binary
  expansion (at most `q <= 2^s` terms) until there are `2^s` of them. Let `m` be linear
  with slope `2^(k_i)` on `[(i-1)/2^s, i/2^s]`, with `m(0) = 0`. Then `m(1) = q`.
  Extend by `m(x + j) = m(x) + q j`. So `m` lies in `PL_2(R)`, with dyadic breakpoints
  and dyadic values.
- **The relation.** `m z m^-1 = z^q`.
- **Faithfulness.** The map `BS(1,q) -> <z, m>` sends the normal closure `Z[1/q]` of the
  first generator injectively: `m^-k z^j m^k = 1` forces `j = 0`. A normal subgroup of
  `BS(1,q)` that meets `Z[1/q]` trivially centralizes `Z[1/q]`, so it lies in `Z[1/q]`
  and is trivial. So `<z, m>` is isomorphic to `BS(1,q)`.
