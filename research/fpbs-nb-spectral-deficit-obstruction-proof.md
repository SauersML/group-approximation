---
rg: 2
id: fpbs-nb-spectral-deficit-obstruction-proof
kind: route
title: Nonbacktracking majorant plus Harris excludes uniqueness below 1/sigma, a derivative bound compares deficits, and Cauchy-Schwarz on cosets bounds the norm by the quotient
target: fpbs-nb-spectral-deficit-obstruction
requires:
  - fpbs-ew-nb-majorant
---

Notation as in the target.

## Step 1: `p_u >= 1/sigma(Lambda)`

`fpbs-ew-nb-majorant` (Section 5 of its artifact) applies to any infinite
`d`-regular simple graph and any `D >= max(||A||, 2 sqrt b)`. It gives
`||T_p||_{2->2} <= (1-p^2)/(1 - D p + b p^2) < infinity` for `p < 1/sigma(D)`.

A Cayley graph with `e ∉ S` is simple and `d`-regular. Suppose there is a
unique infinite cluster at `p`. By Harris,
`T_p(x,y) >= P(x, y ∈ I) >= theta(p)^2`. For finite `F`,
`<1_F, T_p 1_F> >= theta(p)^2 |F|^2`, so `||T_p|| >= theta(p)^2 |F|`, which is
unbounded. Hence `p` is not a uniqueness parameter for any `p < 1/sigma(D)`, and
`p_u >= 1/sigma(D)`.

Take `D = Lambda_G`, or any larger admissible bound; `sigma` is increasing on
`[2 sqrt b, infinity)`. If `D(G) < Delta(G)` then `1/p_c > sigma(Lambda_G)`, so
`p_c < 1/sigma(Lambda_G) <= p_u`.

## Step 2: comparing the deficits

For `x > 2 sqrt b`, `sigma'(x) = (1 + x/sqrt(x^2-4b))/2`, and
`x/sqrt(x^2-4b)` is decreasing in `x`. At `x = d`,
`sqrt(d^2 - 4(d-1)) = d-2`, so `sigma(d) = d-1` and `sigma'(d) = (d-1)/(d-2)`.

Hence for `2 sqrt b <= x <= d`:

```text
sigma(d) - sigma(x) = ∫_x^d sigma' >= (d-x)(d-1)/(d-2).
```

This gives `Delta >= (d - ||A||)(d-1)/(d-2)` when `||A|| >= 2 sqrt b`. Also
`sigma(x) < d-1` iff `x < d`.

Remark: `D(G) >= 0`, because `p_c >= 1/(d-1)` by counting self-avoiding paths
(at most `d(d-1)^(n-1)` of length `n`).

## Step 3: quotient norm (Theorem 2)

`A` has a nonnegative kernel, so `||A|| = sup ⟨g, A f⟩` over nonnegative unit
`f, g`. Cosets are `q = xN`. Since `N` is normal, `x ∈ q` implies
`xs ∈ q pi(s)`, and `x -> xs` is a bijection `q -> q pi(s)`.

Put `F(q) = (sum_{x ∈ q} f(x)^2)^(1/2)`, and define `G(q)` from `g` in the same
way. By Cauchy–Schwarz on each coset,

```text
⟨g, A f⟩ = sum_{s ∈ S} sum_q sum_{x ∈ q} g(x) f(xs)
        <= sum_{s} sum_q G(q) F(q pi(s)) = ⟨G, A_X F⟩ <= ||A_X|| ||g|| ||f||.
```

## Step 4: Corollary 3

Take `N = B`. Then `X` is `Cay(H,S_H)` with `d_B` loops at every vertex, so
`A_X = A_H + d_B I`. Since `A_H` is self-adjoint with nonnegative kernel,
`sup spec A_H = ||A_H||`, so `||A_X|| = d_B + ||A_H||`.

**Case `Lambda = d_B + ||A_H|| >= 2 sqrt b`.** Step 2 gives
`Delta >= (d_H - ||A_H||)(d-1)/(d-2)`.

**Otherwise.** `Delta = d-1-sqrt(d-1)`. Also `||A_H||^2 >= ⟨delta_e, A_H^2 delta_e⟩ = d_H`.
With `g(x) = x - sqrt x`, which is increasing for `x >= 1`, and
`d_H <= d-1` (since `d_B >= 1`):

```text
d_H - ||A_H|| <= g(d_H) <= g(d-1) = Delta.
```

Then apply Step 1 in contrapositive form.

## Step 5: Corollary 4

**The tree subgraph.** If a nontrivial reduced word in the `s_i` were trivial,
its image under `phi` would be a nontrivial reduced word in the basis, a
contradiction. So the `s_i` freely generate a free group `F`. The subgraph of
`G` on the vertex set `F` with the `s_i^±1` edges is the `2m`-regular tree.
By monotonicity in subgraphs, `p_c(G) <= p_c(T_{2m}) = 1/(2m-1)`.

**The quotient norm.** With `N = ker phi`, `X` is the standard tree of `F_m`
with `j` loops at each vertex. So `||A_X|| = 2 sqrt(2m-1) + j`.

**The comparison.** Put `b = 2m+j-1` and `y0 = 2m-1`. For `y >= sqrt b`, the
map `y -> y + b/y` is increasing and inverts `sigma`, so
`sigma(Lambda) < y0` iff `y0 + b/y0 > Lambda`. Here `y0 >= sqrt b`, because
`(2m-1)^2 >= 2m+j-1` in the stated range. If `Lambda < 2 sqrt b`, then
`sigma = sqrt b < y0` directly.

Now `y0 + b/y0 = 2m + j/(2m-1)`. The inequality `2m + j/(2m-1) > 2 sqrt(2m-1) + j`
is `j(2m-2)/(2m-1) < 2m - 2 sqrt(2m-1)`, which is the hypothesis. So
`p_c <= 1/(2m-1) < 1/sigma <= p_u`.

**The Benjamini–Schramm version.** Using `p_u >= 1/Lambda` needs
`2m-1 > 2 sqrt(2m-1) + j`. The difference of the two `j`-ranges is
`1 + (2m - 2 sqrt(2m-1))/(2m-2) > 1`.

Numerics:

| `m` | new range | BS range |
|---|---|---|
| 4 | `j < 3.16` | `j < 1.71` |
| 5 | `j < 4.5` | `j < 3` |

## Step 6: the example `Z^2 ⋊ F_5`

`phi` is the quotient by `Z^2`, and `e_1^±1, e_2^±1 ∈ ker phi`, so `j = 4`. The
group is torsion-free and the elements of `S` are distinct and nontrivial. The
listed group properties are standard:

* an infinite amenable normal subgroup excludes acylindrical hyperbolicity;
* `Z^2` excludes hyperbolicity;
* Gaboriau's criterion for an infinite amenable normal subgroup gives fixed
  price one.
