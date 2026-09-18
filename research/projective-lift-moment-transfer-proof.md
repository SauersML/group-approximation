---
rg: 2
id: projective-lift-moment-transfer-proof
kind: route
title: Lifted colourings, a power count, Jensen and Chebyshev give the projective moment transfer and its kill of bounded-map amplification
target: projective-alphabet-lifts-cannot-amplify-pairing-moments
requires: []
artifacts:
  - experiments/projective-amplification-2026-09-17/check_projective_lift_moments.py
  - research/artifacts/unique-games-finite-density-moments-2026-09-12.md
---

Notation is that of the target claim. For a law `nu` on matchings (partial
matchings allowed) of a point set `P` of even size, write
`D(x) = m^(|P|/2) Pr[x constant on every pair]` for `x in [m]^P`, and
`||1_A D||_q^q = m^(-|P|) sum_(x in A) D(x)^q`. For full perfect matchings
this is the density of the pull-back law, as in artifact equation (2).

## Step 0 (projective soundness implies compatibility)

Suppose an output 2-to-1 constraint `phi' : Sigma' -> [n']` has kernel
`lambda`, an input constraint `phi : Sigma -> [n]` has kernel `pi`, and some
right-label map `p'` satisfies `p' o phi' = phi o p`. If `{x,y}` is in
`lambda` then `phi(p(x)) = phi(p(y))`, so `p(x) = p(y)` or
`{p(x), p(y)}` is in `pi`. Since `p` maps into `S`, that pair lies in
`pi|_S`, the set of pairs of `pi` with both ends in `S`. This is (K).

## Step 1 (pointwise lifted domination)

Fix `i`, with map `p = p_i`, image `S`, `s = |S|`, and surplus `g = 2n' - s`.
Let `z in [m]^S` be constant on every pair of `pi|_S`. For every pair `{x,y}`
of a compatible `lambda`, either `p(x) = p(y)`, or `{p(x),p(y)}` lies in
`pi|_S`. In both cases `z(p(x)) = z(p(y))`. So `z o p` is constant on
`lambda`. Keeping only the `i`-th mixture component gives

```text
D'(z o p) = m^(n') Pr[z o p const on lambda]
          >= m^(n') w_i Pr[z const on pi|_S | i]
          =  m^(n' - s/2) w_i D_(S,i)(z).                        (1)
```

## Step 2 (distinct lifts and the power count)

The map `p` is onto `S`, so `z -> z o p` is injective. By definition `z` lies
in `E''_i` exactly when `z o p` lies in `E'`. Hence

```text
||1_(E') D'||_q^q  >= m^(-2n') sum_(z in E''_i) D'(z o p)^q
                   >= w_i^q m^(-2n' + q n' - q s/2 + s) ||1_(E''_i) D_(S,i)||_q^q.
```

The exponent is `(q-2) n' - (q-2) s/2 = (q-2) g/2`. This proves the transfer
inequality (T). No convexity or independence is used.

## Step 3 (Jensen and the lifted balance probability)

Since `q >= 1`, `||1_A D||_q >= ||1_A D||_1 = E_U[1_A D]`. Fix a partial
matching `pi|_S` with `c` pairs. It has `m^(s-c)` constant colourings, and a
`theta_pi` fraction of them lift into `E'`. So

```text
E_U[1_(E''_i) D_(S,i)] = m^(s/2 - s) E_pi[ m^(s-c) theta_pi ]
                       = E_pi[ m^(s/2 - c) theta_pi ] >= theta_(*,i),
```

because `c <= s/2`. With (T) this gives (T1).

For the Chebyshev bound, take `z` uniform among the colourings constant on
`pi|_S`. Each super-block `B` (the fibre of one point of `S` unmatched in
`pi|_S`, or the union of the fibres of a pair of `pi|_S`) receives one
independent uniform colour. For a colour `c`, the count of `c` in `z o p` is
`sum_B |B| 1[colour_B = c]`. Its mean is `2n'/m`, and its variance is
`sum_B |B|^2 (1/m)(1 - 1/m) <= 2n' R / m`. Chebyshev and a union bound over
the `m` colours show that `z o p` leaves `W_kappa` with probability at most
`R/kappa^2`. Since `E'` contains `W_kappa`, we get
`theta_* >= 1 - R/kappa^2`.

The same computation for an arbitrary output law uses pairs of weight 2. The
variance is at most `4n'/m`, so `nu_(mu',m)(E') >= 1 - 2/kappa^2`.

## Step 4 (support count)

Compatibility depends only on `(p, pi|_S)`. It says that every pair of
`lambda` lies inside one super-block. So the compatible matchings are the
products of perfect matchings of the super-blocks, and there are
`prod_B (|B| - 1)!!` of them. The product is zero if some block is odd.

Let `c_B` be 1 or 2, the number of points of `S` under `B`. Then
`sum_B c_B = s` and `sum_B (|B| - c_B) = g`. For each block
`(|B| - 1)!! <= (2n')^(|B|/2)`, and `|B|/2 <= 3(|B| - c_B)/2` whenever `B` is
not a two-point block over a matched pair. A two-point block over a matched
pair contributes the factor 1. Multiplying over blocks gives the bound
`(2n')^(3g/2)`. Summing over the distinct `pi|_S` of map `i` and then over
`i` gives (S).

## Step 5 (the kill)

Assume `||1_(E') D'||_q <= C`, `q >= 3`, `kappa^2 >= 2R` and `kappa^2 >= 4`,
so that `theta_* >= 1/2` and `nu(E') >= 1/2` for every law.

(K1) By (T1), `C >= w_i (1/2) m^((q-2) g_i/(2q))`.

(K2) Fix `G >= 0`. The maps with `g_i > G` have total weight below
`2Ck m^(-(q-2)G/(2q))`. If this is at most `1/2`, the maps with `g_i <= G`
carry weight `W >= 1/2`. Their normalized sub-mixture `mu_s` has density
`D_s` with `W D_s <= D'` pointwise, so `||1_(E') D_s||_q <= 2C`. By Hölder
on the support `T` of `nu_(mu_s,m)`,

```text
1/2 <= nu_(mu_s,m)(E') = E_U[1_(E' cap T) D_s] <= 2C U(T)^(1 - 1/q),
```

and `U(T) <= |supp mu_s| m^(-n')`. So
`|supp mu_s| >= (4C)^(-q/(q-1)) m^(n')`. Step 4 bounds
`|supp mu_s| <= k S_in (2n')^(3G/2)`. This proves (K2).

(K3) Put `G = n'/(3 log_m(2n'))`, so that `(2n')^(3G/2) = m^(n'/2)`, and
substitute into (K2).

(K4) This is (T) with `m^((q-2) g_i/2) >= 1`.

## Regression checks

`experiments/projective-amplification-2026-09-17/check_projective_lift_moments.py`
makes exact rational comparisons of (T) and (T1). The random cases use
`m` in {2, 3}, up to 8 output points, one or two maps, partial `pi`, and
`E'` equal to all colourings, a count window, or a random subset. The script
also checks the count `prod (|B|-1)!!` and the bound (S) by enumeration.
Finally it evaluates the doubling lift of the fully rich law exactly through
a closed form, which it cross-checks by enumeration. Runtime is about 2.5 s,
and it prints `ALL CHECKS PASSED`. These runs are regression checks only;
Steps 0 to 5 are the proof.
