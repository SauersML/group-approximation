---
rg: 2
id: fpbs-pointwise-critical-bound-fails-on-spread-products-proof
kind: route
title: Compare with the range-k fibre at 1/(d-1), count layered monotone paths, and bound the second moment by a two-state transfer matrix
target: fpbs-pointwise-critical-bound-fails-on-spread-products
requires:
  - fpbs-hyperbolic-and-nonunimodular-nonuniqueness
artifacts:
  - experiments/pointwise-critical-bound-2026-09-17/layered_lower_bound.py
  - experiments/pointwise-critical-bound-2026-09-17/layered_lower_bound.out
---

Notation is as in the target. Let `X = Cay(H x Z, S_H u {t^(+-1..+-k)})`, where

- `D = |S_H| >= 2`, `1 ∉ S_H`, and `k >= 2` is even with `2k >= D`;
- `d = D + 2k` and `q = 1/(d-1) = 1/(D+2k-1)`.

`X_(r,k)` is the case `H = F_r` with a free basis, `D = 2r`.

Items 1 and 3, and the violation half of item 2, are elementary and self-contained. The strict-threshold half of item 2 imports only Hutchcroft's nonunimodular theorem.

## 1. Geometry of X

The map `(h, t^m) -> (h, m)` identifies `X` with the Cartesian product of `G_H = Cay(H, S_H)` and `Y = Cay(Z, {+-1,...,+-k})`. Each generator moves exactly one coordinate.

- **Word length.** Graph distance in a Cartesian product is the sum of the factor distances, so `|(h,m)| = |h|_(S_H) + d_Y(0,m)`. A step in `Y` moves by at most `k`, and `ceil(|m|/k)` steps of size at most `k` reach `m`. So `d_Y(0,m) = ceil(|m|/k)`, and `|t^(kn)| = n`.
- **Growth.** `|S_n(X)| = sum_(a+b=n) |S_a(G_H)| |S_b(Y)|` with `|S_b(Y)| = 2k` for `b >= 1`. Hence
  `|S_n(G_H)| <= |S_n(X)| <= 2k (n+1) max_(a <= n) |S_a(G_H)|`, and `gr(X) = gr(G_H)`.
  - For the free basis of `F_r`, `gr = 2r-1`.
  - For `S_H = B_L \ {1}` in `F_2`, the ball of radius `n` is the standard ball of radius `Ln`, so `gr = 3^L`.

## 2. Critical point and fibre comparison

- **(a) `p_c(X) >= q`.** There are at most `d(d-1)^(n-1)` self-avoiding paths of length `n` from `o`. For `p < 1/(d-1)` this gives `E_p|K_o| <= 1 + sum_n d(d-1)^(n-1) p^n < infinity`, so `p_c >= 1/(d-1) = q`.
- **(b) Monotonicity.** `p -> tau_p(o,x)` is nondecreasing (standard coupling). Therefore `tau_(p_c)(o, t^m) >= tau_q(o, t^m)`.
- **(c) Subgraph.** The fibre `{(1, j) : j in Z}` with its `t`-edges is a copy of `Y` inside `X`. Connection inside a subgraph implies connection in `X`, and the edge variables of the subgraph are i.i.d. Bernoulli(`q`). Hence

  ```text
  tau^X_(p_c)(o, t^m)  >=  P^Y_q(0 <-> m).
  ```

## 3. Layered paths and the second moment

Fix integers `w, s, m` with

```text
1 <= w <= s,   s + w - 1 <= k,   m >= 2.
```

Define the layers `I_0 = {0}`, `I_i = {is, is+1, ..., is+w-1}` for `1 <= i <= m-1`, and `I_m = {ms}`.
Let `P` be the set of sequences `v = (v_0, ..., v_m)` with `v_i in I_i`. So `|P| = w^(m-1)`.

**Lemma 3.1 (these are paths in Y).**

1. Every hop `v_i - v_(i-1)` lies in `[1, k]`, so `v` is a self-avoiding path in `Y` with `m` distinct edges.
2. The layers are pairwise disjoint and increasing.
3. An edge of `v` can equal an edge of `v'` only if both join `I_(i-1)` to `I_i` for the same `i`, with `v_(i-1) = v'_(i-1)` and `v_i = v'_i`.

*Proof.*

1. For `2 <= i <= m-1` the hop lies in `[s-(w-1), s+(w-1)]`, and that interval sits inside `[1, k]` by the two constraints. The first hop lies in `[s, s+w-1]` and the last in `[s-w+1, s]`, both inside `[1, k]`. All hops are positive, so the vertices strictly increase.
2. `max I_i = is+w-1 < (i+1)s = min I_(i+1)`, because `w <= s`.
3. An edge of `v` joins consecutive layers, and the layers are disjoint, so the pair of layers determines `i`. The endpoints are ordered, so the equality of endpoints follows. QED.

Let `N` be the number of `v in P` all of whose edges are `q`-open. Then

```text
E N = w^(m-1) q^m.
```

For `v, v' in P`, let `A(v,v') = {i : v_i = v'_i}`, which always contains `0` and `m`. Let `e(A) = #{i in [1,m] : i-1 in A and i in A}`.
By Lemma 3.1(3), `|E(v) ∩ E(v')| = e(A)`, so

```text
E N^2 = sum_(v,v') q^(2m - e(A(v,v'))).
```

Fix `v`. The number of `v'` with `A(v,v') ∩ [1,m-1]` equal to a given set `B` of size `b` is `(w-1)^(m-1-b)`: each disagreeing interior layer allows `w-1` choices. This count does not depend on `v`. Hence

```text
E N^2 = (E N) Z_m,     Z_m = sum_(B ⊆ [1,m-1]) (w-1)^(m-1-|B|) q^(m - e(B u {0,m})).
```

By Cauchy–Schwarz, `P(N > 0) >= (E N)^2 / E N^2 = E N / Z_m`.
Since `{N > 0}` is contained in `{0 <-> ms in Y}`,

```text
P^Y_q(0 <-> ms)  >=  E N / Z_m.                                        (3.2)
```

## 4. Transfer matrix

Record, at each site `i`, whether the two paths agree (`a`) or differ (`b`); sites `0` and `m` are always `a`. The factors in `Z_m` are:

- each interior `b` site contributes `w-1`;
- each edge `(i-1, i)` contributes `q` unless both of its sites are `a`, in which case it contributes `1`.

Hence, with `x = (w-1) q`,

```text
Z_m = e_a^T K^(m-1) g,    K = [[1, x], [q, x]]  (rows/columns a, b),    g = (1, q)^T.
```

Row `a` of `K` is `(1, (w-1)q)` and row `b` is `(q, (w-1)q)`. The vector `g` is the weight of the last edge into the forced `a` site `m`.

**Lemma 4.1.** If `x <= 1/2`, then `Z_m <= (1+q)^(m-1)`.

*Proof.* Put `h = (1, 2q)^T`. Then

```text
(Kh)_a = 1 + 2xq  <=  1 + q,
(Kh)_b = q(1 + 2x) <= 2q(1+q),
```

so `Kh <= (1+q) h` entrywise. `K` is nonnegative and `g <= h`, so

```text
Z_m = e_a^T K^(m-1) g  <=  e_a^T K^(m-1) h  <=  (1+q)^(m-1) h_a  =  (1+q)^(m-1).
```

QED.

(The exact top eigenvalue is `lambda_+ < 1 + xq/(1-x)`. The characteristic polynomial `lambda^2 - (1+x)lambda + x(1-q)` evaluates to `(xq/(1-x))^2 > 0` at `1 + xq/(1-x)` and is increasing there. The script computes `Z_m` exactly and does not need the bound.)

## 5. Proof of item 1 (ray bound)

Take `w = s = k/2` and `m = 2n`. Check the hypotheses:

- the constraints hold: `w <= s` and `s + w - 1 = k - 1 <= k`;
- `x = (k/2 - 1) q < (k/2)/(2k) = 1/4`;
- `wq = (k/2)/(D+2k-1) >= (k/2)/(4k) = 1/8`, using `D <= 2k`;
- `q <= 1/5`, since `D >= 2` and `k >= 2`;
- the endpoint is `ms = nk`.

By (3.2) and Lemma 4.1,

```text
P^Y_q(0 <-> nk) >= w^(m-1) q^m (1+q)^(-(m-1)) = q (wq/(1+q))^(2n-1) >= q (5/48)^(2n-1) >= q 100^(-n).
```

The last step uses `(5/48)^2 = 25/2304 > 1/100` and `5/48 < 1`. Section 2 then gives

```text
tau^X_(p_c)(o, t^(kn)) >= 100^(-n)/(D+2k-1),   and   |t^(kn)| = n.
```

The script's `check_clean_bound` verifies both inequalities of this chain, and `Z_m <= (1+q)^(m-1)`, in exact arithmetic on a grid of `(D, k, n)`. QED.

## 6. Proof of items 2 and 3 (no universal pointwise bound)

Let `alpha > 0` and `C < infinity`. Choose `r` with `(2r-1)^alpha > 100`, and any even `k >= r`. Then `D = 2r <= 2k`, and item 1 gives

```text
tau_(p_c)(o, t^(kn)) / (C gr^(-alpha n))  >=  ((2r-1)^alpha / 100)^n / (C(2r+2k-1))  ->  infinity.
```

So the bound fails for all large `n`, and the same argument absorbs any `e^(o(n))` correction.

For item 3, take `H = F_2`, `S_H = B_L \ {1}`, `D = |B_L| - 1 = 2*3^L - 2`, and even `k >= D/2`. Item 1 gives

```text
limsup_n -(1/n) log tau_(p_c)(o, t^(kn)) <= log 100,
```

while `log gr = L log 3` by Section 1. All of these are Cayley graphs of `F_2 x Z`.

**Exact finite instances.** For a certificate at small `|x|`, (3.2) is evaluated exactly with `Fraction` arithmetic. The script `layered_lower_bound.py` computes `E N` and `Z_m` exactly and checks

```text
(E N / Z_m)^j * gr^(ceil(ms/k)) > 1,
```

that is, `tau_(p_c)(o, t^(ms)) > gr^(-|x|/j)`. The output file records:

| r | k | w | s | m | alpha | abs x | log10 LB | log10 bound | violation |
|---|---|---|---|---|---|---|---|---|---|
| 120 | 20000 | 8000 | 12001 | 60 | 1/2 | 37 | -46.00 | -44.00 | no |
| 150 | 20000 | 8000 | 12000 | 100 | 1/2 | 60 | -74.12 | -74.27 | yes |
| 500 | 10000 | 4000 | 6001 | 40 | 1/2 | 25 | -32.41 | -37.49 | yes |
| 500 | 10000 | 4000 | 6001 | 60 | 1/2 | 37 | -46.81 | -55.49 | yes |
| 2000 | 100000 | 40000 | 60001 | 30 | 1/2 | 19 | -25.83 | -34.22 | yes |
| 100000 | 2000000 | 700000 | 1300000 | 80 | 1/4 | 52 | -68.10 | -68.91 | yes |

The first row is a recorded near miss. Its per-layer margin `log(wq) + (s/2k) log gr` is positive (about 0.028), but at `m = 60` it does not beat the prefactor loss from `E N = q (wq)^(m-1)`.

**Optimised rate (remark, not used).** With `w = uk`, `s = k - w + 1` and `r/k -> 0`, the per-layer margin is

```text
log(u/2) + ((1-u)/2) log(2r-1).
```

This is positive at `u = 0.4` once `r >= 107` or so. The ray rate tends to `min_u (1/(1-u)) log(2/u)`, about `log 14.6`.

## 7. Strict thresholds on X_(r,k) (second half of item 2)

`X_(r,k)` is the Cartesian product `T x Y` of the `2r`-regular tree with the vertex-transitive graph `Y`.

- Let `Aut_xi(T)` be the stabiliser of an end `xi` of `T`. It acts transitively on `T`, and it is nonunimodular for `2r >= 3`: its modular function is `(2r-1)^(Busemann shift)`.
- The group `Aut_xi(T) x Z`, with `Z` acting by translations on `Y`, acts on `T x Y` by automorphisms. It is transitive and closed. It is nonunimodular, because the modular function of a product is the product of the modular functions.

Hence `p_c(X) < p_u(X)` by Hutchcroft, arXiv:1711.02590, as recorded in `fpbs-hyperbolic-and-nonunimodular-nonuniqueness`, item 2. That node states this case verbatim: "This covers `T_k x Z^d`, a `k`-regular tree times a Euclidean lattice." The same argument applies with `Y` in place of `Z^d`. It is also the "tree factor with a free basis" case recorded in the Attempts of `fpbs-product-every-generating-set`. QED.

## 8. Where the heuristic came from, and what breaks

The false pointwise heuristic comes from `T_d`, where `tau_(p_c)(o,x) = (d-1)^(-|x|) = gr^(-|x|)`.

The spread generators break it. Along the `t`-ray, word length counts one unit per `k` fibre steps, but a fibre path needs only about two hops per unit, each with probability about `1/(2k)`. It has about `k/2` choices per hop, and the second moment shows these choices behave independently: `Z_m = 1 + O(m/k)`.

So the probability cost per unit of word length is an absolute constant, while `gr = 2r-1` is free. Hutchcroft's argument bounds only the infimum `kappa`. The infimum can be realised in directions where `tau` is small, such as the tree directions, without saying anything about the `t`-ray.

Any pointwise decay rate at `p_c` must therefore depend on the generating set beyond `gr`, as it does through `p_c < p_(2->2)` and exponential decay below `p_(2->2)`. It cannot be a function of `gr` alone.
