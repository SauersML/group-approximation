---
rg: 2
id: stacked-models-doubling-tower-proof
kind: route
title: Proof that stacked phi-twisted LEF towers are sofic models of the mapping torus whose Kazhdan frames double at every interior layer under a surviving defect generator
target: stacked-models-force-lef-witnesses-into-doubling-towers
requires:
  - twisted-lef-tower-order-budget-kills-compression-defects
  - kazhdan-marked-limits-eventually-uniform-expanders
  - bounded-cluster-period-preserves-kazhdan-fixed-algebras
artifacts:
  - research/twisted-lef-tower-order-budget-proof.md
  - experiments/stacked-doubling-2026-09-17/stack_check.py
---

Notation is as in the target. Throughout, `0 <= m < P` indexes levels, and `|a| < P`.

## Imports

**(I1)** From `twisted-lef-tower-order-budget-proof` (the route of the ESTABLISHED
`twisted-lef-tower-order-budget-kills-compression-defects`), Sections 2, 3 and 5, verbatim:

> Call `m` *good* if `rho_m` is a local embedding on `B_0`.

> Two identities hold exactly, for all `m` and all `g` in `K`, straight from the definition:
> `rho_m(g) = rho_(m+a)(phi^a(g)),   rho_m(g) = rho_(m+b)(phi^b(g)).   (SH)`

> Let `m + a` be good. Put `x = rho_(m+a)(k)` and `c_x(y) = x y x^-1`. [...] In particular
> `c_x(Pi_m) <= Pi_(m+a)`.

> **Lagrange step.** `c_x(Pi_m)` is a subgroup of `Pi_(m+a)` of order `|Pi_m|`. So either
> `|Pi_(m+a)| = |Pi_m|` and `c_x(Pi_m) = Pi_(m+a)`, or `|Pi_(m+a)| >= 2 |Pi_m|`.

> **Lemma.** Suppose `m + a`, `m + b` and `m + a + b` are good, and `|Pi_m| = |Pi_(m+a)|`.
> Then (GOAL) holds for every `l` in `S_L`.

Here (GOAL) is `k' phi^b(g_l) k'^-1 = g_l`, which is equivalent to `[s z s^-1, l] = 1`
(Section 1 of that route). The set `B_0 = B_0(s, z, S_L)` is the one defined there.

**(I2)** From `kazhdan-marked-limits-eventually-uniform-expanders` (ESTABLISHED), verbatim:

> Let `G` have property (T) with finite generating set `T`. There are `κ > 0` and a finite set
> `R_0` of relators such that, if `(Q_k, T_k) → (G, T)` in the space of marked groups with
> `Q_k` finite, then for all large `k`: [...] the normalized adjacency operator of
> `Cay(Q_k, T_k)` has spectrum in `[−1, 1 − κ^2/(2|T^±|)]` on `ℓ^2_0(Q_k)`.

**(I3)** From `bounded-cluster-period-preserves-kazhdan-fixed-algebras`: the definitions of
cluster frame, dominant target `pi(i)`, loss `ell(i) = |Q_i| - |u Q_i ∩ Q_(pi i)|` and
`lambda = sum_i ell(i) / |Y|`, and item 5, which rests on Kun--Thom Lemma 2.3:
`D_U^(sigma(L)) = prod_U D(Q_n)` for every cluster frame.

## 1. Soficity

Every `g ∈ G` is uniquely `g = k t^j`, so `sigma_T(g)` is well defined. It is a bijection of
`Y`: it permutes the levels by `m -> m + j mod P`, and on each level it is a left
multiplication in `F`. Also `sigma_T(1) = id`, because `iota(1) = iota(1) iota(1)` forces
`iota(1) = 1`.

*Multiplicativity.* Take `g = k t^j` and `g' = k' t^(j')`, so `g g' = k phi^j(k') t^(j+j')`.
Fix `(m, f)`. Put `m' = (m + j') mod P`, and suppose `m' + j ∈ [0, P)`. Put `m'' = m' + j`,
which is `(m + j + j') mod P`. Then:

```text
sigma(g) sigma(g') (m, f) = ( m'', rho_(m'')(k) rho_(m')(k') f ),
sigma(g g') (m, f)        = ( m'', rho_(m'')(k phi^j(k')) f ).
```

By definition `rho_(m')(k') = iota(phi^(-m')(k')) = iota(phi^(-m'')(phi^j(k')))
= rho_(m'')(phi^j(k'))`. Now `k`, `phi^j(k')` and `k phi^j(k')` lie in `B`. So
`phi^(-m'')` maps them into `phi^(-m'')(B)`, where `iota` is multiplicative. Hence the two
right sides agree.

The condition `m' + j ∈ [0, P)` fails for at most `|j|` values of `m'`. Since `m -> m'` is a
bijection of the levels, it fails for at most `|j|` levels `m`. So the two maps differ on at
most a `|j|/P` fraction of `Y`. This fraction tends to `0` as `P_n -> infinity`, once
`B_n` contains the three elements, which happens for large `n` since `B_n` increases to `K`.

*Freeness.* Let `g = k t^j != 1`.
- If `0 < |j| < P`, then `sigma(g)` moves every level, so it has no fixed point.
- If `j = 0`, then `k != 1`. Since `iota` is injective on `phi^(-m)(B)`, which contains
  `phi^(-m)(k)` and `phi^(-m)(1)`, we get `rho_m(k) != rho_m(1) = 1`. So left multiplication
  by `rho_m(k)` has no fixed point.

Hence for every `g != 1`, the fraction of fixed points of `sigma_(T_n)(g)` is eventually `0`.
The sequence `(sigma_(T_n))` is therefore a sofic approximation. Its ultraproduct is a
homomorphism `G -> S_U` with trace zero off the identity. □

## 2. The stacked frame (item 2)

Since `B ⊇ B_0` and `iota` is a local embedding on every `phi^(-m)(B)`, it is one on every
`phi^(-m)(B_0)`. So every level `m ∈ [0, P)` is good in the sense of (I1).

*Cells are invariant.* For `l ∈ S_L`, `sigma_T(l)(m, f) = (m, rho_m(l) f)`. This preserves
each right coset `Pi_m f`. The map `f' -> f' f^-1` identifies the generator graph of
`sigma_T|_(S_L)` on `{m} × Pi_m f` with `Cay(Pi_m, rho_m(S_L))`, the Cayley graph for left
multiplication, with its edge multiset indexed by `S_L`. No edge leaves a cell, so no edit is
needed.

*Cheeger bound.* Let `B` contain the word ball `Ball_r` of radius `r` of `(L, S_L)`. Take a
word `w` in `S_L` of length at most `r`. Its prefix values lie in `Ball_r ⊆ B`, and `rho_m`
is multiplicative on `B` (if `x, y, xy ∈ B`, then `rho_m(x) rho_m(y) = rho_m(xy)`). So
induction on prefixes gives `w(rho_m(S_L)) = rho_m(w(S_L))`. By injectivity of `rho_m` on `B`,
`w(rho_m(S_L)) = 1` if and only if `w(S_L) = 1` in `L`.

So the marked groups `(Pi_m, rho_m(S_L))` agree with `(L, S_L)` on all relations of length
`<= r`. Enumerate the pairs `(n, m)`, `0 <= m < P_n`, in increasing order of `n`. If
`r_n -> infinity`, this sequence converges to `(L, S_L)` in the space of marked groups.
- By (I2), all but finitely many terms have spectral gap at least `κ^2/(2|S_L|)` on
  `ℓ^2_0(Pi_m)` for the normalized adjacency operator.
- By the easy half of the discrete Cheeger inequality, each of these `|S_L|`-regular graphs
  has edge expansion at least `h = κ^2/4`.

Since each `n` has finitely many `m`, this bound holds for all `m` once `n` is large. So
`Q(T_n)` is a cluster frame in the sense of (I3).

*Compressor step.* Let `m + a ∈ [0, P)`. Then `sigma_T(s)(m, f') = (m + a, x f')` with
`x = rho_(m+a)(k)`. The image of the cell `{m} × Pi_m f` is

```text
{m + a} × x Pi_m f  =  {m + a} × c_x(Pi_m) x f  ⊆  {m + a} × Pi_(m+a) x f,
```

by (I1), since `m + a` is good. So the cell maps into one cell. That cell is its dominant
target, and its loss is `0`. The size ratio is `|Pi_(m+a)| / |Pi_m| = [Pi_(m+a) : c_x(Pi_m)]`,
since `|c_x(Pi_m)| = |Pi_m|`. By the Lagrange step of (I1), this ratio is `1` or `>= 2`.

*Loss.* Only the `|a|` wrap levels (`m + a ∉ [0, P)`) can carry loss, and a cell loses at
most its size. So `sum_i ell(i) <= |a| |F|`, and `lambda(T) <= |a| |F| / (P |F|) = |a| / P`.
With `|Y| = P |F|`, this gives (UP). □

## 3. Strict doubling (item 3)

Let `m ∈ J`. The levels `m + a`, `m + b` and `m + a + b` lie in `[0, P)`, so they are good.
If `|Pi_(m+a)| = |Pi_m|`, then the Lemma of (I1) gives (GOAL) for every `l ∈ S_L`. That is
`[s z s^-1, l] = 1` for all `l ∈ S_L`, hence for all `l ∈ L`, contrary to hypothesis. So by
the Lagrange step, `|Pi_(m+a)| >= 2 |Pi_m|`.

By Section 2, each cell at level `m` maps into one cell at level `m + a`, of size
`|Pi_(m+a)| >= 2 |Pi_m|`.

For the count of `J`: `m` fails to lie in `J` only if one of `m + a`, `m + b` or `m + a + b`
leaves `[0, P)`. Each condition excludes at most `|a|`, `|b|` and `|a| + |b|` levels
respectively. So `|J| >= P - 2(|a| + |b|)`. □

## 4. The lower bound (item 4)

Put `phi(y) = log |Q(y)|`, where `Q(y)` is the cell of `y`, and write `u = sigma_T(s)`. Since
`u` is a bijection of `Y`,

```text
sum_(y in Y) ( phi(u y) - phi(y) )  =  0.                                   (CONS)
```

Let `W` be the set of points on the `|a|` wrap levels, so `|W| = |a| |F|`. By Sections 2 and 3:
- for `y ∉ W`, `phi(u y) >= phi(y)`;
- for `y` on a level of `J`, `phi(u y) >= phi(y) + log 2`.

Put `Delta(y) = phi(y) - phi(u y)`. Then (CONS) gives

```text
sum_(y in W) Delta(y)  >=  |J| |F| log 2.                                   (1)
```

Each `Delta(y) <= phi(y) <= log |F|`, since `phi >= 0`.

*Budget.* Bounding the left side of (1) by `|W| log |F|` gives `|J| log 2 <= |a| log |F|`,
hence `P <= |a| log_2 |F| + 2(|a| + |b|)`.

*Loss.* Fix `D > 0` and put `A = {y ∈ W : Delta(y) >= D}`. Then
`sum_W Delta <= |A| log |F| + |W| D`, and by (1)

```text
|A|  >=  ( |J| log 2 - |a| D ) |F| / log |F|.                                (2)
```

Here `|F| >= 2`, because `J` is nonempty for large `P` and strict doubling needs `|F| >= 2`.

Let `Q_i` be a wrap cell and `A_i = A ∩ Q_i`. Every point of `u A_i` lies in a cell of size
at most `e^(-D) |Q_i|`. Take any cell `Q_j`:
- if `|Q_j| <= e^(-D) |Q_i|`, then `|u Q_i ∩ Q_j| <= e^(-D) |Q_i|`;
- otherwise `Q_j` misses `u A_i`, so `|u Q_i ∩ Q_j| <= |Q_i| - |A_i|`.

Hence

```text
ell(i)  >=  min( (1 - e^(-D)) |Q_i| , |A_i| )  >=  (1 - e^(-D)) |A_i|.
```

Summing over the wrap cells and using (2),

```text
lambda(T) log |F|  =  (log |F| / (P |F|)) · sum_i ell(i)
                   >= (1 - e^(-D)) ( |J| log 2 - |a| D ) / P,
```

which is (LOW). With `D = log P` and `|J| >= P - 2(|a| + |b|)`,

```text
lambda(T) log |Y|  >=  lambda(T) log |F|
                   >=  (1 - 1/P) ( log 2 - (2(|a| + |b|) log 2 + |a| log P) / P ),
```

and the right side tends to `log 2`. □

## 5. The fixed algebra moves (item 5)

Let `m ∈ J`. Then `u` maps level `m` bijectively onto level `m + a`, and no other level maps
there. Take a cell `C = {m + a} × Pi_(m+a) y`. It is the disjoint union of the
`r = [Pi_(m+a) : c_x(Pi_m)] >= 2` cosets of `c_x(Pi_m)` that it contains, each of size
`|Pi_m|`. Each such coset `c_x(Pi_m) y' = x Pi_m (x^-1 y')` is the image under `u` of the
level-`m` cell `{m} × Pi_m x^-1 y'`.

Let `g ∈ D(Q(T))` take independent uniform signs `±1` on the cells. Put
`h = g o u^-1`, which is the multiplication operator `u g u^-1`. On `C`, `h` carries `r`
independent signs on `r` parts of size `|Pi_m|`. If `p` of these signs are `+1`, then

```text
min_(c ∈ R) sum_(y ∈ C) |h(y) - c|  =  2 |Pi_m| min(p, r - p).
```

The minimum over real `c` is attained at `c = ±1`, because the sum is piecewise linear in `c`.

For `p ~ Bin(r, 1/2)` and `r >= 2`, `E min(p, r - p) >= r/4`:
- `r = 2` gives `1/2`, and `r = 3` gives `3/4`;
- for `r >= 4`, `E min = r/2 - E|p - r/2| >= r/2 - sqrt(r)/2 >= r/4`.

So the expected distance from `h|_C` to the constants is at least `|C|/2`.

The distance from `h` to `D(Q(T))` is the sum of these distances over all cells. The cells at
the levels `m + a`, `m ∈ J`, have total size `|J| |F|`. Hence the expected normalized
`ℓ^1`-distance is at least `|J| |F| / (2 P |F|) = |J| / (2P)`, and some `g` attains this.

*Ultraproduct.* Choose such `g_n` for `T_n`, and put `g = [g_n] ∈ prod_U D(Q(T_n))`. For any
`d = [d_n]` in that algebra,

```text
|| sigma(s) g sigma(s)^-1 - d ||_1  =  lim_U || h_n - d_n ||_1 / |Y_n|
                                    >=  lim_U |J_n| / (2 P_n)  =  1/2.
```

So `Ad sigma(s)` does not preserve `prod_U D(Q(T_n))`. By Section 2 the `Q(T_n)` form a
cluster frame, so by (I3) this algebra is `D_U^(sigma(L))`. Restricting `sigma` to `<L, s>`
changes neither side. □

## 6. The consequence for LEF kernels

Let `K` be LEF. For every finite `B` and every `P`, the set `union_(m < P) phi^(-m)(B)` is
finite. So some `iota : K -> F` is a local embedding on that union, hence on each translate.
Therefore towers with `P_n -> infinity` and `B_n` increasing to `K` exist, and item 1 applies.

Suppose `[s z s^-1, l] != 1`. Then `B_n ⊇ B_0` and `B_n ⊇ Ball_(r_n)` with `r_n -> infinity`
for large `n`, and Section 5 shows that `sigma(s)` moves the fixed algebra. Contrapositively,
fixed-algebra invariance for `sigma(s)` in these stacked representations forces
`[s z s^-1, l] = 1` for all `z` and `l`.

By Section 0 of `twisted-lef-tower-order-budget-proof` (`s^-1 C s <= C` always), if this
holds for every compressor `s`, then `D_G(L) = 1`. □

## Sanity check

`experiments/stacked-doubling-2026-09-17/stack_check.py` builds the model with
`F = (Z/2)^N`, `Pi_m = (Z/2)^m` and `a = 1`, by explicit permutations. It computes the
frame loss exactly, and checks that `lambda log |F| = N log 2 / (N + 1) · (1 - 2^-N)`. This
tends to `log 2`, so (LOW) is attained up to lower-order terms.
