# The flat-rate point exceeds the l2 point on free products of Z/2's and Z/3's

swarm-0917-w9-w9-bs-break, 2026-09-18. This note refutes
`fpbs-flat-rate-point-equals-l2-point`.

Scripts are in `experiments/fpbs-green-weighted-flat-rate-2026-09-17/`:

- `free_product_thresholds.py` (floating point), with output in
  `free_product_thresholds.out`;
- `certify_a_ne_b.py` (exact rationals), with output in `certify_a_ne_b.out`.

## 0. Result

Let `k >= 1` and `m >= 1`, with `(k,m) != (1,1)`. Put

```text
Gamma_{k,m} = (Z/2)^{*k} * (Z/3)^{*m},
S = {x_1,...,x_k} ∪ {r_1^{±1},...,r_m^{±1}},   d = |S| = k + 2m,
```

and let `G = Cay(Gamma_{k,m}, S)`. Use the notation of the target claim:

- `a_n(p) = E tau_p(o,X_n)`;
- `lambda(p) = lim a_n(p)^(1/n)`;
- `p_* = sup{p : lambda(p) = rho}`;
- `p_2 = sup{p : sum_x tau_p(o,x)^2 < infinity}`.

**Theorem.**

1. (Section 3.) `p_* = p_G`, where `p_G` is the unique root in `(0,1]` of
   `Phi(a(R) p, 2F(R) q(p)) = 1`, or `1` if there is no root. The notation is
   defined in Section 1.
2. (Section 5.) `p_* >= p_2`, with equality if and only if `A = B`. Here
   `A = (log a(R)^2, log 2F(R)^2)` and `B = (log p_2^2, log 2q(p_2)^2)`.
3. (Section 6.) `A != B` for `(k,m) = (2,1), (3,1), (1,2), (2,2), (4,1)`, by
   an exact rational certificate. So `p_* > p_2` on these five graphs, and the
   claim `p_* = p_2` fails on every one of them.

The smallest case is `Z/2 * Z/2 * Z/3` of degree 4. Its values, in floating
point and not certified, are:

- `p_c = 0.360461`;
- `p_2 = 0.5736456`;
- `p_* = p_G = 0.5737271`.

So `p_* - p_2 ≈ 8.1e-5`.

Part 1 needs no numerics at all, and the strictness in part 2 is proved by
convexity. The only computer input is the exact certificate `A != B`, which
has a wide margin: the two values of `z` it compares differ by `0.059`.

## 1. Notation and block structure

### Group and graph

Every `x` in `Gamma` has a unique normal form `x = h_1 ... h_L`, by the normal
form theorem for free products. Each letter `h_i` is a nontrivial element of
one factor, and consecutive letters lie in different factors.

In `G`:

- the cosets of `<x_i>` span `K_2` blocks;
- the cosets of `<r_j>` span `K_3` blocks (triangles);
- `G` is a block graph whose block-cut tree is the Bass–Serre tree.

The prefixes `g_i = h_1...h_i` are cut vertices that separate `o = e` from
`x`.

### Two-point function

A simple path between two vertices of a block cannot leave the block. If it
left at `v` and came back at `w != v`, the block would not be a maximal
2-connected subgraph, and it cannot come back at `v` because the path is
simple. So:

- `{o <-> x}` is the intersection of the events `{g_{i-1} <-> g_i` inside
  block `i}`;
- these events use disjoint edge sets and are independent;
- `tau_p(o,x) = prod_i t(h_i)`, where `t(x_i) = p` and
  `t(r_j^{±1}) = q(p) := p + (1-p) p^2`.

`q` is the `K_3` two-point function. Since `q'(p) = (1-p)(1+3p) > 0`, it is
strictly increasing on `[0,1)`.

### Green function

Let `R = 1/rho` and `z in (0,R)`. Write:

- `G_z(x,y) = sum_n p^(n)(x,y) z^n` for the Green function;
- `F_z(x,y)` for the first-passage generating function;
- `a(z) = F_z(e,x_i)` and `F(z) = F_z(e,r_j) = F_z(e,r_j^{-1})`.

These do not depend on `i` or `j`, because permuting factors and inverting in
a `Z/3` factor are automorphisms of `Gamma` that preserve `S`.

The strong Markov property at the cut vertices, together with left
invariance, gives

```text
G_z(o,x) = G_z(o,o) prod_i f(h_i),   f(x_i) = a(z),   f(r_j^{±1}) = F(z).     (1.1)
```

### First-step equations

First-step analysis, again through the cut vertices, gives, with
`alpha = z/d`,

```text
a = alpha [1 + ((k-1) a + 2m F) a],
F = alpha [1 + F + (k a + 2(m-1) F) F].                                        (1.2)
```

For example, from `r^{-1}` the walk reaches `r` without passing `e`, at cost
`F_z(r^{-1},r) = F_z(e,r^2) = F`. From another generator `s`, it must return
through `e`, at cost `F_z(s,e) F_z(e,r)`.

`free_product_thresholds.py` checks (1.2) independently. It finds exact
rational agreement of `P^n(e,e)` with brute-force enumeration of reduced words
for `n <= 12`, for `(k,m) = (2,1)` and `(1,2)`.

### Bounds at R

`a(z)` and `F(z)` are power series with nonnegative coefficients, and they
are strictly increasing on `(0,R)`. They are bounded by 1 there. To see this:

- concatenating a first passage `o -> s`, a first passage `s -> o` and an
  arbitrary `o -> o` path is injective into the `o -> o` paths, and never
  produces the empty path;
- so `G_z(o,o) >= 1 + F_z(o,s)F_z(s,o) G_z(o,o)`;
- and `F_z(s,o) = F_z(e,s^{-1})`.

So `a(R) = lim_{z↑R} a(z) <= 1` and `F(R) <= 1` exist, and (1.2) holds at
`z = R` by passing to the limit.

### Word sums

For weights `u_2, u_3 > 0`, let

```text
S(u_2,u_3) = sum over nonempty reduced words of prod(letter weights),
```

where a `Z/2` letter has weight `u_2` and each of the two nontrivial elements
of a `Z/3` factor has weight `u_3/2`. So `u_i` is the total weight of one
factor. Put

```text
Phi(u_2,u_3) = k u_2/(1+u_2) + m u_3/(1+u_3).
```

## 2. The word-sum lemma

**Lemma 2.1.** `S(u_2,u_3) < infinity` if and only if `Phi(u_2,u_3) < 1`.
In that case `S = Phi/(1-Phi)`.

*Proof.* Let `S_c^{(L)}` be the sum over words of length at most `L` whose
first letter lies in factor `c`. Then

```text
S_c^{(L)} = u_c (1 + sum_{c' != c} S_{c'}^{(L-1)}).
```

Suppose `Phi < 1`. Put `S* = Phi/(1-Phi)` and
`S_c* = u_c (1+S*)/(1+u_c)`. Then `sum_c S_c* = S*` and
`S_c* = u_c (1 + sum_{c' != c} S_{c'}*)`. Induction on `L` gives
`S_c^{(L)} <= S_c*`, so `S <= S*` is finite.

Conversely, suppose `S < infinity`. Then `S_c = u_c(1 + S - S_c)` gives
`S_c = u_c(1+S)/(1+u_c)`. Summing over factors gives `S = Phi (1+S)`, so
`Phi = S/(1+S) < 1`. ∎

Combining (1.1) with the two-point product formula:

```text
sum_x tau_p(o,x)          = 1 + S(p, 2q(p)),
sum_x tau_p(o,x)^2        = 1 + S(p^2, 2q(p)^2),
sum_x G_z(o,x)^2          = G_z(o,o)^2 (1 + S(a(z)^2, 2F(z)^2)),
sum_x G_z(o,x) tau_p(o,x) = G_z(o,o) (1 + S(a(z)p, 2F(z)q(p))).               (2.1)
```

So `p_c` and `p_2` are the roots of `Phi(p,2q) = 1` and `Phi(p^2,2q^2) = 1`.
(The first is Kozáková's formula.)

## 3. The flat-rate point is the Green-weighted point

**Lemma 3.1 (any transitive graph).** Let
`A_p(z) = sum_n a_n(p) z^n = sum_x G_z(o,x) tau_p(o,x)`. The equality is
Tonelli. Then `lambda(p) = 1/r_p`, where `r_p` is the radius of convergence of
`A_p`. Hence

```text
p_* = sup{p : A_p(z) < infinity for every z < 1/rho}.
```

*Proof.* The limit exists because `a_{n+m} >= a_n a_m`, by Harris-FKG and the
Markov property. This is step 1 of `fpbs-lq-two-point-bounds-walk-rate-proof`.
It equals `limsup a_n^(1/n) = 1/r_p`. Also, `lambda >= rho` always holds,
because `a_n >= p^(n)(o,o)`. ∎

**Theorem 3.2.** On `Gamma_{k,m}` (any `k + m >= 2` with `m >= 1`),

```text
p_* = p_G := sup{p in [0,1] : Phi(a(R)p, 2F(R)q(p)) <= 1}.
```

*Proof.* The map `p -> Phi(a(R)p, 2F(R)q(p))` is continuous and strictly
increasing.

- Suppose `Phi(a(R)p, 2F(R)q(p)) <= 1`. For `z < R`, strict monotonicity of
  `a` and `F` gives `Phi(a(z)p, 2F(z)q(p)) < 1`. So `A_p(z) < infinity` by
  (2.1) and Lemma 2.1, and `G_z(o,o) < infinity`. Hence `r_p >= R` and
  `lambda(p) = rho`.
- Suppose `Phi(a(R)p, 2F(R)q(p)) > 1`. Continuity of `a` and `F` at `R` from
  below gives `z < R` with `Phi(a(z)p, ...) > 1`. Then `A_p(z) = infinity`,
  so `lambda(p) >= 1/z > rho`. ∎

This does not use `G_R(o,o) < infinity`, which is rho-transience.

## 4. The Green point A lies in the closed region

Let `D = {s in R^2 : Phi(e^{s_2}, e^{s_3}) < 1}`.

- By Lemma 2.1, `D = {s : S(e^{s_2}, e^{s_3}) < infinity}`.
- `D` is convex: by Cauchy–Schwarz,
  `S((s+t)/2) = sum_w e^{<n_w,s>/2} e^{<n_w,t>/2} <= S(s)^{1/2} S(t)^{1/2}`,
  where `n_w` counts the letters of each type.
- `D` is open. Since `Phi` is strictly increasing in each coordinate,
  `cl D = {Phi <= 1}` and `∂D = {Phi = 1}`.

**Lemma 4.1.** `A = (log a(R)^2, log 2F(R)^2)` lies in `cl D`.

*Proof.* Take `z < R`. By symmetry of simple random walk,

```text
sum_x G_z(o,x)^2 = sum_x G_z(o,x) G_z(x,o) = sum_n (n+1) p^(n)(o,o) z^n < infinity.
```

By (2.1) and Lemma 2.1, `Phi(a(z)^2, 2F(z)^2) < 1`. Let `z ↑ R`. ∎

Numerically `Phi(A) = 1.0000000000` in all six cases, which is the
square-root singularity `G'(R) = infinity`. Only `Phi(A) <= 1` is used.

By definition of `p_2`, the point `B = (log p_2^2, log 2q(p_2)^2)` lies in
`∂D`.

## 5. Strictness by convexity

The midpoint of `A` and `B` is

```text
M = (A+B)/2 = (log(a(R) p_2), log(2F(R) q(p_2))).
```

By convexity, `M` lies in `cl D`, which gives `p_G >= p_2` directly.

### The boundary curve

`∂D` is the graph of

```text
h(s_2) = logit((1 - k sigma(s_2))/m),   sigma = logistic,
```

on the interval `I = {s_2 : k sigma(s_2) < 1}`. The function `h` is
real-analytic on `I`.

**`h` is not affine unless `(k,m) = (1,1)`.**

- If `k >= 2`, then `I = (-infinity, logit(1/k))` and `h -> -infinity` at the
  finite right endpoint.
- If `k = 1` and `m >= 2`, then `h -> logit(1/m)`, which is finite, as
  `s_2 -> -infinity`, while `h(s_2) = -s_2 - log m + o(1) -> -infinity` as
  `s_2 -> +infinity`.

An affine function can do neither. By the identity theorem, `h` is affine on
no subinterval of `I`.

For `(k,m) = (1,1)`, `h(s_2) = -s_2` is affine.

**Proposition 5.1.** Suppose `(k,m) != (1,1)` and `m >= 1`. If `A != B`, then
`M in D`, so `Phi(a(R)p_2, 2F(R)q(p_2)) < 1` and `p_* = p_G > p_2`. If
`A = B`, then `M = B in ∂D` and `p_G = p_2`.

*Proof.* Suppose `M` is not in `D`. Then `M in ∂D`, and some affine
functional `l` satisfies `l < l(M)` on the open convex set `D`, and hence
`l <= l(M)` on `cl D`.

- Since `A, B in cl D` and `l(A) + l(B) = 2 l(M)`, we get
  `l(A) = l(B) = l(M)`.
- So the segment `[A,B]` lies in `cl D ∩ {l = l(M)}`, which misses `D`.
- So `[A,B]` lies in `∂D`, the graph of `h`.

A graph contains no vertical segment. So `A_2 != B_2`, and `h` is affine on
`[A_2, B_2]`, which is a contradiction.

Finally, `p -> Phi(a(R)p, 2F(R)q(p))` is continuous and strictly increasing,
so `Phi < 1` at `p_2` gives `p_G > p_2`. ∎

## 6. Certificate that A != B

Suppose `A = B`. Then `a(R) = p_2` and `F(R) = q(p_2)`, and by (1.2) at
`z = R`,

```text
z_1 := d a / (1 + ((k-1)a + 2mF) a)
     = R
     = d F / (1 + F + (ka + 2(m-1)F) F) =: z_2,
```

evaluated at `(a,F) = (p_2, q(p_2))`. This uses neither `R` nor the branch
point condition.

`certify_a_ne_b.py` works in exact `Fraction` arithmetic:

- it brackets `p_2` in a dyadic interval of width `2^-80` by bisection on the
  sign of `Phi(p^2, 2q^2) - 1`;
- it encloses `z_1` and `z_2` over that interval using monotonicity;
- it checks that the two enclosures are disjoint.

Output:

| (k,m) | p_2 | z_1 | z_2 | disjoint |
|---|---|---|---|---|
| (2,1) | 0.5736455868 | 1.068155 | 1.127409 | yes |
| (3,1) | 0.4867568402 | 1.177954 | 1.218314 | yes |
| (1,2) | 0.4710902511 | 1.116916 | 1.150125 | yes |
| (2,2) | 0.4183130440 | 1.227178 | 1.250122 | yes |
| (4,1) | 0.4331905865 | 1.280100 | 1.308289 | yes |
| (1,1) | 0.7761733270 | 0.964505 | 1.043896 | yes |

So `A != B` in all six cases, and Proposition 5.1 gives `p_* > p_2` for the
first five.

## 7. Numbers and calibration

The values below are floating point. The branch point comes from Newton's
method on (1.2) together with `det(I - J) = 0`, with residual below `2e-16`.
They are not certified. Only the sign of `p_G - p_2` is proved, in Sections 5
and 6.

| (k,m) | deg | rho | p_c | p_2 | p_* = p_G | p_* - p_2 |
|---|---|---|---|---|---|---|
| (2,1) | 4 | 0.911910 | 0.360461 | 0.5736456 | 0.5737271 | 8.1e-5 |
| (1,1) | 3 | 0.988482 | 0.637278 | 0.7761733 | 0.7761733 | 0 |
| (3,1) | 5 | 0.837198 | 0.259385 | 0.4867568 | 0.4868021 | 4.5e-5 |
| (1,2) | 5 | 0.874311 | 0.270837 | 0.4710903 | 0.4711430 | 5.3e-5 |
| (2,2) | 6 | 0.804454 | 0.208772 | 0.4183130 | 0.4183386 | 2.6e-5 |
| (4,1) | 6 | 0.775091 | 0.204144 | 0.4331906 | 0.4332126 | 2.2e-5 |

### Mechanism

`p_*` is fixed by pairing the two-point function with the Green function at
the spectral radius, and `p_2` by pairing it with itself. In log-weight
coordinates both thresholds are read off one convex region `D`:

- `A` is the Green function's point, which is l2-borderline;
- `B` is the two-point function's l2 point;
- `p_*` is where the ray through the geometric mean `M` of `A` and `B` leaves
  `D`.

Equality `p_* = p_2` needs the boundary of `D` to be flat between `A` and `B`.
This happens:

- when there is only one block type, as on `T_d` and in the radial heuristic
  of the target's first Attempt, where `D` is an interval and `A = B`;
- or when the boundary is a line, as for `PSL_2(Z) = Z/2 * Z/3`, where only
  the product `u_2 u_3` matters.

With two block types that are not forced to alternate, the Green function and
the two-point function are l2-borderline along different block-type
frequencies, and strict convexity separates them.

### Consequences for the goal

This does not give a new case of Benjamini–Schramm: here `p_u = 1`. What it
settles:

1. `fpbs-flat-rate-point-equals-l2-point` is false. The flat-rate statement
   `p_c < p_*` (hole [F] of `fpbs-flat-rate-route`) is, as a property of the
   graph, strictly weaker than `p_c < p_2` on some Cayley graphs. So the
   flat-rate lane does not collapse to the l2 lane.
2. Lemma 3.1 is an exact characterization on every transitive graph. It says
   that [F] at `p` is equivalent to `sum_x G_z(o,x) tau_p(o,x) < infinity`
   for every `z < 1/rho`. This is the Green-visit functional of
   `fpbs-green-visit-criterion-universal`, taken at `z = 1`, pushed all the
   way to the spectral radius.
3. Any proof of `p_* <= p_2` for a class of graphs must fail on these
   tree-like graphs. So it must use something false for free products with
   two block types.
