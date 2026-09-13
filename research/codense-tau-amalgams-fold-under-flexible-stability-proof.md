---
rg: 2
id: codense-tau-amalgams-fold-under-flexible-stability-proof
kind: route
title: A swap vector on doubled finite actions plus flexible correction folds the two vertex copies
target: codense-tau-amalgams-fold-under-flexible-stability
requires: []
---

Notation as in the claim. The proof is elementary. Its inputs are the normal
form theorem for amalgamated free products (Serre, *Trees*, Ch. I), Bowen--Burton's
definitions of perfect approximations and of conjugacy, and linear algebra.

## 1. Swap vector (proof of F1)

Fix `U`, `rho_0` and `rho_1`. Put `V' = U x {0,1}`, and let `A_0 x A_1` act on it
by

```text
rho(a,b)(u,0) = (rho_0(a) u, 0),      rho(a,b)(u,1) = (rho_1(b) u, 1).
```

Let `X = V' x V'` carry the diagonal action, with permutation representation
`lambda` on `l2(X)`. Let `tau(u,i) = (u, 1-i)` and take the unit vector

```text
xi = |V'|^(-1/2) sum_{x in V'} delta_(x, tau x).
```

**The inner product.** For `g` in `A_0 x A_1`,

```text
lambda(g) xi = |V'|^(-1/2) sum_{y in V'} delta_(y, rho(g) tau rho(g)^(-1) y),
<lambda(g) xi, xi> = |{ y : rho(g) tau rho(g)^(-1) y = tau y }| / |V'|.
```

Take `g = (a,b)`.
- For `y = (u,0)`: `rho(g) tau rho(g)^(-1) y = (rho_1(b) rho_0(a)^(-1) u, 1)` and
  `tau y = (u,1)`. They agree exactly when `x = rho_0(a)^(-1) u` satisfies
  `rho_1(b) x = rho_0(a) x`.
- For `y = (u,1)`: they agree exactly when `x = rho_1(b)^(-1) u` satisfies
  `rho_0(a) x = rho_1(b) x`.

Both substitutions are bijections of `U`, so

```text
<lambda(a,b) xi, xi> = 1 - d_U(rho_0(a), rho_1(b)),
|| lambda(a,b) xi - xi ||^2 = 2 d_U(rho_0(a), rho_1(b)).                        (SW1)
```

**The gap step.** Write `xi = xi_D + xi_perp`, where `xi_D` is fixed by
`lambda(Delta)` and `xi_perp` is orthogonal to the `Delta`-fixed vectors. That
subspace and its complement are both `lambda(Delta)`-invariant. For `s` in `S`,
`lambda(iota_0 s, iota_1 s) xi - xi = lambda(iota_0 s, iota_1 s) xi_perp - xi_perp`.
Hypothesis (tau-Delta) gives

```text
kappa || xi_perp || <= max_{s in S} || lambda(iota_0 s, iota_1 s) xi - xi ||.   (SW2)
```

**The closure step.** Let `(a,b)` lie in `Delta_bar`. The kernel `N` of
`rho : A_0 x A_1 -> Sym(V')` has finite index and is normal, and `lambda`
factors through `(A_0 x A_1)/N`. Since `(a,b)` lies in `Delta N`,
`lambda(a,b) = lambda(iota_0 h, iota_1 h)` for some `h` in `H`, so `lambda(a,b)`
fixes `xi_D`. Hence

```text
|| lambda(a,b) xi - xi || = || lambda(a,b) xi_perp - xi_perp || <= 2 || xi_perp ||
                          <= (2/kappa) max_{s in S} || lambda(iota_0 s, iota_1 s) xi - xi ||.
```

Squaring and inserting (SW1) on both sides gives
`2 d_U(rho_0 a, rho_1 b) <= (4/kappa^2) * 2 max_s d_U(rho_0 iota_0 s, rho_1 iota_1 s)`,
which is (FT1).

## 2. Flexible correction (proof of F2)

**The data.** By hypothesis there are finite sets `U^(j)`, injections
`pi^(j) : V_n -> U^(j)` and `r^(j) : W^(j) -> U^(j)`, and homomorphisms
`xi^(j) : A_j -> Sym(W^(j))` with the following properties.
- `|V_n|/|U^(j)| -> 1` and `|W^(j)|/|U^(j)| -> 1`.
- For each fixed `g` in `A_j`, the pushforwards of `sigma_n(i_j g)` and of
  `xi^(j)(g)` (the identity off the images) agree on all but a vanishing
  fraction of `U^(j)`.

**Gluing.** Let `U_n` be `U^(0)` and `U^(1)` glued along `V_n`, that is
`pi^(0)(v) ~ pi^(1)(v)`. Then `|U_n| = |U^(0)| + |U^(1)| - |V_n|`, so
`|V_n|/|U_n| -> 1`. Define two families of permutations of `U_n`:
- `R_j(g)`: the pushforward of `xi^(j)(g)`, extended by the identity on
  `U_n \ U^(j)`. Each `R_j` is a homomorphism.
- `T_j(g)`: `sigma_n(i_j g)` on `V_n` and the identity elsewhere.

For fixed `g` in `A_j`, both `T_j(g)` and `R_j(g)` are the identity off
`U^(j)`, and `|U^(j)| <= |U_n|`, so

```text
d_{U_n}(T_j(g), R_j(g)) -> 0.                                                  (FC1)
```

**On the generators.** For `s` in `S`, the elements `i_0 iota_0 s` and
`i_1 iota_1 s` of `P` are equal, so `T_0(iota_0 s) = T_1(iota_1 s)`. With (FC1),
`d_{U_n}(R_0(iota_0 s), R_1(iota_1 s)) -> 0`.

**Conclusion.** By (FT1) for `U_n`, `R_0`, `R_1`, every `(a,b)` in `Delta_bar`
has `d_{U_n}(R_0 a, R_1 b) -> 0`. By (FC1) again, `d_{U_n}(T_0 a, T_1 b) -> 0`.
Since `T_j` agrees with `sigma_n o i_j` on `V_n`,

```text
d_{V_n}(sigma_n(i_0 a), sigma_n(i_1 b)) <= (|U_n|/|V_n|) d_{U_n}(T_0 a, T_1 b) -> 0.
```

## 3. Nonsoficity (proof of F3)

Suppose `sigma_n` is a sofic approximation of `P`. By the normal form theorem
the vertex maps `i_j` are injective, so each `sigma_n o i_j` is a sofic
approximation of `A_j`, and by (FS) it is conjugate to a perfect one. So (F2)
applies.

Choose `(a,b)` in `Delta_bar \ Delta`. By the normal form theorem, `i_0(a) = i_1(b)`
in `P` only if `a = iota_0(h)` and `b = iota_1(h)` for some `h`. So
`w = i_0(a) i_1(b)^(-1) != 1`.

**Why the image of `w` is nearly trivial.**
- Asymptotic multiplicativity makes `sigma_n(1)` Hamming-close to a permutation
  equal to its own square off few points, and a permutation `p` with
  `p(p(x)) = p(x)` has `p(x) = x`. So `sigma_n(1)` tends to the identity.
- Hence `sigma_n(x^(-1))` is close to `sigma_n(x)^(-1)`, and
  `sigma_n(w) ~ sigma_n(i_0 a) sigma_n(i_1 b)^(-1)`, which by (F2) is close to the
  identity.

So the fraction of points fixed by `sigma_n(w)` tends to 1, while a sofic
approximation sends it to 0 for `w != 1`. This is a contradiction.

## 4. The double

- **(tau-C) gives (tau-Delta).** A finite `A x A`-set `X`, pulled back along the
  diagonal `A -> A x A`, is a finite `A`-set. The `Delta`-fixed vectors are the
  `C`-fixed vectors, and the generators `(s,s)` act as `s`.
- **Profinite density gives the diagonal in `Delta_bar`.** Let `N` be a
  finite-index normal subgroup of `A x A`. The subgroup
  `M = { m : (m,1) in N and (1,m) in N }` has finite index, is normal in `A`,
  and `M x M <= N`. Density gives `CM = A`, so `a = cm` with `c` in `C` and
  `m` in `M`, and `(a,a) = (c,c)(m,m)` lies in `Delta N`.
- **A proper subgroup gives a fold word.** If `C != A`, any `a` in `A \ C`
  gives `(a,a)` in `Delta_bar \ Delta`.

## 5. Scope

- **Property (T) is never used.** Only the edge group's gap on finite actions
  enters, together with the profinite closure.
- **Twisted embeddings.** The argument covers two different embeddings
  `iota_1 = iota_0 o theta` into one group, with no change. One then needs
  (tau-Delta) for the graph subgroup over all finite `A x A`-sets, and
  `Delta_bar != Delta`.
