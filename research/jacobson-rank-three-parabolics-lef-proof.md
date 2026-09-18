---
rg: 2
id: jacobson-rank-three-parabolics-lef-proof
kind: route
title: Extend the mirror-glued Levi model by evaluating the column on the first basis vectors, then transport it to every rank-three parabolic
target: jacobson-rank-three-parabolics-are-lef
requires:
  - binary-jacobson-el2-is-lef
  - binary-jacobson-mark-dichotomy-holds-from-rank-two
artifacts:
  - experiments/jacobson-parabolic-lef-2026-09-17/check_parabolic_lef.py
---

Notation as in the target. `V_+ = F^((N)) (x) F^2` carries the near action
`g -> g_+` of `M_2(J)`. `W_M = span{e_(k,i) : 0 <= k <= M}`, and `Phi_M` is
the glued map (G1) of `binary-jacobson-el2-lef-proof`. LEF is used in the
finite-subset sense. For every finite `B` there is a map `phi : G -> H` into a
finite group that is injective on `B` and satisfies
`phi(xy) = phi(x) phi(y)` for `x, y in B`.

## Step 0. What is imported from the rank-two route

Fix a finite set `B_2 ⊂ EL_2(J)` with `1 in B_2 = B_2^(-1)`. Let `R` and `C`
be the constants of that route for `B_2 ∪ B_2 B_2`. For `M > 4(R + C) + 4`
the route shows:

- `Phi_M(g) in GL(W_M)` for `g in B_2 ∪ B_2 B_2`;
- `Phi_M(gh) = Phi_M(g) Phi_M(h)` for `g, h in B_2`;
- `Phi_M` is injective on `B_2`.

Moreover, directly from (G1), `Phi_M(g) e_k = g_+ e_k` for every `k <= M/2`,
and `supp(g_+ e_k) ⊂ [k - R, k + R]`. Hence, for every vector `w in V_+`
supported in `[0, M/2]`:

```text
Phi_M(g) w = g_+ w   (in particular g_+ w in W_M).                 (E0)
```

This is the only property of `Phi_M` used besides the three facts listed above.

## Step 1. Column evaluation

For `d >= 1` define the `F`-linear map

```text
ev_d : J -> F^((N))^d,      ev_d(x) = (x e_0, x e_1, ..., x e_(d-1)),
```

and apply it entrywise to matrices. For `X in M_(2 x m)(J)`, `ev_d(X)` is the
linear map `F^m (x) F^d -> V_+` sending `f_j (x) delta_s` to `X_(.j) e_s`,
where `X_(.j) e_s = (X_1j e_s, X_2j e_s)`.

**(E1) Left equivariance.** `ev_d(gX) = g_+ ev_d(X)` for `g in M_2(J)`,
because `(gX)_(.j) e_s = g_+ (X_(.j) e_s)`. This holds since `V_+` is a module.

**(E2) Right scalar equivariance.** `ev_d(X c) = ev_d(X) (c (x) 1_d)` for
`c in M_m(F)`. Indeed `(Xc)_(.j) e_s = sum_i c_ij X_(.i) e_s`, since the
entries of `c` are central scalars.

**(E3) Kernel.** `ev_d(x) = 0` if and only if `x in span{S^a T^b : b >= d}`.
- The operator `S^a T^b` kills `e_s` for `s < b` and sends `e_s` to
  `e_(s-b+a)` for `s >= b`, so the span lies in the kernel.
- Conversely, write `x = sum c_ab S^a T^b` in the monomial basis, and suppose
  some `c_ab` with `b < d` is nonzero. Let `b_0` be the least such `b`. Then
  `x e_(b_0) = sum_a c_(a b_0) e_a + (terms from b > b_0, which vanish on e_(b_0))`.
  So `x e_(b_0) = sum_a c_(a b_0) e_a != 0`.

Consequently, for any finite set `Y ⊂ M_(2 x m)(J)`, `ev_d` is injective on
`Y` once `d` exceeds every `T`-degree `b` occurring in the entries of the
differences `Y - Y`.

**(E4) Support.** If every monomial `S^a T^b` in the entries of `X` has
`a <= D`, then `ev_d(X)` takes values supported in `[0, d + D]`, because
`S^a T^b e_s` is `0` or `e_(s - b + a)` with `s - b + a < d + D`.

## Step 2. The column parabolic G_m is LEF (P1)

**Normal form.** Write `x = (g, X, c)` for `[[g, X], [0, c]]`. Block
multiplication gives

```text
(g, X, c)(g', X', c') = (g g', g X' + X c', c c').                      (N)
```

So `G_m` is a group, with `(g, X, c)^(-1) = (g^(-1), -g^(-1) X c^(-1), c^(-1))`.
Also `(g, X, c) = (1, X, 1)(g, 0, 1)(1, 0, c)`, and
`(1, X, 1) = prod x_(i alpha)(X_(i alpha))`. Therefore `G_m^el` is generated
by `x_12(J)`, `x_21(J)`, the roots `x_(i alpha)(J)` with `i <= 2 < alpha`, and
`EL_m(F)`. In particular `G_1^el = G_1 = <x_12(J), x_21(J), x_13(J), x_23(J)>`.

**Choice of constants.** Let `B ⊂ G_m` be finite, with `1 in B = B^(-1)`.
- Let `B_2` be the set of first components of `B`. It is finite and symmetric
  and contains `1`. Take `R` and `C` as in Step 0 for `B_2`.
- Let `D` be the largest `S`-exponent `a` occurring in the entries of `X` over
  all `(g, X, c) in B ∪ BB`.
- Let `d` exceed every `T`-exponent `b` occurring in the entries of `X - X'`
  over all pairs of elements of `B`.
- Take `M > max(4(R + C) + 4, 2(d + D))`.

**The model.** Let `H = GL(W_M ⊕ (F^m (x) F^d))`, a finite group. For
`x = (g, X, c) in B ∪ BB` put

```text
Psi(x) = [[ Phi_M(g), ev_d(X) ], [ 0, c (x) 1_d ]].
```

Here `ev_d(X)` maps into `W_M` by (E4), since `d + D < M/2`. Put
`Psi(x) = 1` for `x` outside `B ∪ BB`.

**Multiplicativity on B x B.** Let `x = (g, X, c)` and `y = (g', X', c')` be
in `B`. Block multiplication gives

```text
Psi(x) Psi(y) = [[ Phi_M(g) Phi_M(g'),  Phi_M(g) ev_d(X') + ev_d(X)(c' (x) 1_d) ],
                 [ 0,                   c c' (x) 1_d ]].
```

- `Phi_M(g) Phi_M(g') = Phi_M(g g')` by Step 0.
- `ev_d(X')` has values supported in `[0, d + D] ⊂ [0, M/2]`. So by (E0) and
  (E1), `Phi_M(g) ev_d(X') = g_+ ev_d(X') = ev_d(g X')`.
- `ev_d(X)(c' (x) 1_d) = ev_d(X c')` by (E2).
- So the upper right block is `ev_d(g X' + X c')`. By (N), `Psi(x) Psi(y) = Psi(xy)`.

Since `Psi(1) = 1` and `x^(-1) in B`, each `Psi(x)`, `x in B ∪ BB`, is
invertible. Hence `Psi` does take values in `H` on `B ∪ BB`.

**Injectivity on B.** Suppose `Psi(x) = Psi(y)` for `x, y in B`.
- The lower right blocks give `c = c'`.
- The upper left blocks give `Phi_M(g) = Phi_M(g')`, so `g = g'` by Step 0.
- The upper right blocks give `ev_d(X - X') = 0`, so `X = X'` by (E3) and the
  choice of `d`.

So `G_m` is LEF, and so is its subgroup `G_m^el`.

**Consequences.** MF, soficity, hyperlinearity and `Rad_MF = 1` follow exactly
as in Step 4 of `binary-jacobson-el2-lef-proof`: compose with left regular
representations of the finite groups `H`. The head is
`x_13(Q) = (1, (Q, 0)^t, 1)`, and `Q e_0 = e_0 - S T e_0 = e_0`. So the
upper right block of `Psi(x_13(Q))` is nonzero for every `d >= 1`, and the
head has nontrivial image in every model.

**Remark.** The only place the Levi model is used is (E0): a model agreeing
with the near action `g_+` on low columns. The column block is evaluated only
on low columns. The mirror end of `Phi_M` absorbs the Fredholm defect and never
interacts with the column. This is exactly why the construction fails for the
double parabolic `M_2(J) x| (EL_2(J) x EL_2(J))`. There the second Levi factor
acts on the column from the right with nonconstant coefficients. `ev_d` is not
right equivariant for nonconstant right multiplication, because right
multiplication by `T` moves the evaluation window.

## Step 3. Every proper parabolic of EL_3(J) is LEF (P2)

**Roots.** Write `alpha_ij = e_i - e_j` for `i != j` in `{1,2,3}`, and
`x_alpha(J)` for the root subgroup. A set `Psi` of roots is closed if
`alpha, beta in Psi` and `alpha + beta` a root imply `alpha + beta in Psi`.
For `lambda in Z^3` put `P_lambda = {alpha_ij : lambda_i >= lambda_j}`.

**(a) Maximal parabolic sets.** Up to the Weyl group `S_3`, a nonconstant
`lambda` gives one of two maximal sets:
- `lambda = (1,1,0)`: `P = {±alpha_12, alpha_13, alpha_23}`. The group
  `<x_alpha(J) : alpha in P>` is `G_1`, the column type.
- `lambda = (1,0,0)`: `P' = {±alpha_23, alpha_12, alpha_13}`, the row type
  `[[1, *, *], [0, *, *], [0, *, *]]`.

Every nonconstant `lambda` has `P_lambda` inside one of the six Weyl
translates of `P` or `P'`. For a generic `lambda`, `P_lambda` is a positive
system, and it lies in both maximal sets containing it.

**(b) Every proper closed set lies in a maximal parabolic set.** The script
checks all `2^6` subsets of the six roots. There are 29 closed subsets, 28 of
them proper, and each proper one lies in some translate of `P` or `P'`.

A conceptual reason: the symmetric closed subsets of `A_2` are `∅`,
`{±alpha}` and `A_2`, and a closed set whose symmetric part is not all of
`A_2` lies in a parabolic set. The brute force makes this check unnecessary.

**(c) Weyl translates.** A signed permutation matrix `w in SL_3(F) = EL_3(F)`
satisfies `w x_ij(a) w^(-1) = x_(sigma i, sigma j)(± a)`. Conjugation by `w` is
an automorphism of `EL_3(J)`, and it carries `<x_alpha(J) : alpha in P_lambda>`
onto the subgroup for `P_(sigma lambda)`. So every column-type maximal parabolic
subgroup is isomorphic to `G_1`.

**(d) Row type.** Define `Theta(g) = (g^tau)^(-1)` on `GL_3(J)`, where `g^tau`
applies the anti-automorphism `tau` entrywise and transposes.
- `(gh)^tau = h^tau g^tau` (Step 2(a) of `binary-jacobson-el2-lef-proof`, which
  is entrywise and holds in every size). So `Theta` is an automorphism.
- `Theta(x_ij(a)) = x_ji(-tau a)`, and `tau` is bijective on `J`, so `Theta`
  preserves `EL_3(J)`.
- `Theta` maps the subgroup for `P'` onto the subgroup for
  `{±alpha_32, alpha_21, alpha_31} = P_(0,1,1)`, which is column type.

So every row-type maximal parabolic subgroup is isomorphic to `G_1` as well.

**Conclusion.** For a proper closed `Psi`, `U_Psi` lies in a maximal parabolic
subgroup, and that subgroup is isomorphic to `G_1`, which is LEF by Step 2.
Subgroups of LEF groups are LEF. For the head: `x_13(Q)` lies in the subgroup
for `P` and for `P_(1,0,0)`. In each model it is sent to an image under an
isomorphism onto `G_1`, of the form `x_(ij)(± Q)` or `x_(ji)(-Q)`, which is a
column root of `G_1`. That is nontrivial in the models by Step 2, because
`ev_d` detects every nonzero column entry of degree less than `d`.

## Step 4. Finite quotients of G_1 kill the head (P3)

Let `pi : G_1 -> H` be a homomorphism to a finite group, with kernel `K`.
Let `N = {(1, v) : v in J^2} ≅ (J^2, +)`. It is normal in `G_1`, and
`(g, 0)(1, v)(g, 0)^(-1) = (1, g v)`.

**`W = K ∩ N` is a submodule of the form `I ⊕ I`.** `W` is a finite-index
additive subgroup of `J^2`, since `N/W` embeds in `H`. It is invariant under
`v -> g v` for every `g in EL_2(J)`, since `K` is normal. Put
`I_1 = {x : (x, 0) in W}` and `I_2 = {y : (0, y) in W}`.
- For `(v_1, v_2) in W` and `a in J`, `x_12(a) v - v = (a v_2, 0)` and
  `x_21(a) v - v = (0, a v_1)`, both in `W`. So `J v_2 ⊂ I_1` and
  `J v_1 ⊂ I_2`.
- Applying this to `(x, 0)` and `(0, y)` gives `J I_1 ⊂ I_2` and
  `J I_2 ⊂ I_1`. With `a = 1`, `I_1 ⊂ I_2 ⊂ I_1`.
- So `I := I_1 = I_2` is a left ideal, and every `(v_1, v_2) in W` has
  `v_1, v_2 in I`. Hence `W = I ⊕ I`, and `I` has finite index in `J`.

**`Q in I`.** `J/I` is a finite left `J`-module. On it, `T S = 1`, so `S` is
injective on a finite set, hence bijective, so `S T = 1` on `J/I` as well.
Applied to the class of `1`: `(1 - ST) · 1 = Q in I`.

**Conclusion.** `(Q, 0) in W ⊂ K`, that is, `pi(x_13(Q)) = 1`.
- `G_1` is not residually finite.
- A finitely presented LEF group is residually finite, so `G_1` is not
  finitely presented. If `G_1` is not finitely generated, this holds
  trivially.
- The same argument applies to the first two rows of `G_m`, using the
  `2 x 1` columns. Every `x_(i alpha)(Q)` dies in every finite quotient,
  while (P1) keeps it alive in finite local models. For a column `alpha`,
  `N_alpha = {(1, X, 1) : X supported in column alpha}` is invariant under
  conjugation by `(g, 0, 1)`, which acts as `X -> gX`. So `K ∩ N_alpha` is an
  `EL_2(J)`-invariant finite-index subgroup of `J^2`, and the argument above
  applies.

## Step 5. Generation boundary (P4)

The Steinberg relation `[x_ij(a), x_jk(b)] = x_ik(ab)` holds for distinct
`i, j, k`.
- **With `x_31(1)`.** `[x_31(1), x_12(a)] = x_32(a)` for all `a`. Then
  `[x_32(a), x_21(b)] = x_31(ab)`, so `x_31(J)` is reached as well. With
  `G_1 ⊃ x_12(J), x_21(J), x_13(J), x_23(J)`, all six root subgroups are
  present, and the group is `EL_3(J)`.
- **With `x_32(1)`.** `[x_32(1), x_21(b)] = x_31(b)`, and then
  `[x_31(a), x_12(b)] = x_32(ab)`.
- **General `m`.** Let `n = m + 2`, `alpha > 2` and `i <= 2`, and put
  `{i, i'} = {1, 2}`.
  - `[x_(alpha i)(1), x_(i i')(a)] = x_(alpha i')(a)`, and then
    `[x_(alpha i')(a), x_(i' i)(b)] = x_(alpha i)(ab)`. So row `alpha` of the
    lower-left block is full.
  - For `beta > 2` with `beta != alpha`, `x_(beta alpha)(1) in EL_m(F)` and
    `[x_(beta alpha)(1), x_(alpha j)(b)] = x_(beta j)(b)`. So every
    `x_(beta j)(J)` with `beta > 2`, `j <= 2` is present.
  - Finally `[x_(beta j)(a), x_(j gamma)(b)] = x_(beta gamma)(ab)` for
    `beta != gamma > 2` and `j <= 2`. This gives the `J`-coefficient roots in
    the lower block.
  - Hence all root subgroups are present, and the group is `E_n`.

## Step 6. The class death

**Setup.** Let `h = x_13(Q)`. Call an argument *`G_1`-local* if it is, in
effect, a proof of the following statement:

> for every sequence of maps `phi_k : G_1 -> U(n_k)` with
> `||phi_k(xy) - phi_k(x) phi_k(y)|| -> 0` for all `x, y in G_1`,
> `||phi_k(h) - 1|| -> 0`.

Any argument about a larger group `A ⊃ G_1` (such as `St_n(J)` or `EL_n(J)`
on some index triple) that uses only relations holding in `G_1`, and only the
asymptotic multiplicativity of the model on pairs from `G_1`, is `G_1`-local.

**Why every such argument fails.** Choose finite sets `B_k` exhausting `G_1`,
and take the models `Psi_k` of Step 2 for `B_k`. Let `lambda_k` be the left
regular representation of the finite group `H_k`, and set
`phi_k = lambda_k ∘ Psi_k`.
- For fixed `x, y`, eventually `x, y in B_k`, and then
  `phi_k(xy) = phi_k(x) phi_k(y)` exactly.
- For large `k`, `Psi_k(h) != 1` by Step 2. Hence
  `||phi_k(h) - 1|| >= ||delta_(Psi_k(h)) - delta_1|| = sqrt 2`.

So the statement is false, and no `G_1`-local argument exists. By Step 3,
the same holds with `G_1` replaced by any proper parabolic of any index
triple.

**Coverage.** The following are all `G_1`-local.
- Any relation of `EL_2(J)`: the Whitehead involution, the symbol cocycle and
  the Fredholm index.
- The compressor `u = [[S, Q], [0, T]] in EL_2(J)`, together with
  `u N u^(-1) <= N`.
- Both three-index commutator families.
- Relative-(T)-type projection arguments for the pair `(G_1, N)`. These
  concern only the restriction of the model to `G_1`.
- Finite-image module collapse. Step 4 shows it is exactly the mechanism that
  separates finite quotients, where `h` dies, from local models, where `h`
  survives.

**What remains for three indices.** Let `P_mu` be a maximal parabolic set of
the triple other than `P`.
- Both sets have four elements, so `P_mu` contains `alpha_31` or `alpha_32`.
- The subgroup generated by the two parabolics therefore contains
  `x_31(1)` or `x_32(1)`, and it is `EL_3(J)` by Step 5.
- The general pair reduces to this one by Weyl conjugation (Step 3(c)).

`binary-jacobson-mark-dichotomy-holds-from-rank-two` gives
`Rad_MF(EL_3(J)) in {1, L_3}`, with `h in L_3 \ {1}`. So a three-index proof
that `h` dies in MF models is equivalent to proving `EL_3(J)` is not MF. The
rank-five property (T) route does not give this. A (T)-free head-collapse
proof must therefore either prove `EL_3(J)` is not MF, or use at least four
indices in an essential way.

## Step 7. Numerical confirmation

`experiments/jacobson-parabolic-lef-2026-09-17/check_parabolic_lef.py` takes
`F = F_2`, `m = 1`, `M = 100` and `d = 8`. It tests 400 random words of length
at most 7 in `x_12(a)`, `x_21(a)`, `x_13(a)` and `x_23(a)`, over 12
coefficient types.
- **Multiplicativity.** The affine product of the generator images equals
  `Psi` of the exact element, with `theta` recomputed from `g^(-1)` through
  `K (g^tau)^(-1) K^(-1)`. There were 0 failures.
- **Injectivity.** 367 distinct elements gave 367 distinct images.
- **Relations.** Both three-index commutator families hold exactly in the
  images, for all coefficient pairs.
- **Head.** `x_13(Q)` has a nonzero column block.
- **Control.** Hard truncation in place of `Phi_M` fails 34 times.
- **Root sets.** All 28 proper closed subsets of `A_2` lie in a maximal
  parabolic set.
- The script exits 0 in about 25 seconds.
