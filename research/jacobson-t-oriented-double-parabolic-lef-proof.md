---
rg: 2
id: jacobson-t-oriented-double-parabolic-lef-proof
kind: route
title: Right multiplication by T is exact on the evaluation window, so the column-evaluation model extends to a T-oriented right Levi
target: jacobson-t-oriented-double-parabolic-is-lef
requires:
  - jacobson-rank-three-parabolics-are-lef
  - binary-jacobson-el2-is-lef
  - jacobson-double-parabolic-two-step-models-kill-head
artifacts:
  - experiments/jacobson-levi-orientation-2026-09-17/check_orientation.py
---

Notation is as in the target and in `jacobson-rank-three-parabolics-lef-proof`.
- `V_+ = F^((N)) (x) F^k` with `S e_j = e_(j+1)`, `T e_j = e_(j-1)` and
  `T e_0 = 0`. `W_M` is the span of the `e_j`, `j <= M`.
- `Phi_M` is the glued model of `binary-jacobson-el2-lef-proof`.
- `ev_d(X) : F^l (x) F^d -> V_+` sends `f_c (x) delta_s` to `X_(.c) e_s`.
- LEF is meant in the finite-subset sense of that route.

## Step 0. Imports

From `jacobson-rank-three-parabolics-lef-proof`, which proves them for any
number of rows and columns:
- Step 0: the three properties of `Phi_M` on `B_2 ∪ B_2 B_2`, and (E0).
- Step 1: (E1) left equivariance `ev_d(gX) = g_+ ev_d(X)`.
- Step 1: (E3) `ev_d(x) = 0` iff `x in span{S^a T^b : b >= d}`.
- Step 1: (E4) `ev_d(X)` is supported in `[0, d + D]` if every `S`-exponent in
  `X` is at most `D`.

Their proofs are entrywise, so they hold verbatim for `X in M_(k x l)(J)`.

## Step 1. The window is T-stable

Let `N_d` be the nilpotent shift of `F^d` with `N_d delta_s = delta_(s-1)`
and `N_d delta_0 = 0`.
- `T^j -> N_d^j` extends to a ring homomorphism `F[T] -> F[N_d]`. Its kernel
  is `T^d F[T]`, because `F[T]` is a polynomial ring and `N_d` has minimal
  polynomial `x^d`.
- For `C in M_l(F[T])` write `C^(d)` for the entrywise image in
  `M_l(F[N_d]) ⊂ End(F^l (x) F^d)`. Then `C -> C^(d)` is a ring homomorphism,
  so `EL_l(F[T]) -> GL(F^l (x) F^d)` is a group homomorphism.

**(E5) Right equivariance.** For `X in M_(k x l)(J)` and `C in M_l(F[T])`:

```text
ev_d(X C) = ev_d(X) C^(d).
```

*Proof.* Both sides are additive in `C`. So take `C = T^j E_(c c')` and
evaluate on `f_(c') (x) delta_s`, `s < d`.
- The left side gives `X_(.c) T^j e_s`. This is `X_(.c) e_(s-j)` if
  `s >= j`, and `0` otherwise.
- On the right, `C^(d)` sends `f_(c') (x) delta_s` to
  `f_c (x) N_d^j delta_s`. This is `f_c (x) delta_(s-j)` if `s >= j`, and `0`
  otherwise. Then `ev_d(X)` sends it to `X_(.c) e_(s-j)`, or to `0`.

The two sides agree for every `s < d`, with no truncation error, because
`T` maps `span(e_0, ..., e_(d-1))` into itself. QED.

**Contrast, not used.** `S` sends `e_(d-1)` to `e_d`, which lies outside the
window. So `ev_d(X S)` is not a function of `ev_d(X)`, and no
`d x d` matrix can replace `N_d` for `S`. This is Control D of the artifact.

## Step 2. P^T_l is LEF (statement A)

**Normal form.** `P^T_l` is closed under the product of the target, because
`X B'` lies in `M_(2 x l)(J)` and `B B'` lies in `EL_l(F[T])`. Inverses are
`(g, X, B)^(-1) = (g^(-1), -g^(-1) X B^(-1), B^(-1))`. It is a subgroup of
`EL_(2+l)(J)`: `(g, X, B) = (1, X, 1)(g, 0, 1)(1, 0, B)`, and `(1, X, 1)` is
a product of root elements `x_(i, 2+c)(X_ic)`.

**Constants.** Let `B ⊂ P^T_l` be finite, with `1 in B = B^(-1)`.
- `B_2` is the set of first components. Take `R` and `C` for `B_2` as in
  Step 0.
- `D` is the largest `S`-exponent in the entries of `X`, over all
  `(g, X, B) in B ∪ BB`.
- `d` exceeds every `T`-exponent in the entries of `X - X'` and of `B - B'`,
  over all pairs of elements of `B`.
- `M > max(4(R + C) + 4, 2(d + D))`.

**The model.** Let `H = GL(W_M ⊕ (F^l (x) F^d))`. For
`x = (g, X, B) in B ∪ BB` put

```text
Psi(x) = [[ Phi_M(g), ev_d(X) ], [ 0, B^(d) ]],
```

and `Psi(x) = 1` elsewhere. `ev_d(X)` lands in `W_M` by (E4), since
`d + D < M/2`.

**Multiplicativity on B x B.** Take `x = (g, X, B)` and `y = (g', X', B')` in
`B`.
- The upper left block is `Phi_M(g) Phi_M(g') = Phi_M(g g')`, by Step 0.
- The lower right block is `B^(d) B'^(d) = (B B')^(d)`, by Step 1.
- The upper right block is `Phi_M(g) ev_d(X') + ev_d(X) B'^(d)`.
  - `ev_d(X')` is supported in `[0, d + D] ⊂ [0, M/2]`. So (E0) and (E1)
    give `Phi_M(g) ev_d(X') = g_+ ev_d(X') = ev_d(g X')`.
  - (E5) gives `ev_d(X) B'^(d) = ev_d(X B')`.
  - So the block is `ev_d(g X' + X B')`.
- Hence `Psi(x) Psi(y) = Psi(xy)`.

`Psi(1) = 1` and `B` is symmetric, so each `Psi(x)`, `x in B ∪ BB`, is
invertible and lies in `H`.

**Injectivity on B.** Suppose `Psi(x) = Psi(y)` with `x, y in B`.
- `Phi_M(g) = Phi_M(g')`, so `g = g'` by Step 0.
- `(B - B')^(d) = 0`, so every entry of `B - B'` lies in `T^d F[T]`, by
  Step 1. By the choice of `d` this forces `B = B'`.
- `ev_d(X - X') = 0`, so `X = X'` by (E3) and the choice of `d`.

So `P^T_l` is LEF. MF, soficity, hyperlinearity and `Rad_MF = 1` follow as in
Step 4 of `binary-jacobson-el2-lef-proof`.

**The head.** `x_13(Q) = (1, Q E_11, 1)`. The upper right block of its image
sends `f_1 (x) delta_0` to `(Q e_0, 0) = (e_0, 0) != 0`, because `T e_0 = 0`.
So `Psi(x_13(Q)) != 1` for every `d >= 1` and `M`.

**Two-step.** `W_M ⊕ 0` is stable under the whole image. On it the root
group acts trivially, and `Psi(1, Y, 1) - 1` maps the quotient into
`W_M ⊕ 0` and kills `W_M ⊕ 0`. So `Psi`, restricted to any ball containing
the generators of `jacobson-double-parabolic-two-step-models-kill-head` that
lie in `P^T_2`, is a two-step partial model with the Levi-stable flag
`W_M ⊕ 0 ⊂ W_M ⊕ (F^2 (x) F^d)`.

## Step 3. Both Levis polynomial (statement B)

Let `k, l >= 1`. Replace `Phi_M` by the truncated up-shift. Let `sigma_M` act
on `W_M = F^([0, M])` by `sigma_M e_j = e_(j+1)` for `j < M` and
`sigma_M e_M = 0`.
- `S^a -> sigma_M^a` extends to a ring homomorphism `F[S] -> F[sigma_M]`
  with kernel `S^(M+1) F[S]`.
- Write `g^[M]` for the entrywise image of `g in M_k(F[S])` in
  `End(W_M (x) F^k)`. Then `g -> g^[M]` is a group homomorphism on
  `EL_k(F[S])`.
- **Left equivariance.** Let `w in V_+^k` be supported in `[0, M - a]`. Then
  `(S^a)_+ w = sigma_M^a w`. Hence `g^[M] ev_d(X') = ev_d(g X')` whenever
  every `S`-exponent `a` in `g` satisfies `d + D + a <= M`, using (E4).

**Constants.**
- `D` and `d` are as in Step 2.
- `D_L` is the largest `S`-exponent in the first components of `B ∪ BB`.
- `M > d + D + D_L`, and `M` exceeds every `S`-degree of `g - g'` for `g, g'`
  first components of `B`.

**The model.**

```text
Psi(g, X, B) = [[ g^[M], ev_d(X) ], [ 0, B^(d) ]].
```

It is multiplicative on `B x B`:
- the diagonal blocks, by the two ring homomorphisms;
- the corner, by left equivariance and (E5).

It is injective on `B`:
- `g^[M] = g'^[M]` forces `g = g'` by the choice of `M`;
- the other blocks are as in Step 2.

The head `x_(1,k+1)(Q)` has corner entry `Q e_0 = e_0 != 0`. No import from
the rank-two route is used in this step.

## Step 4. The mirror (statement C)

- `tau` is an anti-automorphism of `J`, so `x -> (x^tau)^t` (entrywise `tau`,
  then transpose) is an anti-automorphism of `M_4(J)`.
- Hence `beta(x) = ((x^tau)^t)^(-1)` is an automorphism of `GL_4(J)`, and so
  is `alpha = w beta w`, with `w` the block swap `[[0, 1], [1, 0]]`.
- For an elementary matrix, `beta(x_ij(a)) = x_ji(-a^tau)`. Conjugating by
  `w` renames the indices by `pi = (13)(24)`. So
  `alpha(x_ij(a)) = x_(pi j, pi i)(-a^tau)`, and `alpha` preserves `EL_4(J)`.
- **The head.** `(ST)^tau = T^tau S^tau = S T`. So `Q^tau = Q`, and
  `alpha(x_13(Q)) = x_(pi 3, pi 1)(-Q) = x_13(-Q)`. In characteristic 2 this
  is the head. In general it is its inverse.
- **Blocks.** `alpha(g, X, B) = ((B^tau)^(t,-1), *, (g^tau)^(t,-1))`,
  because `beta` sends upper block-triangular matrices to lower ones and `w`
  swaps them back. `tau` maps `F[S]` onto `F[T]`, and `EL_2(J)` onto itself.
  - So `alpha` maps `M_2(J) x| (EL_2(F[S]) x EL_2(J))` onto
    `M_2(J) x| (EL_2(J) x EL_2(F[T])) = P^T_2`.
  - It maps the unipotent radical `M_2(J)` onto itself.
- LEF passes to isomorphic groups, and the head is a nonidentity element. So
  the models `Psi o alpha` keep it.

**Generators of the mirror trap.**
- Left: `alpha(x_34(1)) = x_21(1)` and `alpha(x_43(S)) = x_12(T)`.
- Right: `alpha(x_21(1)) = x_34(1)`, `alpha(x_12(S)) = x_43(T)` and
  `alpha(x_12(T)) = x_43(S)`.
- Applying `alpha` to Step 5 below: two-step models of any subgroup of
  `P_(2,2)(J)` containing `x_21(1), x_12(T)` on the left and
  `x_34(1), x_43(T), x_43(S)` on the right kill the head.

## Step 5. The trap needs x_43(S) and nothing else on the right (statement D)

Use the setting of `jacobson-double-parabolic-two-step-models-kill-head`, but
with the smaller set

```text
L_0^S = {x_12(s), x_12(t), x_21(1), x_34(1), x_43(s)},
```

and with `B_*`, `B_0` and partial models defined from `L_0^S` in the same way.
Run `jacobson-double-parabolic-two-step-trap-proof` with these changes.
- **Steps 0 and 1** are unchanged.
- **Steps 2(a) to 2(c)** are unchanged. Step 2(d) is used only for `b = s`,
  and gives `eps(Y_s) = M(s) v`.
- **Step 3.** (R1) is needed only for `s`: `Lambda(s) v = M(s) v`. (R2) and
  (R3) are unchanged, since they use only the left Levi.
- **Step 4** is needed only for the pairs in `L_0^S`.
- **Step 5.** Let `𝓜_s` be the unital algebra generated by `M(s)`, and put
  `Z = 𝓜_s v`.
  - For `m in 𝓜_s`: `Lambda(s) m v = m Lambda(s) v = m M(s) v`, which lies
    in `Z`.
  - `Lambda(t) Lambda(s) m v = m v`.
  - So `Lambda(s)|_Z` is injective. `Z` is finite-dimensional, so it is
    bijective.
  - Write `v = Lambda(s) z` with `z in Z`. Then
    `Lambda(t) v = Lambda(t) Lambda(s) z = z`, so
    `Lambda(s) Lambda(t) v = Lambda(s) z = v`.
  - `Lambda(t)` never had to preserve `Z`, so `x_43(t)` is not needed.
- The conclusion is `eps(Y_q) = 0`, and in the two-step case
  `rho(x_13(q)) = 1`. This holds for the spark group
  `H_mix = M_2(J) x| (EL_2(J) x <x_34(1), x_43(S)>)`.

**The T-oriented set gives no trap.** Let `L_0^T` be `L_0^S` with `x_43(s)`
replaced by `x_43(t)`. All of `L_0^T` and `N_0` lie in `P^T_2`. Step 2
applied to the finite symmetric set `B_0^T` gives an exact partial model
`Psi`.
- `Psi` is two-step for the `Psi(L_0^T)`-stable flag `W_M ⊕ 0`.
- `Psi(x_13(Q)) != 1`.

So the conclusion of the trap is false for `L_0^T`. With `L_0^T` the proof
gives `Lambda(t) v = M(t) v` and (R2). The space `F[M(t)] v` is
`Lambda(t)`-invariant, but that gives no left inverse to invert.

The artifact (Test E(ii)) records a four-line linear counterexample to the
T-side implication. On `F^2` take:
- `v = e_1`;
- `Lambda(s) = (e_1 -> e_2, e_2 -> 0)`;
- `Lambda(t) = (e_2 -> e_1, e_1 -> 0)`;
- `M(t) = 0`.

Then `Lambda(t) v = M(t) v`, `M(t)` commutes with everything, and
`Lambda(t) Lambda(s) v = v`, but `Lambda(s) Lambda(t) v = 0`.

## Step 6. The class kill (statement E)

Let `G` be one of `P^T_l`, `P^(S,T)_(k,l)`, or the mirror group. Suppose an
argument derives `pi(head) = 1` for every representation `pi` of some class
(norm-corona, MF, sofic, LEF-type), using only:
- relations holding in `G`;
- asymptotic multiplicativity of `pi` on finite subsets of `G`.

The models of Steps 2 to 4 are exact on every finite ball. Composed with the
left regular representations of the finite groups `H`, they give a norm-corona
representation of `G` in which `pi(head)` is at distance `sqrt 2` from `1`. So
the argument fails at its final step, `pi(head) = 1`.

The invariant is Step 1: `F[T]` preserves the window `span(e_0, ..., e_(d-1))`,
and `F[S]` does not. Every relation available in `G` is a relation among
left coefficients acting through `Phi_M` or `sigma_M` and right coefficients
acting through `N_d`. Both actions are exact.

## Step 7. Numerical confirmation

`experiments/jacobson-levi-orientation-2026-09-17/check_orientation.py` exits
0. It prints:

```text
A/B  P^T words: product failures 0, distinct elements 290, collisions 0
C    head x_13(Q) nontrivial in model: True
D    control with x_43(S): product failures 47 of 59 (expected > 0)
E(i) F_2^2 exhaustive: 96 hypothesis tuples, 0 violate the trap
E(i) F_2^3 random:     16 hypothesis tuples, 0 violate the trap
E(ii) T-oriented counterexample valid: True
ALL PASS
```

**The run.** `M = 120` and `d = 20`, with 300 random words of length at most
7. The generators are:
- `x_12(a)` and `x_21(a)`, for the 12 coefficients `a` of `coeffs(2)` from the
  w9 script;
- the four column roots `x_(i, 2+c)(a)`;
- the right roots `x_34(p)` and `x_43(p)`, for `p in {1, T, T^2, T+1}`.

**The checks.**
- Each product of images is compared with the model of the exact product in
  `P^T_2`.
- Control D appends a column root followed by `x_43(S)`, modelled by the
  truncated up-shift. The product fails in 47 of 59 words, as Step 1 predicts.
- Test E(i) checks the linear algebra of Step 5 with the S-side hypotheses.
  - The search is exhaustive over `F_2^2`.
  - Over `F_2^3` it is random, and few tuples meet the hypotheses. That part
    is a spot check only; the proof of Step 5 is the argument.
