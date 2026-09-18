---
rg: 2
id: jacobson-mirror-head-swap-kill-proof
kind: route
title: Swap the head across the wall by one finitary involution and use unitary invariance of the trace norm
target: jacobson-mirror-head-swap-kills-ambient-approximations
requires:
  - jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group
  - untwisted-bilateral-symbol-enrichment-is-lef
---

Notation as in the target. `||X||_2 = (tr_d(X* X))^(1/2)` with `tr_d(1) = 1`.
This norm is invariant under left and right multiplication by unitaries.

## Step 1. The two heads and the swap

`J` acts on `V_+` by `S e_k = e_(k+1)`, `T e_0 = 0` and `T e_(k+1) = e_k`.
- Then `ST e_0 = 0` and `ST e_(k+1) = e_(k+1)`.
- So `Q = 1 - ST` is the projection onto `F_2 e_0` along the other basis vectors.
- `x_13(Q) - 1` sends `e_(k,3)` to `e_(0,1)` when `k = 0`, and kills every other basis vector.
- Hence `w = 1 + e_(0,1) (x) e*_(0,3)`.

On `V_-` the same formulas hold in the mirror basis `e'_k = e_(-1-k)`, so
`w' = 1 + e_(-1,1) (x) e*_(-1,3)`.
- The pair `(1, x_13(Q))` lies in `P`, because the symbol of `x_13(Q)` is `1`, the symbol of the identity.
- It lies in `{1} x L_- = ker pi`.
- Likewise `(x_13(Q), 1)` lies in `P`, and `pi(w) = x_13(Q)` is the head. The head is nontrivial in `EL_n(J)` because it acts nontrivially on `V_+^n`.

The swap `s` exchanges `e_(0,i)` and `e_(-1,i)` for `i = 1..n`. It is a
finitary permutation matrix, so `s = s^(-1)` lies in `GL_fin(W) <= H_bi`.
Since `s e_(-1,1) = e_(0,1)` and `e*_(-1,3) o s^(-1) = e*_(0,3)`:

```text
s w' s^(-1) = 1 + (s e_(-1,1)) (x) (e*_(-1,3) o s^(-1)) = 1 + e_(0,1) (x) e*_(0,3) = w.
```

Note that `s` is not in `P`, because it does not preserve `V_+`. Inside `P`
the heads are not conjugate: `w'` lies in the normal subgroup `L_-` and `w` does not.

## Step 2. The estimate (HS)

Write `a = gamma(s)`, `b = gamma(s^(-1))`, `c = gamma(w')`. By hypothesis:
- `||gamma(w' s^(-1)) - c b||_2 <= eps`;
- `||gamma(s w' s^(-1)) - a gamma(w' s^(-1))||_2 <= eps`;
- `||a b - gamma(1)||_2 <= eps`, with `gamma(1) = 1`.

Since `a` is unitary, the first two give `||gamma(w) - a c b||_2 <= 2 eps`. Then

```text
||a c b - 1||_2 <= ||a (c - 1) b||_2 + ||a b - 1||_2 <= ||c - 1||_2 + eps,
```

using that `b` is unitary. Adding the two bounds gives (HS).

## Step 3. Consequence 1

Suppose `||alpha_k(pi p) - gamma_k(p)||_2 -> 0` for `p in {w, w'}`, where the
`gamma_k` are asymptotic homomorphisms of `K`. Then `eps_k -> 0` on the three
pairs in Step 2.
- `gamma_k(w') -> alpha_k(1) = 1`.
- By (HS), `gamma_k(w) -> 1`, so `alpha_k(pi w) -> 1`.
- A hyperlinear approximation has `tr alpha_k(g) -> 0` for `g != 1`. Hence `||alpha_k(g) - 1||_2^2 = 2 - 2 Re tr alpha_k(g) -> 2` for `g = pi w != 1`, a contradiction.
- If `alpha_k(1) != 1`, replace `1` by `alpha_k(1)`. Asymptotic multiplicativity gives `||alpha_k(1) - 1||_2 -> 0` for unitary models, so nothing changes.

**Other metrics.** A permutation `p` has
`||p - 1||_2^2 = 2 (fraction of points moved)`, so sofic approximations are a
special case. For a linear-sofic or rank model, `rho(X) = rank(X - 1)/d` is
invariant under conjugation and subadditive. The same three-line argument gives
`rho(gamma(w)) <= rho(gamma(w')) + 3 eps` in that metric.

## Step 4. Consequence 2 (periodic models)

`untwisted-bilateral-symbol-enrichment-is-lef` reduces the `k`-coordinate mod `m`.
- For `m` larger than the supports involved, `iota_m` sends finitary operators to the same matrices on `F_2^(Z/m x {1..n})`.
- So `iota_m(w)` and `iota_m(w')` are transvections of `GL_(N_m)(F_2)`, with `N_m = nm >= 3`.
- All transvections of `GL_N(F_2)` are conjugate, for example by `iota_m(s)`.
- A class function takes equal values on them. Any `psi_m o iota_m` restricted to `P` therefore gives `w` and `w'` the same trace. Such a model cannot send `w'` to `1` while sending `w` to trace near `0`.

## Step 5. Consequence 3 (normal closure)

Every `g in GL_fin(W)` is a finite product of transvections. Over `F_2`, every
transvection of `GL_fin(W)` is conjugate to `w'` by an element of `GL_fin(W)`.
- Apply (HS), with `s` replaced by these fixed conjugators, then subadditivity over the fixed factorization.
- The result: an asymptotic homomorphism of `H_bi` that tends to `1` at `w'` tends to `1` at every fixed element of `GL_fin(W)`, in particular on `L_+ x L_-`.
- Its restriction to `P` is then asymptotically constant on cosets of `L_+ x L_-`.
- By (MQ1), `P/(L_+ x L_-)` is `SL_n(A)`, embedded diagonally.

QED.
