---
rg: 2
id: thompson-f-factorization-iff-ucp-models-separate-proof
kind: route
title: Subadditive Stinespring defect, the face of amenable traces, and the character simplex of F
target: thompson-f-factorization-iff-ucp-models-separate
requires:
  - thompson-f-character-simplex
---

Write `A = C*(F)`. For a matrix `z` in `M_n`, `||z||_2 = tr_n(z^*z)^(1/2)`, and `||.||_HS` is the
unnormalized Hilbert--Schmidt norm.

**External inputs**, both from N. P. Brown, *Invariant means and finite representation theory of
C*-algebras*, Mem. AMS 184 (2006), as already used in `literal-fp-via-llp` and
`factorization-semidirect-permanence-proof`.
- **(B1)** Theorem 3.1.6. For a trace `tau` on a unital separable C*-algebra `A`, the following are
  equivalent:
  - `tau` is amenable;
  - there are ucp maps `phi_k : A -> M_(n_k)` with `||phi_k(xy) - phi_k(x)phi_k(y)||_2 -> 0` and
    `tr o phi_k -> tau` pointwise;
  - the functional `x (x) y^op -> tau(xy)` is continuous for the minimal norm on `A (.) A^op`.
- **(B2)** Theorem 4.1.9 (Kirchberg). A discrete group has the factorization property iff its canonical
  trace on `C*(Gamma)` is amenable.

## Step 1. Forms 2 and 3 are the same data

A ucp map `phi : A -> M_n` has a Stinespring dilation `phi = V^* pi(.) V`, where `pi` is a unitary
representation of `F` on `K` and `V : C^n -> K` is an isometry. Put `P = VV^*`. Conversely any `(pi, P)`
with `rank P = n` defines such a `phi`. For `g in F`:

```text
||P pi(g) P||_HS^2 = n tr_n(phi(g)phi(g)^*),
||P pi(g)(1-P)||_HS^2 = ||(1-P) pi(g) P||_HS^2 = n - ||P pi(g) P||_HS^2.        (S1)
```

So, with `D(g) = ||P pi(g)(1-P)||_HS / sqrt n`,

```text
1 - tr_n(phi(g)phi(g)^*) = D(g)^2,   ||[pi(g),P]||_HS^2 = 2 n D(g)^2,   D(g^-1) = D(g).   (S2)
```

Moreover `[P pi(a) P, P pi(b) P] = V [phi(a),phi(b)] V^*`, so its HS norm is
`sqrt n ||[phi(a),phi(b)]||_2`. Hence 2 and 3 are equivalent, with `delta` changed to `sqrt(2 delta)`.

## Step 2. The defect is subadditive and controls multiplicativity

Split `P pi(gh)(1-P) = P pi(g)(1-P) pi(h)(1-P) + P pi(g) P pi(h)(1-P)`. Then

```text
D(gh) <= D(g) + D(h),   so   D(g) <= |g|_S max(D(a), D(b))                    (S3)
```

for word length over `S = {a^+-1, b^+-1}`. For `g in F` and `x in A`,
`phi(gx) - phi(g)phi(x) = V^* pi(g)(1-P) pi(x) V`, and `||V^* T||_HS = ||P T||_HS`. So

```text
||phi(gx) - phi(g)phi(x)||_2 <= D(g) ||x||.                                   (S4)
```

Suppose `phi_k` are ucp with `D_k(a), D_k(b) -> 0`. By (S3), (S4), linearity on `C[F]`, and
`||phi_k(z)||_2 <= ||z||`, we get `||phi_k(yx) - phi_k(y)phi_k(x)||_2 -> 0` for all `x, y in A`.
Fix a free ultrafilter and put `tau = lim tr o phi_k`.
- `tau` is tracial, since `|tr_n(z)| <= ||z||_2` and `tr(phi(x)phi(y)) = tr(phi(y)phi(x))`.
- `tau` is amenable by (B1). Choose a subsequence converging on a countable dense set, which is possible
  by separability.

## Step 3. The commutator norm reads off the regular weight

Let `phi_k` be ucp and asymptotically multiplicative in `||.||_2` with `tr o phi_k -> tau`. Using
`phi(g)^* = phi(g^-1)`, `||T z||_2 <= ||T|| ||z||_2` and (S4), products of four `phi_k`-images of group
elements have the same limiting trace as the image of the product. So

```text
||[phi_k(a), phi_k(b)]||_2^2 -> 2 - 2 Re tau(b^-1 a^-1 b a).                  (S5)
```

By `thompson-f-character-simplex`, `tau|_F = t tau_reg + (1-t) chi` with `chi` a mixture of characters
through `ab : F -> Z^2`, hence `chi = 1` on `F'`. States on `C*(F)` correspond linearly to positive
definite functions, so `tau = t tau_reg + (1-t) tau_chi` as traces on `A`. Since `a, b` generate the
nonabelian group `F`, `b^-1 a^-1 b a` is a nontrivial element of `F'`, and

```text
lim ||[phi_k(a), phi_k(b)]||_2^2 = 2t.                                        (S6)
```

## Step 4. Amenable traces form a face

Let `sigma` be a trace on `A` with GNS data `(pi_sigma, L^2(A,sigma), xi)`.
- Right multiplication `rho(y^op) x^ = (xy)^` is bounded, since
  `sigma(y^* x^* x y) = sigma(x y y^* x^*) <= ||y||^2 sigma(x^* x)`. It is a representation of `A^op`
  commuting with `pi_sigma`.
- So `mu_sigma(x (x) y^op) = sigma(xy) = <pi_sigma(x) rho(y^op) xi, xi>` is a positive functional on
  `A (x)_max A^op`.

Let `J` be the kernel of `A (x)_max A^op -> A (x)_min A^op`. By (B1), `sigma` is amenable iff
`mu_sigma(J) = 0`.

If `tau = t tau_1 + (1-t) tau_2` with `0 < t <= 1` and `tau` amenable, then
`mu_tau - t mu_(tau_1) = (1-t) mu_(tau_2) >= 0`. So `0 <= t mu_(tau_1)(x) <= mu_tau(x) = 0` for
`x in J^+`. A closed ideal is spanned by its positive part, so `mu_(tau_1)(J) = 0` and `tau_1` is
amenable.

## Step 5. Conclusion

- **1 => 2.** (B2) gives ucp `phi_k` with `tr o phi_k -> tau_reg` that are asymptotically multiplicative.
  Then `1 - tr(phi_k(s)phi_k(s)^*) -> 0`, and (S5) with `tau_reg(b^-1 a^-1 b a) = 0` gives commutator norms
  tending to `sqrt 2`. So any `epsilon < sqrt 2` works.
- **2 => 1.** Take `phi_k` with `delta = 1/k`, so `D_k(s)^2 < 1/k` by (S2). Step 2 makes the limit trace
  `tau` amenable, and (S6) gives `2t >= epsilon^2 > 0`. Step 4 makes `tau_reg` amenable, and (B2) gives
  the factorization property.
- **2 <=> 3** is Step 1.
