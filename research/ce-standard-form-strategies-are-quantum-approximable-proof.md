---
rg: 2
id: ce-standard-form-strategies-are-quantum-approximable-proof
kind: route
title: Lift the projections and one bounded density element to matrices and read the correlation off a vectorized matrix
target: ce-standard-form-strategies-are-quantum-approximable
requires: []
---

Notation as in the target. `C_qa` is closed, and for a contraction `T`,
`|<T xi,xi> - <T xi',xi'>| <= 2 ||xi-xi'||`. It therefore suffices to treat
`xi = eta Omega` with `eta in M` and `tau(eta^* eta)=1`, since such vectors
are dense in the unit sphere.

**Step 1 (Bob moved to the left algebra).** Put `R_(y,b) = J Q_(y,b) J`.
This is a projection-valued measure in `M`. For `x,z in M` we have
`J z Omega = z^* Omega`, hence `J x J (z Omega) = z x^* Omega`. So

```text
p(a,b|x,y) = < P_(x,a) eta R_(y,b) Omega , eta Omega >
           = tau( eta^* P_(x,a) eta R_(y,b) ).                  (SFP1)
```

**Step 2 (lifting).** Let `theta : M -> prod_omega (M_(n_k), tr)` be a
trace-preserving unital star-homomorphism. Fix `x`, let `m=|A|`,
`zeta=exp(2 pi i/m)`, and `U_x = sum_a zeta^a P_(x,a)`, a unitary with
`U_x^m=1`.
- Lift `theta(U_x)` to unitaries `u_k` (lift to a bounded sequence, then take polar parts). Then `||u_k^m - 1||_2 -> 0` along `omega`.
- Let `f` send a point of the circle to a nearest `m`-th root of unity (a Borel choice). If `lambda = exp(i s)` is at arc distance `delta <= pi/m` from its nearest root, then `|lambda^m - 1| = 2 sin(m delta/2) >= (2/pi) m delta`. Hence `|f(lambda)-lambda| <= (pi/2m) |lambda^m-1|`.
- Functional calculus for the normal matrix `u_k` gives `||f(u_k)-u_k||_2 <= (pi/2m)||u_k^m-1||_2 -> 0`. So `v_k=f(u_k)` also lifts `theta(U_x)` and satisfies `v_k^m = 1` exactly.
- The matrices `p_(x,a,k) = (1/m) sum_j zeta^(-aj) v_k^j` form an exact projection-valued measure lifting `theta(P_(x,a))`.

In the same way, lift each `R_(y,b)` to exact measures `r_(y,b,k)`. Lift
`theta(eta)` to a bounded sequence `h_k`, so that `tr(h_k^* h_k) -> 1`.

**Step 3 (vectorization).** In `C^n (x) C^n` put `vec(E_ij)=e_i (x) e_j`.
Then `(X (x) Y^T) vec(H) = vec(X H Y)` and `<vec(G),vec(H)> = Tr(H^* G)`.
Let `w_k = vec(h_k)/||vec(h_k)||`, Alice's measurement be `p_(x,a,k) (x) 1`
and Bob's be `1 (x) r_(y,b,k)^T`, which is again a projection-valued measure.
These give finite-dimensional quantum correlations

```text
p_k(a,b|x,y) = tr( h_k^* p_(x,a,k) h_k r_(y,b,k) ) / tr( h_k^* h_k ).   (SFP2)
```

**Step 4 (limit).** The lifts are bounded, the quotient map is
multiplicative, and `theta` preserves the trace. So along `omega` the
numerator of `(SFP2)` tends to `tau(eta^* P_(x,a) eta R_(y,b))` and the
denominator tends to 1. By `(SFP1)`, `p_k -> p` along `omega` in the
finite-dimensional space of correlations. Hence `p` lies in the closure
`C_qa`.

**Amplified form.** First, *positive operator-valued measures lift*. Let
`a_1,...,a_m >= 0` in the ultraproduct with `sum a_i = 1`.
- Lift each `a_i` to a positive contraction `x_(i,k)`, taking the positive part of the self-adjoint part and cutting at 1.
- Put `S_k = sum_i x_(i,k)`, so `||S_k - 1||_2 -> 0`, and `T_k = max(S_k, 1/2)^(-1/2)`, so `||T_k|| <= sqrt 2` and `||T_k - 1||_2 <= C ||S_k - 1||_2`.
- Put `y_(i,k) = T_k x_(i,k) T_k` for `i < m`, and give `y_(m,k)` the remainder `T_k x_(m,k) T_k + (1 - T_k S_k T_k)`. The remainder is positive and supported where `S_k < 1/2`, so its two-norm is at most `2||S_k-1||_2`.
- The `y_(i,k)` form exact positive operator-valued measures lifting the `a_i`.

With this in place of the unitary rounding, Steps 1-4 apply verbatim to
positive operator-valued measures, because the transpose of a positive
matrix is positive.

Second, *the amplification*. Let `N_2 = M_F (x) M (x) M_G`, which is Connes
embeddable, with
`L^2(N_2) = (C^F (x) C^F) (x) L^2(M) (x) (C^G (x) C^G)`.
- `M_F` acts on the left `C^F` leg.
- The commutant of the left action of `M_G` on `C^G (x) C^G` is `1 (x) M_G`, acting on the right leg.
- So Alice's `M_F(M)`, placed on the left `C^F` leg and `L^2(M)`, lies in `N_2`.
- Bob's `M' (x) M_G`, placed on `L^2(M)` and the right `C^G` leg, lies in `N_2'`.
- Embed `xi` by inserting fixed unit vectors in the left `C^G` leg and the right `C^F` leg. Neither player acts on those legs, so the correlation is unchanged.

The unamplified statement for `N_2` gives the amplified one.

The corollary for groups follows because hyperlinearity of `Lambda` is
Connes embeddability of `L(Lambda)` with its canonical trace. This is the
same standard identification used in `non-hyperlinear-from-group-factor-bcs-model`.
