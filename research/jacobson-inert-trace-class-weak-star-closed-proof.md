---
rg: 2
id: jacobson-inert-trace-class-weak-star-closed-proof
kind: route
title: Restrict to the mirror kernel, read the mirror mass off the Bauer simplex of GL(infinity,2), bound every nontrivial rank character's average by Burnside, and pass the uniform bound through the GNS estimate
target: jacobson-inert-trace-class-is-weak-star-closed
requires:
  - jacobson-mirror-exact-trace-part-is-multiplicative
  - gl-infinity-f2-trace-simplex-is-extended-naturals
---

Notation as in the target. Section references `Step k` of `jacobson-mirror-exact-trace-part-multiplicative-proof`,
labelled (MX1)-(MX4), are to the established claim `jacobson-mirror-exact-trace-part-is-multiplicative`, whose
route that is.

## Step 1. The Burnside bound

**Lemma 1.** Let `M >= 2`, `G = GL_M(F_2)` and `sigma_k(g) = 2^(-k rank(g-1))`, with `sigma_∞ = delta_e`. Then

```text
0 <= avg_(g in G) sigma_k(g) <= 12 * 2^(-M)      for every k in {1, 2, ..., ∞}.
```

*Proof.*

**Nonnegativity.** `sigma_k|_G` is positive definite, so its average is `<p xi, xi> >= 0`, where `p` is the
projection onto the invariants in a GNS space.

**The case `k = ∞`.** The average is `1/|G|`. For `M >= 2`,
`|G| >= (2^M - 1)(2^M - 2) >= 2^M`, so the average is at most `2^(-M)`.

**Finite `k >= 1`: counting orbits.**
- Let `G` act on `X = Hom(F_2^k, F_2^M)` by `phi -> g phi`.
- The fixed points of `g` are the maps with image in `ker(g-1)`. So there are
  `|ker(g-1)|^k = 2^(k(M - rank(g-1)))` of them, and `sigma_k(g) = |Fix_X(g)| / |X|`.
- By Burnside's lemma, `avg_G sigma_k = (number of G-orbits on X) / 2^(kM)`.
- Two maps lie in one orbit iff they have the same kernel.
  - "Only if" is clear.
  - For "if": let `ker phi = ker psi = K`. Then `phi` and `psi` induce injections of `F_2^k/K` onto subspaces `U` and
    `U'` of `F_2^M` of equal dimension.
  - Any linear isomorphism `U -> U'` extends to some `g in G`, and then `g phi = psi`.
- So the orbits correspond to the subspaces `K <= F_2^k` of codimension `c <= min(k, M)`.

**Finite `k >= 1`: the estimate.**
- There are `binom(k,c)_2` subspaces of codimension `c`.
- `binom(k,c)_2 = prod_(i=0)^(c-1) (2^(k-i) - 1)/(2^(c-i) - 1) <= 2^(c(k-c)) prod_(i=1)^c (1 - 2^(-i))^(-1)`
  `<= 4 * 2^(c(k-c))`, because `prod_(i >= 1) (1 - 2^(-i))^(-1) < 3.47`.
- Write `a(c) = c(k-c) - kM`.
  - For `c = 0`: `a = -kM <= -M`.
  - For `1 <= c <= min(k,M)`: `a = -k(M-c) - c^2 <= -c(M-c) - c^2 = -cM`, using `k >= c` and `M - c >= 0`.
- Hence

  ```text
  avg_G sigma_k <= 4 ( 2^(-M) + sum_(c >= 1) 2^(-cM) ) <= 4 ( 2^(-M) + 2 * 2^(-M) ) = 12 * 2^(-M).
  ```

QED.

This is the estimate (5.2) of the established class-kill, whose sharper constant is `8`. The constant `12` is
proved here from scratch, so nothing depends on the constant.

## Step 2. Mirror mass is the trivial weight (Part 2)

Let `tau in Tr(P)`.

**The measure.** `tau|_(L_-)` is normalized, positive definite, and invariant under conjugation by
`L_- <= P`. So it is a trace of `L_-`.
- `L_- = GL_fin(V_-)`, with `V_-` of countable basis `{e_s : s in Z_(<0) x {1..n}}`.
- By the "any countable index set" clause of `gl-infinity-f2-extreme-characters-are-rank-powers`, as used in
  `gl-infinity-f2-trace-simplex-is-extended-naturals`, `L_- ≅ GL(∞,2)`. Here `rank(g-1)` is intrinsic, so the
  identification carries `sigma_k` to `sigma_k`.
- By Part 1 of `gl-infinity-f2-trace-simplex-is-extended-naturals` (Bauer simplex), there is a unique
  `mu_tau in Prob(N̄)` with

  ```text
  tau|_(L_-) = Phi(mu_tau) = sum_(k in N̄) mu_tau({k}) sigma_k.
  ```

- The map `tau -> mu_tau` is weak*-continuous. It is the composition of restriction, which is continuous, with
  `Phi^(-1)`, which is continuous because `Phi` is an affine homeomorphism.

**The averages.** For `g in F_j`, `rank(g-1)` on `V_-` equals the rank on `span(S_j)`, because `g` fixes the other
basis vectors. So `sigma_k|_(F_j)` is the rank character of `GL_(nj)(F_2)`. The sum is a countable convex sum of
bounded functions, so it commutes with the finite average:

```text
avg_(y in F_j) tau(y) = mu_tau({0}) + sum_(k in [1,∞]) mu_tau({k}) avg_(F_j) sigma_k.
```

By Lemma 1 with `M = nj >= 2`, the second term lies in `[0, eps(nj)]`.

**The limit.**
- By (MX1), in the form "`avg_(F_j) tau = <p_j xi, xi>` decreases to `m(tau)`" (Step 1 and Step 5.1 of the
  class-kill's route), the left side tends to `m(tau)`.
- The right side tends to `mu_tau({0})`.
- So `m(tau) = mu_tau({0})`, and the first inequality of (U) holds:

  ```text
  0 <= avg_(F_j) tau - m(tau) <= eps(nj).                                                 (U1)
  ```

**Continuity of `m`.** `{0}` is clopen in `N̄`, so `mu -> mu({0}) = ∫ 1_{0} d mu` is weak*-continuous on
`Prob(N̄)`. Hence `m` is weak*-continuous on `Tr(P)`. This improves the upper semicontinuity recorded in the
class-kill.

## Step 3. The GNS estimate (second inequality of (U))

Let `(pi, H, xi)` be a GNS triple for `tau`, let `p_j = avg_(y in F_j) pi(y)` be the projection onto `H^(F_j)`, and
let `z` be the projection onto `H^(L_-)`. By (MX1), `z <= p_j`, `p_j -> z` strongly, and
`tau^flat(g) = <z pi(g) xi, xi> = <pi(g) xi, z xi>`.

**The estimate.**

```text
avg_(y in F_j) tau(y g) = <p_j pi(g) xi, xi> = <pi(g) xi, p_j xi>,
|avg_(F_j) tau(y g) - tau^flat(g)| = |<pi(g) xi, (p_j - z) xi>| <= ||(p_j - z) xi||,
||(p_j - z) xi||^2 = <(p_j - z) xi, xi> = avg_(F_j) tau - m(tau) <= eps(nj),
```

- The last equality holds because `p_j - z` is a projection, since `z <= p_j`.
- The final bound is (U1).

This proves (U), which is Part 1 of the target. The bound is uniform in `tau` and in `g`. QED Part 1.

## Step 4. Continuity and closure (Part 3)

**Continuity.** Fix `g`. For each `j`, the map `tau -> avg_(F_j) tau(y g)` is a finite average of evaluations, so
it is weak*-continuous on `Tr(P)`. By (U) these maps converge to `tau -> tau^flat(g)` uniformly on `Tr(P)`. A
uniform limit of continuous functions is continuous.

**`N` is closed.** `N = bigcap_(x in L_+) {tau : tau^flat(x) - tau^flat(1) = 0}` is an intersection of zero sets
of continuous functions. The other closure properties are (MX4).1.

**The closed inert hull.** By (MX4).2 and (MX4).3, `N` contains:
- `delta_P`;
- every trace with `m = 0`;
- every restriction from an overgroup containing the finitary site permutations.

It remains to treat finite-dimensional traces.
- Let `rho : P -> U(d)` be a unitary representation and `tau = tr_d o rho`.
- By Lemma 0 of the class-kill's route, which is part of the established claim (MX3), `L_-` and `L_+ ≅ L_-` have no
  nontrivial finite-dimensional unitary representation. So `rho` is trivial on `L_-` and on `L_+`.
- Then every `F_j`-average of `tau` is `1`, so `m(tau) = 1` and `tau^flat = tau`.
- And `tau = 1` on `L_+`, so `tau in N`.

So `N` is a weak*-closed, convex, product-closed set containing all four generating families. It therefore
contains their closed inert hull. QED Part 3.

## Step 5. The gap (Part 4)

**`h_j` is self-adjoint.**
- In `C[P]`, `y^* = y^(-1)`, and the average over the group `F_j` is invariant under `y -> y^(-1)`. So
  `(avg_(F_j) y)^* = avg_(F_j) y`.
- `w` is an involution, since `x_13(Q)^2 = x_13(2Q) = 1` in characteristic 2. So `(y w)^* = w y^(-1)`.
- Hence `h_j^* = h_j`.

**The value.** For any trace, `tau(w y^(-1)) = tau((y w)^(-1)) = conj(tau(y w))`, so

```text
tau(h_j) = avg_(F_j) tau(y) - Re avg_(F_j) tau(y w).
```

**Hyperlinear case.**
- If `E` is hyperlinear, `delta_E` is CE, and so is `tau_0 = delta_E o q` (Step 2 of the class-kill's route).
- For `y in F_j <= L_- = ker q`: `tau_0(y) = 1`, and `q(y w) = q(w) != 1`, because `q` is injective on `L_+`. So
  `tau_0(y w) = 0`.
- Hence `tau_0(h_j) = 1` and `Gamma_j >= 1`.

**Non-hyperlinear case.**
- If `E` is not hyperlinear, then by (MX2) every CE trace `tau` of `P` has `tau^flat` constant on `L_+`. So
  `tau^flat(w) = tau^flat(1) = m(tau)`.
- By (U):
  - `avg_(F_j) tau(y) <= m(tau) + eps(nj)`;
  - `Re avg_(F_j) tau(y w) >= Re tau^flat(w) - eps(nj)^(1/2) = m(tau) - eps(nj)^(1/2)`.
- Hence `tau(h_j) <= eps(nj) + eps(nj)^(1/2) = delta(nj)` for every CE trace, and `Gamma_j <= delta(nj)`.

**The threshold.**
- `delta(6) = 12/64 + (12/64)^(1/2) = 0.1875 + 0.4331 < 1`.
- `delta` decreases in `M`, so `delta(M) < 1` for all `M >= 6`.
- For `M >= 6` the two cases are separated by the gap `(delta(M), 1)`. This gives the stated equivalence: if
  `tau(h_j) > delta(nj)` for some CE `tau`, the non-hyperlinear case is excluded.

**Numerics for `n = 20`, `j = 1`.**
- `eps(20) = 12 * 2^(-20) < 1.15 * 10^(-5)`.
- `eps(20)^(1/2) = 12^(1/2) / 1024 < 0.00339`.
- So `delta(20) < 0.0035`.

QED Part 4.

## Step 6. Why this is the death step of the limit survivor, and what survives

**The death step.**
- The class-kill's survivor was: a pointwise limit `tau = lim tau_i` of traces in `N` might have
  `m(tau) > lim m(tau_i)`. That would create mirror-exact mass at the limit, possibly charging the head.
- Lemma 1 rules this out uniformly.
  - At level `F_j`, the only "fake" invariant mass, meaning `F_j`-invariant but not `L_-`-invariant, is carried by
    nontrivial rank characters of `L_-`.
  - Each such character has `F_j`-average at most `12 * 2^(-nj)`, whatever `k`.
  - So mass cannot hide at ever larger `k` and reappear in the limit.
- The mechanism is the isolation of `0` in the extended naturals: the trivial character of `GL(∞,2)` is not a
  limit of nontrivial ones. That is precisely what Skudlarek's list, now imported, guarantees.

**What survives.**
- CE traces of `P` that are not in the closed inert hull.
- Concretely: limits of traces of genuinely approximate (non-exact) finite-dimensional representations of `P` that
  are not restrictions from a finitary-site overgroup and not built from the generating families. Such a limit must
  satisfy `tau(h_1) > 0.0035` (for `n = 20`).
- By (U), in any such limit the head must move vectors that are invariant under all of `L_-`, not merely under
  `F_1`, up to trace `12 * 2^(-20)`.
- No construction of this kind is known. The hole stays OPEN in both directions. QED.
