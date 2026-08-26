---
rg: 2
id: abstract-unitary-embedding-upgrades-to-hyperlinear-proof
kind: route
title: Direct-sum with the identity, then tensor-amplify; Connes embeddability supplies unitary microstates
target: abstract-unitary-embedding-upgrades-to-hyperlinear
requires: []
---

Throughout, `tr` is the normalized trace on `M_d`, `||a||_2^2 = tr(a^* a)`, and
`hsDistSq(u,v) = ||u - v||_2^2 = 2 - 2 Re tr(v^* u)` for unitaries.

**(1) => (2).**  Canonical models separated to `2 - epsilon` are separated to
any fixed `delta < 2` once `epsilon <= 2 - delta`
(`isHyperlinearWeak_of_isHyperlinear`).

**(2) => (1).**  Fix a finite `F` and a target `epsilon' > 0`.  Choose `k` with
`2 (1 - delta/4)^(k/2) <= epsilon'`, then `epsilon > 0` with
`k^2 epsilon / 2 <= epsilon'`, and take a `(F, epsilon)`-model `u` of
separation `delta` on `M_d`.  Put

```text
v_g = u_g (+) 1_d in U(2d),        w_g = v_g^(tensor k) in U((2d)^k).
```

*Multiplicativity.*  `v_(gh) - v_g v_h = (u_(gh) - u_g u_h) (+) 0`, so
`||v_(gh) - v_g v_h||_2^2 = epsilon/2` at most.  For unitaries `a_1..a_k`,
`b_1..b_k`, telescoping `a_1 (x) ... (x) a_k - b_1 (x) ... (x) b_k` through
`k` one-factor changes and using `||x (x) y||_2 = ||x||_2 ||y||_2` and
unitary invariance gives `||a^(tensor k) - b^(tensor k)||_2 <= k ||a - b||_2`.
Hence `||w_(gh) - w_g w_h||_2^2 <= k^2 epsilon / 2 <= epsilon'`.

*Separation.*  For `g != h` in `F` put `z = tr(u_h^* u_g)`.  Then `|z| <= 1`
and, by the separation hypothesis, `Re z <= 1 - delta/2`.  Now
`tr(v_h^* v_g) = (z + 1)/2`, and

```text
|(z+1)/2|^2 = (|z|^2 + 2 Re z + 1)/4 <= (2 + 2 Re z)/4 <= 1 - delta/4.
```

Traces multiply under tensor products, so
`|tr(w_h^* w_g)| = |(z+1)/2|^k <= (1 - delta/4)^(k/2)` and
`hsDistSq(w_g, w_h) = 2 - 2 Re tr(w_h^* w_g) >= 2 - 2(1 - delta/4)^(k/2)
>= 2 - epsilon'`.  So `w` is a canonical `(F, epsilon')`-model.  The phase
collapse recorded in `tensorPow_phase_collapse` cannot occur because a unitary
of the form `u (+) 1` is scalar only when `u = 1`.

**(1) => (3).**  Canonical models assemble, along a free ultrafilter, into a
trace-preserving embedding of `L(G)` into `R^omega`, which restricts to an
injective homomorphism `G -> U(R^omega)`.  (`R^omega` itself is the Connes
embeddable algebra of (3).)

**(3) => (2).**  Let `pi : G -> U(N)` be injective, `N` Connes embeddable.
Replace `pi` by `psi(g) = pi(g) (+) 1 in U(M_2(N))`; `M_2(N)` is Connes
embeddable and `psi(g)` is scalar only for `g = e`, so `|tau(psi(g)^* psi(h))|
< 1` whenever `g != h` (a unitary has trace of modulus one exactly when it is a
scalar).  Fix a finite `F`.  Choose `k` with
`|tau(psi(g)^* psi(h))|^k <= 1/2` for all `g != h` in `F`, and put
`phi = psi^(tensor k) : G -> U(N^(tensor-bar k))`, again a homomorphism into a
Connes embeddable algebra, with `Re tau(phi(g)^* phi(h)) <= 1/2`, i.e.
`||phi(g) - phi(h)||_2^2 >= 1` for `g != h` in `F`.  Connes embeddability
supplies, for the finitely many unitaries `phi(g)`, `g in F union F.F`, matrix
unitaries `U_g in U(d)` whose `*`-moments of degree at most `4` approximate
those of the `phi(g)` to any prescribed accuracy (approximating matrices can be
taken unitary by polar decomposition, since the approximants of a unitary are
close to unitary in `||.||_2`).  Then `||U_(gh) - U_g U_h||_2^2` is close to
`||phi(gh) - phi(g)phi(h)||_2^2 = 0` and `||U_g - U_h||_2^2` is close to
`||phi(g) - phi(h)||_2^2 >= 1`.  This is an `(F, epsilon)`-model with
separation `delta = 1/2`, for every `F` and `epsilon`, i.e. (2) with
`delta = 1/2`.

The three implications close the cycle.
