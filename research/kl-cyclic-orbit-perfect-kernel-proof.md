---
rg: 2
id: kl-cyclic-orbit-perfect-kernel-proof
kind: route
title: Reidemeister--Schreier, the finite conjugacy orbit, and simplicity
target: kl-cyclic-orbit-perfect-kernel
requires: [degree-kernel-abelianization-is-infinite-cyclic, kl-simple-failure-leaves-only-the-cyclic-quotient]
artifacts:
  - research/artifacts/kl-cyclic-orbit-audit-2026-08-24.md
---

Use the Reidemeister--Schreier transversal

    1, t, ..., t^(m-1)

for `N_m` in `F`.  The coefficient Schreier generators give the conjugate
free factors `S_i=t^i S t^(-i)`, the closing transition gives `z=t^m`, and
there are no relations joining distinct factors.  Hence

    N_m = S_0 * ... * S_(m-1) * <z>.

Conjugation by `t` shifts the factors, with

    alpha(S_(m-1)) = z S_0 z^(-1),     alpha(z)=z,

so `alpha^m=Ad(z)`.

Because `N_m` is normal in `F`, the `F`-normal closure of `w in N_m` is the
`N_m`-normal closure of all `alpha^k(w)`, `k in Z`.  But

    alpha^(k+m)(w) = z alpha^k(w) z^(-1),

so every such conjugate is `N_m`-conjugate to one of
`w_0,...,w_(m-1)`.  This proves the equality of normal closures.  Since that
subgroup lies in `N_m`, quotienting the short exact sequence
`1 -> N_m -> F -> C_m -> 1` gives

    1 -> Q_w -> H_w -> C_m -> 1.

The first prerequisite computes

    N_m^ab = Z[z],       rho(x)=deg_t(x)/m.

Every `w_i` has `rho(w_i)=1`, since conjugation preserves exponent sum.
Thus the image of even one orbit relator generates `N_m^ab`, and

    Q_w^ab = N_m^ab/<[w_0],...,[w_(m-1)]> = Z/<1> = 0.

For coefficient injectivity, if `S -> H_w` has nontrivial kernel, simplicity
kills all of `S`; after the coefficients disappear, `w=1` becomes `t^m=1`.
The quotient is therefore a quotient of `C_m`, while the displayed exact
sequence supplies a surjection back onto `C_m`.  Hence `H_w=C_m` and
`Q_w=1`.  Conversely `Q_w=1` makes `H_w=C_m`, whose coefficient map kills
`S`.  This is also the equivalence isolated by the second prerequisite.

Finally let `Q_w -> K` have finite image and compose it with `N_m -> Q_w`.
On each `S_i` the kernel is normal, so simplicity makes the restriction
either injective or trivial.  It cannot be injective because `S_i` is
infinite and `K` is finite.  All `S_i` therefore die, and the map factors
through the retraction

    N_m -> <z> = Z.

Each defining relator `w_i` maps to `z`, so imposing `w_i=1` kills `z` as
well.  The finite image is trivial.

If `S` is finitely generated, the free-product description makes `N_m` and
then `Q_w` finitely generated.  A nontrivial finite-dimensional linear image
would be a nontrivial finitely generated linear group.  Malcev's theorem
makes that image residually finite, hence gives it a nontrivial finite
quotient, contradicting the preceding paragraph.
