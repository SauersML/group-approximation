---
rg: 2
id: gap-refuted-witness-holes-collapse-equivalence-proof
kind: route
title: Gap lemmas give the forward implications and zero operators with a step modulus give the converses
target: gap-refuted-witness-holes-are-collapse-equivalent
requires:
  - atomic-leavitt-gap-on-nonzero-matrix-corner
  - approximate-relative-leavitt-cell-kills-active-trace
  - corona-projective-hilbert-hotel-cancellation
  - atomic-morita-return-kills-finite-order-mf-mark
  - finite-root-windows-share-one-reducing-corona-carrier
  - full-leavitt-idempotent-defect-saturation
---

## Step 0. Compactness for a finite-order mark

Let `Gamma=<S|R>` be finitely presented, and let `w^p=1` in `Gamma`. The
corona is `Q=prod M_(k_n)/sum M_(k_n)` in the operator norm.

**(K1)** `w in Rad_MF(Gamma)` holds iff there is a `delta_0>0` such that every
operator-norm `delta_0`-model `U` has `||w(U)-I||_op < c_p = sin(pi/p)`.

*Proof of `=>`.* Suppose not. Then there are `delta_n`-models `U_n` with
`delta_n->0` and `||w(U_n)-I|| >= c_p`. As in
`uniform-obstruction-from-corona-invisibility`, the sequence defines a unitary
representation `rho:Gamma->U(Q)`, whose relators hold because the defects tend
to `0`. It has `||rho(w)-1|| >= c_p`, so `w` is not in the kernel. This
contradicts `w in Rad_MF(Gamma)`.

*Proof of `<=`.* Let `rho:Gamma->U(Q)` be a representation.
- Lift each generator coordinatewise to a unitary. To do this, take any lift
  `x=(x_n)`: `x_n^*x_n-1 -> 0`, so eventually `x_n` is invertible and can be
  replaced by its unitary polar part, which changes it by `o(1)`. The lifts
  are models `U_n` whose defects tend to `0`.
- So eventually `||w(U_n)-I|| < c_p`, and therefore `||rho(w)-1|| <= c_p < 2c_p`.
- `rho(w)` is a unitary with `rho(w)^p=1`, so its spectrum lies in the `p`-th
  roots of unity. Every nontrivial root `zeta` has `|zeta-1| >= 2c_p`.
- Hence the spectrum is `{1}` and `rho(w)=1`.

**(K2) Rounding.**
- Unitaries are normal, so `||w(U)-I||_op` equals the maximum of `|lambda-1|`
  over the spectrum.
- If this maximum is below `c_p`, then every eigenvalue is strictly closer
  to `1` than to any other `p`-th root, since those are at distance at least
  `2c_p` from `1`.
- So nearest-root rounding sends the whole spectrum to `1`, and every
  nontrivial rounded spectral projection `p_U` is `0`.
- Conversely, if all nontrivial `p_U` vanish, then `||w(U)-I|| <= r(delta)`,
  the rounding radius.

## Part (A). AMR is equivalent to w in Rad_MF(Gamma)

**(a) => (b).**
- Choose `delta_1` with `eta(delta_1) < 1/3`.
- If some `delta_1`-model had a nonzero nontrivial atom `p_U`, then (AMR1)
  would give `s_i,t_i in p_U M_d p_U` with all three defects below `1/3`.
- `atomic-leavitt-gap-on-nonzero-matrix-corner` (ALG1) with `m=2` forces the
  sum of the three defects to be at least `1`. Contradiction.
- Hence `p_U=0`.

**(b) => (c).**
- Every operator-norm model with `delta<=delta_1` then has
  `||w(U)-I|| <= r(delta)`, by (K2).
- Lift an arbitrary `rho:Gamma->U(Q)` as in (K1). Its coordinates are
  eventually `delta_1`-models, so `||rho(w)-1|| <= lim r(delta_n) = 0`.
- Alternatively: (b) gives the right side of (K1) directly, after shrinking
  `delta_1` until `r(delta_1)<c_p`.

This is the established theorem `atomic-morita-return-kills-finite-order-mf-mark`,
re-derived at a single scale.

**(c) => (a).**
- (K1) gives `delta_0` such that every `delta_0`-model has
  `||w(U)-I|| < c_p`. So by (K2) every nontrivial `p_U=0`, and (AMR1) is
  vacuous for `delta<=delta_0`.
- Define `eta(delta)=0` for `delta<=delta_0` and `eta(delta)=1` for
  `delta>delta_0`.
- For `delta>delta_0` and any `p_U != 0`, take `s_0=s_1=t_0=t_1=0`. Each of
  the three defects then equals `||p_U||_op = 1 = eta(delta)`.
- Since `eta(delta) -> 0`, AMR holds.

**Literal instance.**
- For `Delta`, `z` has `p=2` and `c_2=1`, and BLAMR is AMR for `(Delta,z)`.
- `full-leavitt-idempotent-defect-saturation` puts all of `Delta` in
  `<<z>>`, and `Rad_MF` is normal. Hence BLAMR is equivalent to
  `Rad_MF(Delta)=Delta`.
- Neither direction uses Property `(T)`.

## Part (B). APC3 is equivalent to ADI3

**Forward.**
- `approximate-relative-leavitt-cell-kills-active-trace` gives
  `tr(P) <= 3 omega`.
- Then (APC4) and (APC1) give
  `||w_A(U)-I||_2 <= ||W-I||_2 + kappa <= 2 tr(P)^(1/2) + kappa
  <= 2 (3 omega)^(1/2) + kappa`.
- This tends to `0`.

**Converse.**
- Assume `||w_A(U)-I||_2 <= eta(delta) -> 0`. Then
  `||W-I||_2 <= eta+kappa`.
- The left inequality of (APC4) gives
  `tr(P) <= (eta+kappa)^2 / (4 sin^2(pi/p))`.
- With `S_i=T_i=0`, each defect in (APC3) is
  `||P||_2 = tr(P)^(1/2) <= (eta+kappa)/(2 sin(pi/p)) =: omega(delta)`,
  and `omega -> 0`.

Both directions are uniform over all HS `delta`-models, so the moduli
correspond as stated.

## Part (C). The corona coefficient-module decoder is equivalent to (NS)

**Forward.**
- Assume the decoder, and suppose some `rho` has `rho(x_ij(r_0)) != 1`.
- `finite-root-windows-share-one-reducing-corona-carrier` gives a nonzero
  finitely generated projective carrier `P_rho`.
- The decoder gives a unital ring homomorphism `R -> End(P_rho)`.
- `corona-projective-hilbert-hotel-cancellation` (its last clause, for rings
  containing a binary Leavitt family) forces `P_rho=0`. Contradiction.

**Converse.** If `(NS)` holds, the decoder's hypothesis is never met, so it
holds vacuously.

**Literal case.**
- `(NS)` says `x_13(q)` lies in the kernel of every corona representation,
  that is, `x_13(q) in Rad_MF`.
- By the same normal-generation step, this is total collapse.
- The route's other prerequisites are used only to guarantee
  `P_rho != 0`, which the carrier theorem already provides.

## Part (G). The general lemma

**Setting.**
- The hole is `H`: for every model `M` with carrier `P(M)` nonzero, a
  witness of type `W` with defect at most `omega(delta) -> 0` exists.
- **Gap.** Every witness on a nonzero carrier has defect at least `g(P)`.
  Either `g` is a positive constant (ALG1, corona hotel, ROW4), or
  `g(P) >= tr(P)/3` (ARL2).
- **Trivial witness.** The zero witness has defect `f(P)`, with `f(P) -> 0`
  as the carrier vanishes in the relevant norm. Here
  `f = ||P||_op` or `f = tr(P)^(1/2)`.

**Forward.** `H` forces `g(P(M)) <= omega(delta)`, so the carrier vanishes
uniformly in the gap's norm.

**Converse.** If the carrier vanishes uniformly in the norm of `f`, the zero
witness has defect at most `sup f -> 0`. For an operator-norm gap, where
`f` is two-valued, the step modulus of Part (A) is used.

**Conclusion.** `H` is equivalent to uniform vanishing of the carrier.
- In the three instances, that vanishing is equivalent to the target by (K1),
  by (APC1)/(APC4), or by (NS).
- (NV) is the contrapositive observation. If some model of the class
  inhabits the witness type on a nonzero carrier, the gap cannot hold
  uniformly, and the above collapse does not occur.
