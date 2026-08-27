---
rg: 2
id: projective-far-defect-formula
kind: claim
title: The far projective commutator energy of a projectively subgroup-central unitary is an exact scalar
distinct_from:
  hecke-far-commutator-defect-formula: that computes the far defect of an exactly Lambda-central unitary as a coefficient of the adjoint representation; this handles unitaries central only up to scalar phases, by doubling the representation so the phases cancel, and its far scalar lives in the superoperator Hilbert space.
  projective-commutant-transfer-for-arithmetic-pair: that is the open quantitative transfer inequality (PRCC); this is its unconditional far-sector calculus -- the deferred "projective far-defect formula" of its attempts, valid in both the transfer and the counterexample scenario.
  no-spherical-leak-in-matrix-ultraproducts: that excludes a spherical component for exactly central witnesses; this classifies the enemy of the PROJECTIVE lane, whose leak is a spherical component of the doubled adjoint representation.
---

Let `(Gamma, Lambda)` be a Hecke pair as in
`hecke-far-commutator-defect-formula` (instances
`Gamma = SL_n(Z[1/p])`, `Lambda = SL_n(Z)`, completion
`G = PSL_n(Q_p)`, compact open `K`, any `n >= 2`).  Let `(M, tau)` be
ANY tracial von Neumann algebra, `pi : Gamma -> U(M)` a unitary
representation, and `U in U(M)` PROJECTIVELY `Lambda`-central:

```text
U pi(lambda) U^* pi(lambda)^* = c(lambda) 1,  c(lambda) in T,   (PFD1)
```

for every `lambda in Lambda`.  Set `psi_U(g) = tau(U^* pi(g) U
pi(g)^*)` and `phi_U = |psi_U|^2`.  Then:

1. `c : Lambda -> T` is a character; for `n >= 3` perfectness of
   `SL_n(Z)` forces `c = 1`, so projective and exact centrality
   coincide there; for `n = 2` the kernel of `c` has index at most
   `12`.
2. `phi_U` is positive definite on `Gamma` (a coefficient of the
   doubled adjoint representation `Ad pi otimes conj(Ad pi)` at the
   EXACTLY `Lambda`-fixed unit vector `U otimes conj(U)` -- the phases
   `c` cancel in the double), `Lambda`-bi-invariant, `= 1` on
   `Lambda`, and extends to a `K`-bi-invariant positive definite
   function on `G`.
3. Along the cofinite double-coset filter,

   ```text
   lim phi_U(gamma) = s_proj := || E_2( P_U ) ||_HS^2,          (PFD2)
   lim ( 1 - |tau(U^* pi(gamma) U pi(gamma)^*)|^2 ) = 1 - s_proj,
   ```

   where `P_U = |U><U|` is the rank-one operator on `L^2(M)` at the
   unit vector `U`, and `E_2` is the orthogonal projection of the
   Hilbert--Schmidt space `HS(L^2(M))` onto the operators commuting
   with every `Ad pi(gamma)`.
4. If `s_proj = 1` then `P_U` is `Ad pi(Gamma)`-invariant, so
   `pi(gamma) U pi(gamma)^* = omega(gamma) U` with `omega : Gamma ->
   T` a character; for `n >= 3` perfectness of `SL_n(Z[1/p])` gives
   `omega = 1`, i.e. `U in pi(Gamma)' cap M` exactly.  Otherwise the
   projective commutator energy `1 - |tr|^2` is uniformly bounded
   below outside finitely many double cosets.
5. For `n >= 3` the lazy Hecke average of
   `hecke-averaging-realizes-commutant-expectation`, applied in the
   doubled representation (`S_2(X) = (1/2) X + (1/(2L)) sum_i
   Ad pi(w_i) circ X circ Ad pi(w_i)^(-1)` on `HS(L^2(M))`),
   contracts `P_U` geometrically onto `E_2(P_U)` with the same rate
   `delta_0(n, p)`.

Consequences.  This is the deferred calculus of the PRCC lane: the
enemy of `projective-trace-square-transfer-for-sl3-pair` is exactly a
`c_0` spherical component of the DOUBLED adjoint representation, its
far energy is one scalar `1 - s_proj`, and (by 4) for the higher-rank
pair the projective and exact collapse statements are equivalent in
any tracial algebra -- the phase quotient that motivates
projectivization costs nothing in the far sector.  In particular the
enemy taxonomy of the exact lane (tempered `Xi`-decay in the
quasi-regular case, non-amenable leak module) transfers verbatim to
`PU`-valued witnesses.
