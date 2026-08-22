---
rg: 2
id: character-group-realizability-parseval-proof
kind: route
title: GNS the joint state, cut to the regular cyclic subspace by Parseval, identify the commutant of the left regular representation
target: character-group-realizability-parseval-criterion
requires: []
---

**Realisable implies the state.**  Let `v : W -> U(L(Lambda))` with
`tau_Lambda o v = tau`.  On `l^2(Lambda)` the operators `v_w in L(Lambda)`
commute with the right regular representation `rho`, so
`w (x) h -> v_w rho_h` is a representation of `C^*(W) (x)_max C^*(Lambda)`,
and `psi(x) = <x delta_e, delta_e>` is a state.  `(PGR1)`:
`<rho_h delta_e, delta_e> = delta_(h,e)`.  `(PGR2)`:
`<v_w delta_e, delta_e> = tau_Lambda(v_w) = tau(w)`.  `(PGR3)`:
`psi(w (x) h) = <rho_h delta_e, v_w^* delta_e> = <delta_(h^-1), v_w^* delta_e>`,
so `sum_h |psi(w (x) h)|^2 = ||v_w^* delta_e||^2 = 1`.

**The state implies realisable.**  Let `(H, sigma, xi)` be the GNS
triple of `psi`; `sigma(W)` and `sigma(Lambda)` commute.  By `(PGR1)` the
vectors `sigma(h) xi`, `h in Lambda`, are orthonormal; let `H_0` be their
closed span, so `(H_0, sigma|_Lambda) ~= (l^2(Lambda), lambda)` via
`sigma(h) xi -> delta_h`.  For `w in W`,

```text
sum_h |<sigma(w) xi, sigma(h) xi>|^2 = sum_h |psi(w (x) h^-1)|^2 = 1 = ||sigma(w) xi||^2
```

by `(PGR3)`, so `sigma(w) xi in H_0`; and then
`sigma(w) sigma(h) xi = sigma(h) sigma(w) xi in H_0`, so `H_0` is
`sigma(W)`-invariant.  The restrictions `v_w = sigma(w)|_(H_0)` commute
with `lambda(Lambda)`, hence lie in `lambda(Lambda)' = R(Lambda)`, the
right group von Neumann algebra, and
`<v_w delta_e, delta_e> = psi(w (x) 1) = tau(w)`.  The unitary
`U delta_x = delta_(x^-1)` satisfies `U lambda_g U^* = rho_g`, so
`Ad U : L(Lambda) -> R(Lambda)` is a trace-preserving isomorphism; composing
gives `v : W -> U(L(Lambda))` with `tau_Lambda o v = tau`, and the GNS
uniqueness theorem identifies `v(W)''` with `Q_tau`.

**Closure properties.**  *Hyperfinite GNS:* a hyperfinite tracial algebra
with separable predual embeds unitally and trace-preservingly into the
hyperfinite II_1 factor `R`, and `R = L(S_infinity)` (Connes; `S_infinity`
the finitary symmetric group is ICC and amenable).  *Convex combination*
`t tau_1 + (1-t) tau_2` with hosts `Lambda_1, Lambda_2`: the GNS algebra is
`Q_1 (+) Q_2` with weights `(t, 1-t)`; choose a projection `p in L(Z)`
of trace `t` and map `x_1 (+) x_2 -> p x_1 + (1-p) x_2` into
`L(Z) (x) L(Lambda_1 x Lambda_2) = L(Z x Lambda_1 x Lambda_2)`.
*Pointwise product* `tau_1 tau_2`: `w -> pi_1(w) (x) pi_2(w)` lands in
`Q_1 (x) Q_2 subset L(Lambda_1 x Lambda_2)`.  *Pullback* along
`phi : W' -> W`: `Q_(tau o phi) = pi_tau(phi(W'))'' subset Q_tau`.
*Induction* from `W_0 <= W` of index `n`: the induced character's GNS
algebra sits in `M_n (x) Q_tau subset L(S_infinity) (x) L(Lambda)
= L(S_infinity x Lambda)`, with the induced character equal to
`tr_n (x) tau` on the induced representation.  Each construction is a
tensor product, direct sum with central projections, or subalgebra of
group factors of hyperlinear groups when the inputs are hyperlinear, which
is the preservation statement in the claim.
