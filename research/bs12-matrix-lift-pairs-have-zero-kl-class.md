---
rg: 2
id: bs12-matrix-lift-pairs-have-zero-kl-class
kind: claim
title: Any two unital lifts of one BS(1,2) trace-kernel homomorphism to the matrix ultraproduct have zero KK-difference class, so every K-theoretic obstruction to same-dimension operator-norm correction of BS(1,2) vanishes
distinct_from:
  dadarlat-matricial-stability-obstruction: Dadarlat's obstruction is the Bott/K-theory class of an almost-representation, which is nonzero for Z^2-type groups; this computes that the corresponding difference class for BS(1,2) inside the trace-kernel ideal is always zero.
  bs14-hs-stability-does-not-supply-relative-op-basin: that is a negative statement about HS-basins; this is a positive K-theoretic vanishing statement for pairs of lifts.
---

**ESTABLISHED** by `bs12-matrix-lift-pairs-have-zero-kl-class-proof`.

**Setting.**  `A = C*(BS(1,2)) = C(Sigma_2) rtimes Z`, where `Sigma_2` is the
dyadic solenoid.  Fix a free ultrafilter `omega` on `N`.  Set
`Q_omega = prod_N M_N / c_omega` (operator norm), and let `tau_omega` be the
limit normalized trace.  Set `J_omega = {x : tau_omega(x*x) = 0}`, the
trace-kernel ideal, and `R^omega = Q_omega / J_omega`, the tracial
ultraproduct.

**Statement.**

1. `K_0(A) = Z[1]` and `K_1(A) = Z[u_t]`, where `u_t` is the canonical unitary
   for the stable letter `t`.
2. `K_1(Q_omega) = 0` and `K_1(J_omega) = 0`.
3. Let `phi, psi : A -> Q_omega` be unital *-homomorphisms that agree
   modulo `J_omega`.  Then for every separable `C*`-subalgebra
   `E subset Q_omega` containing `phi(A) + psi(A)`, there is a separable
   `E_1` with `E subset E_1 subset Q_omega` such that the Cuntz-pair class
   `[phi, psi]` in `KK(A, E_1 cap J_omega)` is zero.
4. (Traces of the census lifts.)  Let `D_N = diag(zeta^j)`, with
   `zeta = e^(2 pi i/N)`, be the clock matrix.  Let `f_N` be any HS-asymptotic
   homomorphism of `BS(1,2)` with `f_N(a) = D_N`.  Then the limit character
   `g -> lim_omega tr_N f_N(g)` is the regular trace `delta_e`.  In
   particular, the exact clock representation `pi_0` and every twisted-clock
   near-representation `(D_N, A_s = W exp(isH))` of the wave-14 census
   (node bs12-twisted-clock-exact-pair-census, on a sibling branch) have the
   same limit trace
   `tau_reg`.  That trace is faithful on `A`, because `BS(1,2)` is amenable, so
   `C*(G) = C*_r(G)`.

**Consequence.**  Correcting a near-representation of `BS(1,2)` in the same
dimension, in operator norm, meets no KK, KL, K_0-ratio or Bott-type
invariant.  The Z^2 mechanism (a nonzero Bott class in `K_0(J_omega)`) has no
analogue here.  Every remaining obstruction is non-K-theoretic.  The wave-14
census pair is one instance of lifts with a common faithful trace, so any
failure it exhibits must come from de-amplification or absorption, not from
an index.

## Attempts

- 2026-09-19 (swarm-0917-w15-w15-ptm-follow): proved as stated.  It is used
  as step (c) of `bs12-full-lift-uniqueness-in-matrix-ultraproducts`.
