---
rg: 2
id: bootstrap-tensoring-cannot-create-qd-trace-positive-class-proof
kind: route
title: Künneth with torsion cokernel, odd products are trace-invisible, extreme traces are product traces, then Krein-Milman
target: bootstrap-tensoring-cannot-create-qd-trace-positive-class
requires: [qd-trace-positive-class-iff-k0-state-off-qd-traces]
artifacts:
  - research/artifacts/qd-trace-positive-class-k0-state-form-2026-09-16.md
---

Artifact Sections 1 and 3.  The required claim (Theorem 1) says that a
separable unital nuclear quasidiagonal `B` is a witness iff
`r_B(T(B)) != r_B(T_qd(B))`, and iff condition (b) holds.

- **Tensor preliminaries** (Lemma 1.4).  Products of quasidiagonal traces are
  quasidiagonal, via the models `phi_n tensor psi_n`.  `A tensor D` is
  quasidiagonal, via the projections `P_n tensor Q_n`.
- **If.**  Take `y, sigma` from (b) for `A`, and put `iota(a) = a tensor 1`.
  Quasidiagonal traces of `A tensor D` restrict along `iota` to quasidiagonal
  traces of `A`, so `iota_* y` is positive on them.  Also
  `(sigma tensor tau_D)_*(iota_* y) = sigma_*(y) < 0`.  Then (b) => (a)
  applies.  The case of `D` is symmetric.
- **Only if.**
  1. *Künneth.*  Since `D` is in the bootstrap class, the Künneth theorem
     (Schochet, Pacific J. Math. 98 (1982); Rosenberg--Schochet, Duke Math. J.
     55 (1987); Blackadar, *K-theory for operator algebras*, §23) makes the
     external product map
     `K_0(A) tensor K_0(D) (+) K_1(A) tensor K_1(D) -> K_0(A tensor D)` have
     cokernel a sum of Tor groups, which is torsion.  So each
     `z in K_0(A tensor D)` has a multiple `m_z z` that is a sum of external
     products.
  2. *Odd products are invisible to traces.*  Even products satisfy
     `(rho_1 tensor rho_2)_*(x × y) = rho_1*(x) rho_2*(y)`.  For odd products,
     naturality gives `[u] × [v] = (phi_u tensor phi_v)_*(c)` with
     `c in K_0(C(T^2))`.  Every point evaluation sends `c` to `0`, so `c` has
     rank zero at every point.  Integrating against the positive functional
     `(Tr tensor omega) o (phi_u tensor phi_v)` then gives trace `0` for
     every `omega`.  Hence `(rho_1 tensor rho_2)_*` depends only on the pair
     `(rho_1*, rho_2*)`.
  3. *Extreme traces are products* (Lemma 1.5).  The GNS closure of an extreme
     trace is a factor.  So the left leg `M_1` is a finite factor.  For
     `d >= 0`, `x -> w(x pi(1 tensor d))` is a normal positive tracial
     functional on `M_1`, hence a multiple of the trace.
  4. *Conclude.*  If neither `A` nor `D` is a witness, every extreme `omega`
     has `omega_* = (tau_1 tensor tau_2)_*` for quasidiagonal `tau_i` with
     `tau_i* = rho_i*`, and `tau_1 tensor tau_2` is quasidiagonal.
     Krein--Milman (Lemma 1.6) and closed convexity of `r(T_qd)` give
     `r(T) = r(T_qd)` for `A tensor D`.  So it is not a witness.
- **Consequences in the claim body.**  The first consequence adds Gabe's
  theorem.  The inner crossed-product isomorphism uses gauge-invariant
  uniqueness for `Z`-crossed products.  The separation consequence uses
  artifact Proposition 3.
