---
rg: 2
id: relative-t-heisenberg-adjoint-quantum-expansion-proof
kind: route
title: Apply the relative Kazhdan inequality to the traceless adjoint representation and lazify
target: relative-t-heisenberg-adjoint-quantum-expansion
requires: []
---

Write `K_q=L^2(End(H_q))` with normalized Hilbert--Schmidt inner product.
Because scalar projective cocycles cancel under conjugation,

```text
rho_q(g)X=pi_q(g)Xpi_q(g)*
```

is a genuine unitary representation of `Gamma` on `K_q`. Its `N`-fixed
vectors are exactly the commutant of `pi_q(N)`. Irreducibility of
`pi_q|N` and Schur's lemma make that commutant `C I`. Hence the traceless
subspace `K_q^0` has no nonzero `N`-fixed vector.

Let

```text
Phi_q=(1/|S|) sum_(s in S) rho_q(s).
```

Symmetry of `S` makes `Phi_q` self-adjoint. If `X in K_q^0` is a unit
vector, the relative Kazhdan inequality gives an `s_0 in S` with
`||rho_q(s_0)X-X||_2>=kappa`. Therefore

```text
2(1-<Phi_q X,X>)
 = (1/|S|) sum_s ||rho_q(s)X-X||_2^2
 >= kappa^2/|S|,
```

and so the largest eigenvalue of `Phi_q|K_q^0` is at most
`1-kappa^2/(2|S|)`. The spectrum of the self-adjoint contraction `Phi_q`
lies in `[-1,1]`. The lazy channel `Psi_q=(I+Phi_q)/2` consequently has
nonnegative spectrum and operator norm at most

```text
(1+1-kappa^2/(2|S|))/2 = 1-kappa^2/(4|S|)
```

on `K_q^0`. This is `(RTH2)`. No bound in the argument depends on `q` or
on `dim H_q`.

