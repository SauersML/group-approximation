---
rg: 2
id: fixed-normalizer-pi-firewall-proof
kind: route
title: Prove tracial functoriality of fixed packet normalization
target: fixed-packet-normalizers-cannot-supply-the-matrix-only-pi-lock
requires: []
---

For a finite group `K` and irreducible `pi`, the central idempotent

```text
e_pi=(dim pi/|K|)sum_k conjugate(chi_pi(k))rho(k)
```

cuts out `A_pi=rho(C[K])e_pi ~= M_dim(pi) tensor I`.  If `u` implements a
type-preserving automorphism of `K`, it fixes `e_pi` and normalizes `A_pi`.
This uses only functoriality of `C[K]e_pi` and holds in every finite tracial
von Neumann algebra.

With approximate covariance, the Fourier formula and triangle inequality
give `||ue_piu^*-e_pi||_2<=C_K epsilon`; fixed packet words have the same
dimension-free compressed estimate.  Hence finitely many returned words
obtained solely through such normalizers remain near the same source matrix
factor universally tracially.

If exact group relations also forced a larger Pauli target tuple there, the
fixed PI gap would kill `e_pi` in every tracial representation.  But the
regular trace has `tau(e_pi)=dim(pi)^2/|K|>0`.  Thus this cannot preserve the
marked regular model, proving that fixed normalizers cannot be the required
matrix-only input.
