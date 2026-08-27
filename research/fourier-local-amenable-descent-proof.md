---
rg: 2
id: fourier-local-amenable-descent-proof
kind: route
title: Compose Fourier sections with amenable-trace microstates
target: fourier-local-sections-already-descend-amenable-trace
requires:
  - amenable-trace-descends-through-locally-liftable-quotient
  - invariant-free-near-state-is-amenable-regular-cover
---

Use the ucp-microstate characterization of the amenable trace `tau_A`.
Given a finite multiplication test `K subset G`, choose `F` containing
`1,K,K^(-1),K^2` and a section `s=s_F`.  If

```text
Phi_i:A -> M_(n_i)
```

are amenable-trace ucp approximants, then `Phi_i o s` is ucp on `E_F` and
extends to a ucp map on `C^*_r(G)` by Arveson's theorem.

For `g,h in K`, put

```text
d_(g,h)=s(lambda_(gh))-s(lambda_g)s(lambda_h).
```

Since `q(d_(g,h))=0` and `tau_A=tau_G o q`, one has
`tau_A(d_(g,h)^*d_(g,h))=0`.  Amenable-trace approximation and Schwarz give

```text
||Phi_i(d_(g,h))||_2 -> 0.
```

After inserting `Phi_i(s(lambda_g)s(lambda_h))`, the ordinary
`tau_A`-multiplicativity of `Phi_i` therefore gives

```text
||Phi_i s(lambda_(gh))
   -Phi_i s(lambda_g) Phi_i s(lambda_h)||_2 -> 0.       (FLS7)
```

The normalized traces converge to `tau_G` because the section is
trace-preserving modulo `q`.  Diagonalizing over finite word tests proves
amenability of `tau_G`.  The cyclic assertion follows from continuous
functional calculus for the unitary `pi(g)`.

