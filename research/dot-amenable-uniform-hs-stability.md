---
rg: 2
id: dot-amenable-uniform-hs-stability
kind: claim
title: Mean epsilon-representations of any amenable group into a finite von Neumann algebra are 71 epsilon-close to a compressed genuine representation
distinct_from:
  gowers-hatami-finite-group-hs-stability: that is the finite-group theorem with dimension bound d/(1-4epsilon^2); this is the De Chiffre--Ozawa--Thom extension to every countable discrete amenable group, including infinite locally finite groups, with the representation living on a corner of M tensor B(l^2).
  all-abelian-uniform-hs-rounding-gives-global-pvm: that is same-dimensional rounding for abelian groups via Akhtiamov--Dogon; this allows irreducibles of unbounded dimension and pays with a flexible enlargement.
---

**ESTABLISHED (import).** Route `dot-amenable-uniform-hs-stability-citation`.

Source: M. De Chiffre, N. Ozawa, A. Thom, *Operator algebraic approach to inverse and stability theorems for
amenable groups*, arXiv:1706.04544 (Mathematika 65 (2019)). Definition 5.1 and Theorem 5.2 are quoted verbatim in the
route.

**Form used in the graph.** Let `G` be a countable discrete amenable group with invariant mean `E`, let `n >= 1`, and
let `phi : G -> U(n)` satisfy

```text
E_h ||phi(gh) - phi(g)phi(h)||_2 < epsilon       for every g in G,          (DOT1)
```

in the normalized Hilbert--Schmidt norm (for instance `sup_(g,h) ||phi(gh)-phi(g)phi(h)||_2 < epsilon`). Put
`M = M_n`, `M_infty = M_n (x) B(l^2(N))` with the semifinite trace `tau` normalized by `tau(1_M) = 1`. Then there are a
projection `P in M_infty`, a partial isometry `U in P M_infty 1_M` and a representation `rho : G -> U(P M_infty P)` with

```text
||phi(g) - U^* rho(g) U||_2 < 71 epsilon   for all g in G,
||1_M - U^* U||_2 < 40 epsilon,     ||P - U U^*||_2 < 30 epsilon.            (DOT2)
```

Since `U U^* <= P`, `tau(P) = tau(UU^*) + ||P-UU^*||_2^2 < 1 + 900 epsilon^2`, so `P` has finite rank and `rho` is a
genuine **finite-dimensional** unitary representation of `G` (on `P l^2`, of dimension `< n(1+900 epsilon^2)`).
This finite-rank reading is exactly how the source derives Gowers--Hatami (its proof of Theorem 1.6).
