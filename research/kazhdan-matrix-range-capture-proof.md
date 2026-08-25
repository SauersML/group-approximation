---
rg: 2
id: kazhdan-matrix-range-capture-proof
kind: route
title: Dilate the nearby matrix-range point and Kazhdan-average its finite corner
target: kazhdan-generator-matrix-range-capture-exactifies
requires:
  - kazhdan-almost-invariant-corner-near-invariant-projection
---

Choose ucp maps `Phi_n:C^*(Gamma)->M_(d_n)` such that, with
`Y_(n,s)=Phi_n(u_s)`,

```text
max_(s in S)||Y_(n,s)-phi_n(s)||_(2,d_n)=:epsilon_n -> 0.          (GMP1)
```

Let `Phi_n(a)=P_n pi_n(a)P_n` be a Stinespring dilation, where `P_n`
has rank `d_n`.  Since `Y_(n,s)` is a contraction and is `epsilon_n`-close
to the unitary `phi_n(s)`,

```text
d_n-||Y_(n,s)||_HS^2=o(d_n).                                     (GMP2)
```

The Stinespring identity gives

```text
||P_n^perp pi_n(s)P_n||_HS^2
 =d_n-||P_n pi_n(s)P_n||_HS^2=o(d_n),                             (GMP3)
```

and the same for `s^(-1)`, hence
`||[pi_n(s),P_n]||_HS=o(sqrt(d_n))` uniformly on the fixed set `S`.
Apply `kazhdan-almost-invariant-corner-near-invariant-projection`: there is
an exactly `pi_n(Gamma)`-invariant finite-rank projection `E_n` with

```text
rank(E_n)/d_n -> 1,       ||E_n-P_n||_HS=o(sqrt(d_n)),              (GMP4)
```

and a partial isometry aligning `ran(P_n)` with `ran(E_n)` at the same
normalized-HS cost.  The restriction
`rho_n=pi_n|_(ran(E_n))` is a genuine finite-dimensional representation.
Equations `(GMP1)` and `(GMP4)` show that its aligned generators approach
`phi_n(s)`.

For a fixed word `g=s_1...s_l`, telescope the two products.  The number `l`
is fixed, the genuine tuple is unitary, and the defects of `phi_n` on the
finitely many prefixes tend to zero.  Generator convergence therefore
implies convergence at `g`.  This proves flexible correction on all fixed
group elements.

