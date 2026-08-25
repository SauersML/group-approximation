---
rg: 2
id: wagon-wheel-exact-radical-has-hs-wall
kind: claim
title: Slofstra's wagon wheel preserves exact finite-dimensional invisibility but has a fixed normalized-HS wall
distinct_from:
  slofstra-involution-not-sofic-radical: that proves the distinguished sign survives one permutation-ultraproduct homomorphism; this combines that construction with exact finite-dimensional invisibility of the same sign and extracts the dimension-uniform no-modulus and arbitrary error-schedule consequences for the actual wagon-wheel output.
  exact-fd-invisibility-has-no-general-hs-robustification: that gives a general counterexample from Slofstra--Vidick Proposition 3.2; this locates the failure inside the explicit solution group produced by Slofstra's wagon-wheel embedding.
  marked-approximate-radical-survives-solution-group-embedding: that is the positive conditional theorem when the source already has a normalized-HS collapse modulus; this proves its approximate-radical hypothesis cannot be weakened to exact finite-dimensional invisibility, even for the distinguished sign in the motivating wagon-wheel construction.
---

**ESTABLISHED SHARP FIREWALL.** Let `S` be the solution group produced in
Slofstra, arXiv:1703.08618v2, Proposition 5.1, from the Higman/HNN source used
in the older Tsirelson-separation proof, and let `J` be its distinguished
central involution. Then both of the following hold.

1. Every exact finite-dimensional unitary representation `pi:S->U(d)` has
   `pi(J)=I`.
2. There are maps `rho_n` from the fixed generators of `S` to permutation
   matrices such that

   ```text
   Def_S(rho_n) -> 0,
   ||rho_n(J)-I||_2 = sqrt(2).                         (WWH1)
   ```

Here `Def_S` is the maximum normalized Hilbert--Schmidt defect of the fixed
finite presentation. The first assertion is the exact mechanism of the
Tsirelson separation: the source central involution is killed in every exact
finite-dimensional representation, and the exact embedding sends it to `J`,
so restriction kills `J` in every exact finite-dimensional representation of
the solution group. The second assertion is the permutation construction in
`slofstra-involution-not-sofic-radical`: its finite-coordinate `J_n` is the
fixed-point-free flip, so

```text
d_H(J_n,I)=1,
||J_n-I||_2^2=2 d_H(J_n,I)=2.                         (WWH2)
```

Consequently there is no dimension-independent function `omega(t)->0` for
which every matrix tuple for this presentation obeys

```text
||rho(J)-I||_2 <= omega(Def_S(rho)).                   (WWH3)
```

The failure can be put on any prescribed error schedule. If
`eta_k>0` and `eta_k->0`, choose a subsequence of `(rho_n)` with
`Def_S(rho_(n_k))<=eta_k`. Equation `(WWH1)` still gives
`||rho_(n_k)(J)-I||_2=sqrt(2)` for every `k`. This is a fixed wall, not merely
failure of a known proof technique.

The exact quantitative phase boundary is therefore

```text
kappa_S(delta) <= kappa_G(A delta)+B delta,            (WWH4)
```

from `marked-approximate-radical-survives-solution-group-embedding`. The
finite wagon-wheel areas provide `A,B` and preserve any source modulus already
known. Exact finite-dimensional invisibility only identifies the value at
zero for exact representations; it gives no control of `kappa_G(epsilon)` as
`epsilon` tends to zero through unbounded dimensions. Slofstra's own output
realizes that discontinuity.

DERIVATION
wagon-wheel-hs-wall-proof
