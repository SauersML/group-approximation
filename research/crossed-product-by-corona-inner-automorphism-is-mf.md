---
rg: 2
id: crossed-product-by-corona-inner-automorphism-is-mf
kind: claim
title: A crossed product by an automorphism implemented in some matrix-corona embedding is MF
distinct_from:
  regular-mf-central-hnn-closure: that concerns a stable letter centralizing a subgroup; this concerns a stable letter acting by a global automorphism, and the certificate is a corona unitary implementing it.
  asymmetric-hnn-embeds-in-central-hnn-of-inner-envelope: that converts a twist into a central letter inside an envelope; this proves the envelope itself (a semidirect product) is MF when the twist is corona-inner.
---

ESTABLISHED.  Let `A` be a separable C-star algebra, `Theta_1, ..., Theta_m`
automorphisms of `A`, and suppose there are an injective *-homomorphism
`Phi : A -> C = prod M_n / (+) M_n` and unitaries `U_1, ..., U_m in C` with

```text
U_i Phi(a) U_i^* = Phi(Theta_i(a))         (a in A, i <= m).       (CP1)
```

Then `A x|_(Theta_i) Z` is MF for each `i`, and `A x| F_m` (the free group
acting through the `Theta_i`) is MF.  For groups: if `B` is a countable
group with `C*(B)` MF and `Theta_i in Aut(B)` are implemented as in `(CP1)`
in one embedding of `C*(B)`, then `C*(B x| F_m)` is MF.

## Proof

*One automorphism.*  Fix `N`.  On `C (x) M_N` define

```text
pi_N(a) = diag( U^-n Phi(a) U^n )_(n = 0..N-1),
W_N     = sum_(n=1)^(N-1) e_(n,n-1) (x) 1  +  e_(0,N-1) (x) U^N.
```

`W_N` is unitary and `W_N pi_N(a) W_N^* = pi_N(Theta a)`: the `n`-th block
of the right side is `U^-(n-1) Phi(a) U^(n-1)` for `n >= 1`, and the `0`-th
block is `U^N (U^-(N-1) Phi(a) U^(N-1)) U^-N = U Phi(a) U^-1`.  So `(pi_N,
W_N)` is a covariant pair and induces `rho_N : A x| Z -> C (x) M_N`.
Realize `C` faithfully on a Hilbert space `H` and let `(pitilde, S)` be the
regular covariant pair on `H (x) l^2(Z)` induced from `Phi`; it is faithful
on the reduced crossed product, which equals the full one since `Z` is
amenable.  For `a = sum_(|m| <= M) a_m theta^m` and a vector `xi` supported
in the coordinates `[M, N-M-1]`, no wrap-around term of `W_N^(+-m)` is
reached, so `rho_N(a) xi = pitilde(a) xi`.  Since `pitilde(a)` has
propagation at most `M`, the supremum of `||pitilde(a) xi||/||xi||` over
such `xi` tends to `||pitilde(a)||` as `N -> oo`.  Hence `limsup_N
||rho_N(a)|| = ||a||`, and `rho = (rho_N)_N` is an isometric embedding of `A
x| Z` into `prod_N (C (x) M_N) / (+)_N`.  A separable subalgebra of that
quotient is MF by the local characterization of MF (each `C (x) M_N` is
locally matricial), so `A x| Z` is MF.

*The free group.*  `B x| F_m` is the amalgam over `B` of the mapping tori `B
x|_(Theta_i) Z` (Shulman, Proposition 28), so `A x| F_m` is the amalgam over
`A` of the `A x|_(Theta_i) Z`.  The embedding `rho^(i)` restricts to `A` as
`pi_N^(i) = diag(U_i^-n Phi U_i^n)`, which is conjugate to `Phi (x) 1_N` by
`diag(U_i^n) in C (x) M_N`.  After this conjugation every factor restricts to
the same embedding `Phi (x) 1_N` of `A`, so Shulman's Theorem 18 applies and
the amalgam is MF.  The group statement is the case `A = C*(B)`, using
`C*(B x| F_m) = C*(B) x| F_m`.
