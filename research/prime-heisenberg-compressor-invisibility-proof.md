---
rg: 2
id: prime-heisenberg-compressor-invisibility-proof
kind: route
title: Trace the Heisenberg normalizer on its Weyl basis and then invoke the properly outer covariance obstruction
target: prime-heisenberg-compressor-hyperfinite-invisibility
requires:
  - hyperfinite-covariant-obstruction-lemma
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

Let `rho:Gamma->U(W)`, where `W` is finite and injective with faithful
normal trace `tau`.  Write `zeta=exp(2 pi i/p)`.  Since `rho(w)` is central
in `rho(Gamma)''`, its spectral projections

```text
e_r=(1/p) sum_(j=0)^(p-1) zeta^(-rj) rho(w)^j,
0<=r<p,                                                   (PHP1)
```

are central.  It is enough to prove `e_r=0` for every `r!=0`.  Otherwise
compress to `e_r W e_r`, normalize the trace, and assume
`rho(w)=zeta^r 1`.

In this sector the represented Weyl elements `rho(d_a)`,
`a in F_p^(2m)`, span the twisted group algebra of the nondegenerate
standard symplectic form, hence a copy

```text
C_r ~= M_(p^m)(C).                                      (PHP2)
```

This is the finite Stone--von Neumann theorem; nondegeneracy is preserved
because `r!=0` in the prime field.  The normalized matrix trace makes the
Weyl elements other than `1` orthogonal to `1`.

Fix `g in V`.  Conjugation by `rho(g)` preserves `C_r`, so it is implemented
there by a unitary `U_g`.  In the Weyl basis its adjoint action is

```text
Ad(U_g)(rho(d_a))=zeta^(r q_g(a)) rho(d_(S_g a)).       (PHP3)
```

The trace of this linear operator on `C_r` receives a contribution only
from `a in Fix(S_g)`.  Also

```text
Tr_(End(C^(p^m)))(Ad(U_g))=Tr(U_g) conjugate(Tr(U_g)).  (PHP4)
```

For completeness, `q_g|Fix(S_g)` is automatically additive.  If `a,b`
are fixed, compare the conjugate of
`d_a d_b=w^(beta(a,b))d_(a+b)` with the product of the conjugates in
`(PH1)`; the cocycle terms cancel and give
`q_g(a+b)=q_g(a)+q_g(b)`.  By hypothesis this character is nontrivial.
Multiplication by `r!=0` preserves nontriviality, so orthogonality of
characters on `Fix(S_g)` gives `(PH2)`.  Hence `Tr(U_g)=0`.

The matrix tensor decomposition of the finite algebra gives

```text
rho(g)=U_g h_g,       h_g in C_r' intersect W,
tau(rho(g))=tr_(p^m)(U_g) tau(h_g)=0.                  (PHP5)
```

Trace invariance and the compressor hypothesis now imply

```text
tau(rho(n))=0                    (n in N\{e}).          (PHP6)
```

Therefore `rho(N)''` is the Haar representation
`L(N)=L^infinity(N_hat)`.  On this abelian algebra, an intertwiner between
the identity and the automorphism induced by `k in K` is supported on the
fixed-point set of the dual transformation.  Hypothesis 3 makes this set
null for every `k!=e`, so the `K`-action on `rho(N)''` is properly outer.

Apply `hyperfinite-covariant-obstruction-lemma` to `N semidirect K`.
It identifies `rho(K)''` with `L(K)` inside the injective algebra `W`,
forcing `K` to be amenable, a contradiction.  Thus every `e_r`, `r!=0`,
vanishes in `(PHP1)`, and `rho(w)=1`.
