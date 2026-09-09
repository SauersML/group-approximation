---
rg: 2
id: native-enlargements-require-external-haar-mass
kind: claim
title: Native S3 enlargements with small forward leakage require Haar mass outside the canonical group factor
distinct_from:
  native-backward-lamp-algebras-have-fixed-forward-leakage: That computes a five-sixths bound for canonical finite subgroup algebras; this uses the internal Kazhdan gap to obstruct arbitrary finite-dimensional subalgebras and quantify how much a successful external enlargement must leave the native group factor.
  native-s3-algebra-enlargement-obstructs-scalar-commutants: That produces a nonscalar full external commutant under three asymptotic enlargement hypotheses; this uses the internal Kazhdan gap to give a finite quantitative bound and an asymptotic lower bound on Haar mass outside the canonical group factor.
artifacts:
  - research/artifacts/leavitt-native-enlargement-external-haar-mass-2026-09-08.md
---

Let `N=L(H)` be the canonical factor of the binary Leavitt group,
and use its native `L,u,F_0=<k_+,k_->≅S_3`. Fix a finite
generating list `S_L` for `L`, set `S=S_L union {u,k_+,k_-}`,
and choose a max-form conjugation Kazhdan constant `0<kappa_H<=1`:

```text
kappa_H ||x||_2 <= max_(g in S)||lambda(g)x-xlambda(g)||_2
for x in L^2(N) with tau(x)=0.
```

Put `c_*=1-exp(-1/16)`. Let `Q` be any finite tracial von
Neumann algebra containing `N` with its canonical trace, and let
`A subset Q` be a unital finite-dimensional subalgebra that
commutes with `L` and contains `k_+,k_-`. Define

```text
alpha=integral_(v in U(A)) ||v-E_(uAu*)(v)||_2^2 dv,
eta_A=integral_(v in U(A)) ||v-E_N(v)||_2^2 dv.
```

If `alpha<=1/4`, then

```text
eta_A >= 1/128-alpha/(kappa_H^2 c_*).                 (1)
```

In particular every such algebra contained in `N` has the
unconditional forward bound

```text
alpha >= kappa_H^2 c_*/128.                          (2)
```

This includes arbitrary finite subalgebras of the canonical amenable
lamp-compressor algebra, not only group algebras.

The asymptotic conclusion permits approximate capture and commutation.
Let each finite tracial `Q_n` contain the same canonical `N`
trace-preservingly, and let `A_n subset Q_n` be finite-dimensional.
If

```text
e_n=sum_(s in S_L) integral_(v in U(A_n))||[s,v]||_2^2 dv ->0,
kappa_n=max_(sign=+,-)dist_2(k_sign,A_n) ->0,
alpha_n=integral_(v in U(A_n))||v-E_(uA_nu*)(v)||_2^2 dv ->0,
```

then `liminf_n eta_(A_n)>=1/128`. No finite-group exactification
is assumed. In particular even approximate versions of the three
conditions cannot be supplied by algebras contained in `N`.

Property `(T)` is used explicitly, only on the internal space
`L^2(N)`. No external commutant is identified with a native subgroup
algebra. The theorem does not prohibit external algebras with the
required positive mass outside `N`, establish a matrix-coordinate
rounding construction, or decide hyperlinearity. This is a written
proof, not a new Lean verification.

DERIVATION
kazhdan-projection-and-central-heights-force-external-mass
