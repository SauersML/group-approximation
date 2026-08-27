---
rg: 2
id: subexponential-blr-sampling-has-scalar-contextual-escape
kind: claim
title: Subexponential BLR sampling has an exact scalar contextual escape
distinct_from:
  rooted-normalized-sum-linear-pcpp-needs-sqrt-n-norm: that obstructs a rooted normalized-sum linear proof through checker norm; this counts scalar solution tables and applies directly to arbitrary sampled parity equations, with arbitrary auxiliary bits.
  positive-rate-tanner-tests-have-contextual-models: that constructs noncommuting class-two operator strategies for positive-rate local codes; this already gives a one-dimensional commuting escape when too few parity checks are used.
  bounded-local-unitary-sum-verifier-no-go: that perturbs continuous scalar unitary leaves near a normalized sum; this uses exact binary signs and zero test defect.
---

Let `v_1,...,v_K in F_2^r` be any selected labels and let a same-basis
tester impose `m` scalar parity equations on their sign table

```text
(f(v_1),...,f(v_K)) in {+1,-1}^K
```

and any number `p` of auxiliary signs.  Assume the equations are jointly
satisfiable.  If

```text
m+r < (1-H_2(rho))K                                      (SBS1)
```

for some `0<rho<1/2`, then there is an exact scalar solution whose restriction
to the selected coordinates has relative Hamming distance greater than `rho`
from the restriction of every additive character of `F_2^r`.

In particular, with `rho=1/4`, every family with

```text
m+r < K/8                                                (SBS2)
```

has a zero-defect scalar table at distance greater than `1/4` from every
exact additive action on the selected labels.  Taking all `K=2^r` labels
shows in particular that `poly(r)` random or deterministic BLR samples cannot
be promoted by metric entropy to a same-basis additive decoder.  More
generally `(SBS1)` is an exact constraint-density lower bound for a private
label list.  The low entropy of exact PVMs becomes usable only after a
separate mechanism has already confined the tested table near the additive
representation variety.

The statement includes finite linear proof/auxiliary coordinates.  It does
not rule out a bounded-degree tester with sufficiently many independent
constraints per selected coordinate, a
nonlinear operator agreement theorem, or a finitely presented actor which
algebraically exposes the entire table with a uniform spectral gap.
