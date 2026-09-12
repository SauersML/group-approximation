---
rg: 2
id: map-free-near-state-pure-singularity-proof
kind: route
title: Decompose the state and rule out a negative constant residual character
target: map-free-near-state-is-purely-singular
requires: []
---

Write the canonical decomposition of the state on `B(H)` as

```text
phi=phi_n+phi_s,
```

where `phi_n` is normal and `phi_s` is singular.  Let
`alpha=phi_n(1)` and `beta=phi_s(1)=1-alpha`.

For every `g`, conjugation by `pi(g)` preserves normal functionals and singular
functionals.  Since `phi` is invariant and the decomposition is unique, both
`phi_n` and `phi_s` are invariant.  If
`d_(g,h)=pi(gh)-pi(g)pi(h)`, then

```text
0=phi(d_(g,h)^*d_(g,h))
 =phi_n(d_(g,h)^*d_(g,h))+phi_s(d_(g,h)^*d_(g,h)).       (MPSP1)
```

Both summands are nonnegative, hence both vanish.  Thus every nonzero normalized
component is itself a state-form near representation.

Represent the normal part by a positive trace-class operator `D`:
`phi_n(a)=Tr(Da)`.  Invariance gives `pi(g)Dpi(g)^*=D`, so every positive
eigenspace of the compact operator `D` is a finite-dimensional invariant
subspace.  Moreover `(MPSP1)` for `phi_n` gives

```text
(pi(gh)-pi(g)pi(h))D^(1/2)=0,
```

so the restriction to `supp(D)` is a genuine representation, exactly as in
`normal-state-free-near-representation-forces-factorization`.  Each positive
eigenspace therefore carries a finite-dimensional unitary representation of
`G`.  Minimal almost periodicity makes all of them trivial.  Their orthogonal
sum is dense in `supp(D)`, so

```text
pi(g)|_(supp D)=1                    for every g.        (MPSP2)
```

Consequently

```text
phi_n(pi(g))=alpha                   for every g.        (MPSP3)
```

If `alpha=1`, `(MPSP3)` contradicts essential freeness for any nonidentity
element.  Suppose `0<alpha<1`.  Normalize the singular part,
`psi_s=beta^-1 phi_s`.  It is an invariant near-state, so
Kahl--Schneider Proposition 5.5(b) makes

```text
chi_s(g)=psi_s(pi(g))
```

a normalized positive-definite character.  For `g!=1`, essential freeness of
`phi` and `(MPSP3)` force

```text
chi_s(g)=c:=-alpha/beta < 0.                              (MPSP4)
```

A nontrivial minimally almost periodic group is infinite (otherwise its
finite-dimensional regular representation is nontrivial).  Choose distinct
`g_1,...,g_m`.  The positive-definite Gram matrix
`(chi_s(g_i^-1 g_j))` has diagonal `1` and every off-diagonal entry `c`.  Its
all-ones eigenvalue is

```text
1+(m-1)c.
```

For sufficiently large `m` this is negative, contradicting positive
definiteness.  Therefore `alpha=0`, i.e. `phi_n=0`, and `phi` is purely
singular.
