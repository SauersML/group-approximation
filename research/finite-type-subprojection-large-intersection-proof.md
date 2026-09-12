---
rg: 2
id: finite-type-subprojection-large-intersection-proof
kind: route
title: Compare the full-overlap trace with the restriction-intersection formula
target: finite-type-subprojection-forces-large-root-intersection
requires:
  - finite-type-restriction-overlap-defect-formula
  - canonical-full-type-overlap-is-algebraic-corner-containment
---

Condition `(LRI2)` gives full overlap:

```text
tau_Gamma(pq)=tau_Gamma(p)=d_rho^2/|H|.                 (LRI7)
```

Apply the finite-type restriction-overlap formula to `p` and `q`. Their
transported subgroup intersection is `L`, so

```text
tau_Gamma(pq)
 =d_rho d_pi |L|/(|H||K|) m.                           (LRI8)
```

Equating `(LRI7)` and `(LRI8)` and cancelling `d_rho/|H|` gives

```text
m=d_rho |K|/(d_pi |L|)=d_rho [K:L]/d_pi,
```

which is `(LRI3)`. Since `m` is an integer, the displayed identity also
gives the divisibility assertion in `(LRI4)`.

The intertwiner space counted by `m` is a subspace of all linear maps from
a `d_rho`-dimensional space to a `d_pi`-dimensional space. Hence

```text
m<=d_rho d_pi.
```

Substitution in `(LRI3)` proves the index bound. If equality holds, the
intertwiner space is the whole matrix space. For every `ell in L`, every
linear map `T` then satisfies

```text
pi(ell)T=T rho^g(ell).
```

Taking matrix units shows that both operators are the same scalar. Varying
`ell` gives one common one-dimensional character, proving the equality
statement.

Finally each atom in a partition summing to `q` is subordinate to `q`,
so the same argument gives `(LRI5)` term by term. If an intersection lies
inside `Z`, then `[K:L]>=[K:Z]`, proving `(LRI6)`. For
`K_D=(C_2)^D semidirect S_D`, the central sign has order two and the full
diagonal sign torus has order `2^D`; the quoted indices are therefore
`2^(D-1)D!` and `D!`, respectively.
