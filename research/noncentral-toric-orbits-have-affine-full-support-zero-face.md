---
rg: 2
id: noncentral-toric-orbits-have-affine-full-support-zero-face
kind: claim
title: Noncentral toric clause orbits still have only affine full-support zero faces
distinct_from:
  centralized-clause-zero-face-is-exact-affine-bcs-quotient: that proves an equivalence for central singleton clauses; this proves the necessary affine-quotient conclusion for arbitrary noncentral finite clause orbits and combines it with the toric normal-quotient formula.
  finite-morita-toricization-cannot-encode-nonaffine-support: that assumes a finite Morita packet and representation-functorial predicate compiler; this permits arbitrary infinite player groups and arbitrary finite noncentral conjugation orbits.
  toric-gap-is-a-relative-fd-central-word-face: that computes the normal toric quotient and relative finite-dimensional face abstractly; this applies the quotient regular trace to BCS residuals and rules out retaining the full support of one nonlinear predicate.
---

Let

```text
Gamma=B times G_A times G_B
```

be a finite-phase two-player toric target, and let

```text
r_i=beta_i a_i b_i,
D=sum_i (r_i-1)^*(r_i-1),
N=normal_closure_Gamma({r_i}).                         (NTO1)
```

The `r_i` may form any finite genuinely noncentral conjugation orbit before
quotienting. Let `z_x` be decoded group words and `H_B` the positive BCS
residual Hamiltonian. Suppose the zero-face implication

```text
phi(D)=0 and phi tracial on C*(z_x)
  ==> phi(H_B)=0                                      (NTO2)
```

holds for every target state. Then, in `barGamma=Gamma/N`,

```text
R(bar z)=0 in C[barGamma]          for every BCS residual R. (NTO3)
```

In particular, for every context `c`, the surviving assignment spectrum is
the linear subspace

```text
Sigma_c=Hom(<bar z_x:x in U_c>,{+1,-1})
        subseteq Allowed_c.                           (NTO4)
```

This conclusion is independent of the size and noncentrality of the clause
orbit. Toric factorization makes that independence structural: the normal
quotient has the established form

```text
(B times A_0 times B_0)/Z,                            (NTO5)
```

where every one-player clause component is central in `A_0` or `B_0` and
`Z` is the central residual clause subgroup. Thus pre-quotient noncentral
orbit data is erased exactly in the quotient on which `(NTO2)` is tested.

There is a sharp full-support obstruction. Suppose Condition 1 is required
to retain a perfect representation whose joint context spectral projection
is nonzero for every allowed assignment of one context `c`. Because that
representation kills all clauses, it factors through `barGamma`; `(NTO3)`
then makes its context spectrum a subset of `Sigma_c`. Full allowed support
therefore gives

```text
Allowed_c subseteq Sigma_c.
```

Together with `(NTO4)`, this forces

```text
Allowed_c=Sigma_c,                                    (NTO6)
```

so the predicate support is linear. Hence no finite noncentral toric clause
orbit can retain all allowed types of a genuinely nonlinear BCS predicate
while satisfying the all-state zero-face condition.

Phase safety does not weaken this conclusion. If `N intersect B={1}`, the
phase group embeds in `barGamma`; its faithful regular trace is still the
state which proves `(NTO3)`. The phase certificate and the noncentral orbit
therefore cannot remove forbidden selector types only on a chosen phase
sector.

Applied to `finite-normal-clause-orbit-bcs-compiler`, the nearest surviving
positive lane is now exact: first find a globally compatible family of
linear subspaces

```text
Sigma_c subseteq Allowed_c                            (NTO7)
```

which supports the chosen perfect non-CE tracial model, and then realize
those subspaces in a phase-safe toric quotient. A finite noncentral orbit can
help with quantitative energy away from zero, but it cannot replace
`(NTO7)` or retain a nonlinear full-support predicate.
