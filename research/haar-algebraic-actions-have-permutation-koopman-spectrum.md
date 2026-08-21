---
rg: 2
id: haar-algebraic-actions-have-permutation-koopman-spectrum
kind: claim
title: Haar algebraic actions have permutation Koopman spectrum and reciprocal stabilizer moments
distinct_from:
  algebraic-compact-action-group-factor-compiler: that Fourier-transforms an algebraic crossed product after an embedding has been found; this gives necessary conditions on attempts to obtain that embedding from an equivariant base map or a direct Haar stabilizer process.
  algebraic-compact-action-envelope-for-non-ce-relation: that asks for an arbitrary von Neumann embedding of the non-CE relation factor; this theorem rules out universal action-factor and unrestricted direct-IRS realizations but does not obstruct a genuinely non-Cartan embedding.
---

Let a countable group `Lambda` act by continuous automorphisms on a compact
second-countable abelian group `K`, with Haar probability `m_K`, and put
`A = K-hat`.

## 1. The Koopman representation is a permutation representation

The characters

```text
{chi_a : a in A}
```

are an orthonormal basis of `L^2(K,m_K)`.  If `g in Lambda`, then

```text
U_g chi_a = chi_(g.a).                                    (HAK1)
```

Consequently the Koopman representation is canonically the permutation
representation

```text
L^2(K) ~= ell^2(A)                                        (HAK2)
```

for the dual `Lambda`-set `A`.

It follows that if a p.m.p. action `Lambda -> Aut(X,mu)` is a measurable
factor of this Haar algebraic action, then its Koopman representation is a
subrepresentation of a permutation representation.  Indeed the factor map
`K -> X` gives an equivariant isometric pullback

```text
L^2(X,mu) -> L^2(K,m_K).
```

The same conclusion holds if one starts with a unital trace-preserving
`Lambda`-equivariant embedding

```text
L^infinity(X) -> L^infinity(K),                            (HAK3)
```

because homomorphisms of standard commutative probability algebras arise from
measurable factor maps modulo null sets.

This already disproves a universal algebraic-factor envelope.  For example,
let `Lambda = Z`.  A permutation unitary on `ell^2(A)` decomposes over the
finite and infinite orbits of the generating permutation.  A finite orbit
contributes only roots of unity as eigenvalues, while an infinite orbit is a
bilateral shift and has no eigenvectors.  Thus every eigenvalue of a Haar
algebraic `Z`-action is a root of unity, and the same is true for every factor.
An irrational circle rotation has an irrational eigenvalue.  It is therefore
not a factor of any compact-abelian Haar action by automorphisms.

The obstruction is specifically to AUTOMORPHISMS.  An irrational rotation is
itself an action on a compact abelian group, but it acts by translation, not by
group automorphisms, and so does not Fourier-transform to the semidirect-product
group factor used by `algebraic-compact-action-group-factor-compiler`.

## 2. Haar stabilizer moments are reciprocal indices

For every finite set `F subset Lambda`, let

```text
Fix_K(F) = {x in K : g.x=x for every g in F}.
```

This is a closed subgroup of `K`.  Therefore

```text
m_K(Fix_K(F)) = 0                 if [K:Fix_K(F)] is infinite,
                  1/[K:Fix_K(F)] if [K:Fix_K(F)] is finite.       (HAK4)
```

The proof is elementary: distinct cosets have equal Haar mass, so a finite
index `n` forces mass `1/n`; infinitely many disjoint equal-mass cosets force
mass zero.

If `H_x = Stab_Lambda(x)` is the stabilizer IRS of Haar-random `x`, then

```text
P(F subset H_x) in {0} union {1/n : n=1,2,...}.            (HAK5)
```

For the preferred linear-subshift architecture

```text
K <= (F_p^m)^Lambda,
```

`Fix_K(F)` is a closed `F_p`-subspace.  Its finite index is a power of `p`, so

```text
P(F subset H_x) in {0} union {p^(-r) : r=0,1,2,...}.       (HAK6)
```

These are simultaneous constraints for every finite `F`, not merely a
restriction on the one-point character values
`P(g in H_x)`.  Equivalently, the positive stabilizer cylinders of a direct
Haar-linear realization have a finite-codimension rank function.

## Consequence for the non-CE relation route

Two tempting generic constructions are therefore unavailable:

1. one cannot take an arbitrary p.m.p. relation action, relabel its atomless
   base as Haar measure on a compact abelian group, and expect all generators
   to become group automorphisms; the Koopman representation would have to
   acquire the permutation form `(HAK2)`;
2. one cannot realize an arbitrary IRS directly as the stabilizer law of a
   Haar linear subshift; all of its positive cylinder moments would have to
   satisfy `(HAK6)`.

For the particular Manzoor IRS used upstream, no violation of `(HAK6)` is
currently established: the construction is existential and does not expose a
finite cylinder with a forbidden value.  Thus this note does **not** refute
`algebraic-compact-action-envelope-for-non-ce-relation`.

It does sharply locate the remaining freedom.  A successful envelope must do
at least one of the following:

- construct a special non-CE witness whose action already has permutation
  Koopman spectrum and whose stabilizer moments obey the Haar rank laws; or
- embed the relation factor in the algebraic crossed product in a genuinely
  non-base-equivariant/non-Cartan fashion, so that the original action is not
  a factor of the Haar algebraic action and its group unitaries are not simply
  the global algebraic-action unitaries.

The second option is not a cosmetic weakening: it is precisely the part not
captured by ordinary action factors, stabilizer processes, or scalar
correlation matching.
