---
rg: 2
id: finite-quotient-fell-cocycle-proof
kind: route
title: Compute the finite-quotient Fell basis change exactly
target: finite-quotient-fell-untwisting-leaves-kernel-cocycle
requires: []
---

Let `T(delta_a tensor xi)=delta_a tensor pi(s(a)^(-1))xi`.  Since `pi` is a
unitary representation,

```text
T^*(delta_a tensor xi)=delta_a tensor pi(s(a))xi.
```

Applying `R_g`, then `T`, gives

```text
delta_(q(g)a) tensor
pi(s(q(g)a)^(-1))pi(g)pi(s(a))xi
=delta_(q(g)a) tensor pi(c(g,a))xi,
```

where `c(g,a)=s(q(g)a)^(-1)g s(a)`.  Applying `q` to this word gives the
identity, so `c(g,a)` belongs to `ker(q)`.  Associativity immediately gives
the section cocycle identity.  Thus the basis change makes the quotient
coordinate permutation-valued but retains exactly the restricted kernel
representation in its blocks; those blocks are all identities precisely
when this cocycle is killed.

For an approximate representation and a fixed finite set of `g` and `a`,
the same displayed calculation uses only finitely many multiplication and
inverse relations among `g`, `s(a)`, and `s(q(g)a)`.  Repeated use of unitary
invariance and the triangle inequality bounds the normalized
Hilbert--Schmidt discrepancy by the sum of those finitely many defects.  It
therefore tends to zero on every fixed window, while the kernel-valued block
cocycle remains present.  This proves the exact and asymptotic assertions of
the target.
