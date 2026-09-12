---
rg: 2
id: exact-support-gap-nonexact-checks-no-advantage-proof
kind: route
title: Subtract acceptance mass and restrict to the exact support
target: exact-support-gap-nonexact-checks-no-advantage
requires: []
---

Fix a marked profile `z`.  From `g>q>=mu(A_z)` we get

```text
mu(E) > mu(A_z).
```

If `E` were contained in `A_z`, then monotonicity of `mu` would give the
opposite inequality.  Hence `E\A_z` is nonempty for every `z`.  In particular
`E` itself is nonempty.

Now put the uniform measure `nu` on the finite set `E`.  Since each `z` misses
at least one member of `E`,

```text
nu(A_z) = nu(A_z intersect E) <= (|E|-1)/|E|.
```

Taking the supremum over all marked profiles gives the stated uniform gap, and
`rho` satisfies every relator in the support of `nu` exactly by definition of
`E`.

For the converse, if some `z` has `E subset A_z`, then for every `mu`

```text
q >= mu(A_z) >= mu(E)=g,
```

so a strict exact-support gap is impossible.  The argument does not use
finiteness of the profile space, only finiteness of the relator menu.
