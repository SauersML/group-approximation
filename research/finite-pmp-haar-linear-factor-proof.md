---
rg: 2
id: finite-pmp-haar-linear-factor-proof
kind: route
title: Rank finite points by iid Haar labels and use the finite action image
target: finite-pmp-actions-have-barren-haar-linear-compilers
requires: []
---

Write the `H`-orbits of `X` as `O_1,...,O_r` and put
`c_j=mu(O_j)`.  Invariance makes `mu` uniform inside each orbit, with point
mass `c_j/|O_j|`.

Let

```text
K_0=(F_p)^N,
K_1=((F_p)^X)^N,
K=K_0 x K_1
```

with product Haar measure.  Let `H` act trivially on `K_0` and by permuting
the `X`-coordinates in every layer of `K_1`.  These are continuous group
automorphisms, and their image is the finite permutation image of the given
action on `X`.

Because `K_0` is an atomless standard probability space, choose a measurable
partition `K_0=E_1 disjoint_union ... disjoint_union E_r` with
`Haar(E_j)=c_j`.  For `z in K_1` and `x in X`, form its infinite iid label

```text
ell_z(x)=(z_n(x))_(n>=1) in (F_p)^N.
```

With probability one, the finitely many labels `ell_z(x)`, `x in X`, are
pairwise distinct.  Order `(F_p)^N` lexicographically using any fixed order
on `F_p`.  If `t in E_j`, define `pi(t,z)` to be the unique point of `O_j`
whose label is least.  On the null tie set define `pi` arbitrarily.

The iid labels are exchangeable inside `O_j`, so conditional on `t in E_j`
each point of `O_j` is selected with probability `1/|O_j|`.  Thus `pi` pushes
Haar measure to `mu`.  Permuting the `X`-coordinates sends the unique least
label in an orbit to the corresponding permuted point, while `t` and the
chosen orbit are fixed.  Hence `pi` is `H`-equivariant almost everywhere,
proving `(FHC1)`.  Equivariant pullback and the identical canonical
`H`-unitaries give the trace-preserving crossed-product inclusion `(FHC2)`.

Let `J` be the finite image of `H -> Aut(K)` and `H_0` its kernel.  Since
`H_0` acts trivially on `A=K-hat`, there is an exact sequence

```text
1 -> A x H_0 -> A rtimes H -> J -> 1.
```

The kernel is sofic (`A` is amenable and `H_0` is a subgroup of the sofic
group `H`), and the quotient is finite, so the middle group is sofic.  This
proves the CE assertion.

Finally, a finite `H`-invariant Boolean algebra is the function algebra of a
finite p.m.p. `H`-space, so the construction applies verbatim.  If a tuple
realizing a finite non-CE microstate obstruction were also transported into
the CE target with the required relations and tolerance, it would contradict
the definition of that obstruction.  Therefore the construction pinpoints
the missing step: extending the base partition factor to the relation's
partial normalizers while keeping their multiplication through the infinite
translate closure.
