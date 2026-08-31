---
rg: 2
id: one-center-heisenberg-tree-has-no-proper-escaped-marginal
kind: claim
title: A one-center Heisenberg tree has no proper escaped finite-type marginal
artifacts:
  - research/heisenberg-tree-proper-marginal-no-go-proof.md
distinct_from:
  odd-prime-heisenberg-star-saturates-finite-type-gates: that exhibits two escaped full context partitions with dense many-phase overlap; this classifies every possible finite-type context in the entire one-center tree architecture and proves that only the full unit can pass between distinct charts.
  central-type-sum-equality-is-intersection-readable: that assumes one central finite chart on each side of a proposed equality; this proves that orthogonality itself forces every Heisenberg-tree context into such a single chart, even when atom-specific finite subgroups and arbitrary conjugates were initially allowed.
  finite-projective-sector-groupoids-have-conjugate-absorbers: that gives a general matricial absorber for finite projective transport; this is a direct character-and-Bass--Serre classification with an exact proper-marginal conclusion.
---

Let `ell` be an odd prime and let `Gamma` be the fundamental group of a
finite tree of groups whose vertex groups are order-`ell^3` Heisenberg
groups

```text
E_v=<J,X_v,Y_v |
     J^ell=X_v^ell=Y_v^ell=1,
     J central, X_v Y_v=J Y_v X_v>,
```

and whose every edge group is a proper subgroup containing the identified
center `Z=<J>`. Thus an edge group is either `Z` or a maximal abelian
subgroup of order `ell^2`; all edge embeddings identify `J`. Fix a
primitive root `zeta` and put

```text
q=e_(Z,zeta)=z_(E_v,pi_(v,zeta)),                      (HNG1)
```

where `pi_(v,zeta)` is the unique degree-`ell` Heisenberg type with
central character `zeta`.

Allow completely arbitrary transported finite types in `Gamma`:

```text
p_a=g_a z_(H_a,rho_a) g_a^(-1).                        (HNG2)
```

If at least two of them form a context partition

```text
p_a p_b=0 (a!=b),             sum_a p_a=q,             (HNG3)
```

then there is one Bass--Serre vertex stabilizer `F`, one maximal abelian
subgroup

```text
Z<A<F,                  |A|=ell^2,                     (HNG4)
```

and exactly the `ell` characters `alpha` of `A` extending `zeta`
such that

```text
{p_a}_a={z_(A,alpha): alpha|Z=zeta}.                   (HNG5)
```

Thus arbitrary atom-specific subgroup choices and conjugates collapse to
one ordinary Heisenberg chart as soon as orthogonality and the root
partition are imposed.

Consequently, let two nontrivial contexts have atom charts `A` and `B`
as in `(HNG5)`. For nonempty proper subsets of their atoms,

```text
P=sum_(alpha in S) z_(A,alpha),
R=sum_(beta in T) z_(B,beta),                          (HNG6)
```

one has

```text
P=R   if and only if   A=B and S=T.                    (HNG7)
```

In particular no proper nonzero marginal can be shared between distinct
maximal abelian charts, including atom-specific conjugate charts. If two
different Heisenberg vertices share a maximal abelian edge, a proper
marginal can pass between them only because both contexts use that very
same finite chart; the equality is literal edge data.

This closes the smallest proposed modifications of the odd-prime
Heisenberg star. A load-bearing finite-type atlas must use a vertex packet
larger than the Stone--von Neumann Heisenberg block or use atoms whose same
block entry is a genuinely noncentral multipath sum rather than one
transported central finite type. Enlarging a Heisenberg edge from the center
to a maximal abelian subgroup merely identifies the entire finite chart.
The theorem is a no-go for this architecture, not a proof of the
nonhyperlinear root.
