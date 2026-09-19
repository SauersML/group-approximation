---
rg: 2
id: stw84-locally-finite-by-abelian-reduces-to-twisted-af-lattices
kind: claim
title: Unrestricted locally-finite-by-abelian groups reduce to group-twisted AF lattice actions
distinct_from:
  stw84-kernel-finite-locally-finite-by-abelian-computation: that theorem makes every finitely generated stage finite-by-abelian; here the kernel intersection may be infinite and the conclusion is an exact reduction to arbitrary twisted lattice actions on group AF algebras, not a finite-dimensional upper bound.
  stw84-arbitrary-stabilizer-permutation-wreath-bound: that theorem exploits a coordinate tensor decomposition of the locally finite kernel; the present reduction applies without any coordinate or commutation structure and identifies precisely what is lost without it.
artifacts:
  - research/artifacts/stw84-twisted-af-lattice-core-2026-08-30.md
---

Let

```text
1 -> L -> G -> A -> 1                              (TAL1)
```

be an extension of countable groups, where `L` is locally finite and `A` is
abelian of finite rational rank `r`.  Let `T=tor(A)` and let `K` be the
inverse image of `T` in `G`.  Then `K` is locally finite, and `(TAL1)` reduces
canonically to

```text
1 -> K -> G -> A/T -> 1,                            (TAL2)
```

whose quotient is torsion-free of rank `r`.

Choose an increasing exhaustion of `A/T` by finitely generated subgroups
`B_j`.  Each `B_j` is a free lattice `Z^(q_j)` with `q_j<=r`.  If `E_j` is
its inverse image in `G`, then

```text
G=union_j E_j,
C*(E_j) = C*(K) rtimes_(alpha_j,u_j) Z^(q_j),        (TAL3)
```

where `C*(K)` is AF and `(alpha_j,u_j)` is a Busby--Smith twisted action
whose cocycle unitaries are canonical group unitaries from `K`.  Thus a
uniform nuclear-dimension estimate for these group-twisted AF lattice
crossed products, depending only on `q_j`, would settle all extensions
`(TAL1)` of rank at most `r` by the directed-union theorem.

This gives a complete answer in rank zero, without the kernel-finite
hypothesis:

```text
r=0  implies  G is locally finite and dim_nuc(C*(G))=0.  (TAL4)
```

In rank one, every lattice stage is cyclic and its extension splits.  Hence
the unresolved core is already the family

```text
C*(K rtimes_alpha Z)=C*(K) rtimes_alpha Z,           (TAL5)
```

for arbitrary countable locally finite groups `K` and arbitrary
automorphisms `alpha`.  A universal bound for `(TAL5)` would settle every
rank-one extension by `(TAL3)`.  It is enough to prove such a bound for
finitely generated locally-finite-by-cyclic groups: after exhausting `K` by
finite subgroups `F_j`, the groups

```text
<F_j,t> = <alpha^n(F_j):n in Z> rtimes <t>
```

increase to `K rtimes_alpha Z` and are finitely generated.

The old kernel-finite lane has an exact boundary inside `(TAL5)`.  It applies
if and only if every finite `E subset K` has finite two-sided orbit hull

```text
<alpha^n(E):n in Z>.                                  (TAL6)
```

Equivalently, `K` admits an increasing exhaustion by finite
`alpha`-invariant subgroups.  The remaining cyclic core is precisely the
failure of such an invariant finite-subgroup exhaustion.

This cyclic core is genuinely outside the permutation-wreath mechanism.
Let `K=Alt_fin(Z)` and let `alpha` shift the underlying integer set.  If
`a=(0,1,2)` and `t` implements the shift, then

```text
K rtimes_alpha Z = <a,t>.                             (TAL7)
```

Indeed, the conjugates `t^n a t^(-n)=(n,n+1,n+2)` generate the finitary
alternating group.  Adjacent conjugates do not commute, and `K` is simple,
so there is no direct-sum coordinate decomposition to which the arbitrary-
stabilizer permutation theorem can be applied.

For every rank, the quotient still gives the unconditional lower bound

```text
dim_nuc(C*(G)) >= r.                                  (TAL8)
```

The reduction does not assert finiteness in positive rank.  Its point is
that cocycle bookkeeping is not the first missing ingredient: even the
untwisted cyclic case `(TAL5)` asks for a uniform theorem for arbitrary
group-origin automorphisms of AF algebras.
