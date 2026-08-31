---
rg: 2
id: heisenberg-tree-proper-marginal-no-go-proof
kind: route
title: Classify marked finite subgroups and force every orthogonal family into one chart
target: one-center-heisenberg-tree-has-no-proper-escaped-marginal
requires:
  - finite-type-restriction-overlap-defect-formula
---

The identified element `J` is central in `Gamma`, and

```text
Jq=zeta q.                                               (HNG8)
```

Every atom in `(HNG3)` satisfies `p_a<=q), hence `Jp_a=zeta p_a`.
Write its transported support subgroup as
`A_a=g_a H_a g_a^(-1)`. The identity coefficient of `p_a` is

```text
dim(rho_a)^2/|A_a|>0.
```

The coefficient of `J` on the left of `Jp_a=zeta p_a` is therefore
nonzero. It follows that `J in A_a). Since `J` is central, Schur's lemma
and the same equality say that the transported type has central character
`zeta).

A finite subgroup of a group acting on a tree fixes a vertex. Applied to
the Bass--Serre tree, this puts `A_a` inside a conjugate `F` of one
Heisenberg vertex group. Because it contains `Z`, its image in

```text
F/Z isomorphic to F_ell^2
```

is a linear subspace. There are only three cases.

- If `A_a=Z`, its marked character idempotent is `q`.
- If `|A_a|=ell^2`, then `A_a` is maximal abelian and the marked type is
  one-dimensional.
- If `A_a=F`, Stone--von Neumann uniqueness makes its marked type
  `pi_(F,zeta)`, whose central idempotent is again `q`.

The first and third cases cannot occur in a partition with at least two
nonzero atoms: one atom would already equal the unit `q`. Thus every atom
is a character idempotent of a maximal abelian subgroup containing `Z`.

Two distinct maximal abelian subgroups in one Heisenberg vertex
intersect in `Z`, since they are inverse images of distinct lines in
`F/Z`. For distinct Bass--Serre vertex stabilizers, their intersection
fixes the whole connecting path and is contained in every edge stabilizer
on that path. Each such stabilizer is either `Z` or a maximal abelian
order-`ell^2` subgroup. Their intersection is therefore `Z` unless all
of them contain one common maximal abelian subgroup. In the latter case,
an atom chart contained at both endpoints must equal that common subgroup.
Consequently two atom charts `A,B` either agree as subgroups of `Gamma`
or satisfy

```text
A intersect B=Z.                                        (HNG9)
```

In the latter case their character restrictions to `Z` are both
`zeta`. The exact restriction-overlap formula gives

```text
tau(z_(A,alpha) z_(B,beta))
 =|Z|/(|A||B|)
 =1/ell^3>0.                                            (HNG10)
```

Such atoms are not orthogonal. Hence every atom in `(HNG3)` uses one and
the same maximal abelian chart `A`. Distinct atoms use distinct characters.
Each has trace `1/ell^2`, whereas `tau(q)=1/ell`; the trace equality in
`(HNG3)` forces exactly `ell` atoms. These are all characters of `A`
whose restriction to `Z` is `zeta`, proving `(HNG5)`.

Finally suppose the proper marginals in `(HNG6)` are equal. Their common
value belongs coefficientwise to

```text
C[A] intersect C[B]=C[A intersect B].                   (HNG11)
```

If `A!=B`, then `(HNG9)` puts it in `C[Z]`. It is a projection below
the primitive character idempotent `q in C[Z]`, so it is either zero or
`q`, contradicting proper nonemptiness. Thus `A=B`. The marked
character idempotents of the finite abelian group `A` are linearly
independent primitive projections, so equality of their subset sums gives
`S=T`. This proves `(HNG7)` and the claimed no-go.
