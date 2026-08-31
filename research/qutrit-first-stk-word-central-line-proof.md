---
rg: 2
id: qutrit-first-stk-word-central-line-proof
kind: proof
title: Classify qutrit character restrictions and audit the first S T k closure
target: qutrit-two-to-one-phase-graph-requires-central-line-twist
requires:
  - qutrit-shortest-tk-word-graphs-are-diagonal-or-complete
  - binary-jacobson-first-alternating-ts-closure-relation
---

Because `C` is abelian, each `e_a` is its character projection.
For `h in H`, write `h'=g^(-1)hg in H'`. If
`e_b g e_a` is nonzero, applying `h` on the left in the two possible
orders gives

```text
chi_b(h)e_b g e_a=chi_a(h')e_b g e_a.
```

This proves the necessity in `(QCT1)`. Conversely, expand both character
idempotents in the group basis. Two terms in `e_b g e_a` collide exactly
along `H`, and the displayed compatibility makes every coefficient in
each collision class equal. Thus at least the class containing `g` has a
nonzero coefficient. This proves sufficiency.

Every order-three subgroup of `C` has a generator `J^r Z_1^q`.
On that generator,

```text
chi_a(J^r Z_1^q)=omega^(r+aq).                          (QCT3)
```

If `q=0`, the subgroup is `<J>` and the value is independent of
`a`. If `q!=0`, the affine map `a |-> r+aq` permutes
`F_3`, so the three restrictions are distinct.

Apply this observation separately to `H` and `H'`. If both restriction
families are constant, `(QCT1)` permits every block or none, depending on
their common central values. If both are injective, it permits a partial
matching, and it is a full matching when the two character families agree.
If exactly one is constant, it permits a three-to-one or one-to-three star;
restricting the multi-vertex side to the two selected phases of `R` is
the only possible two-to-one pattern. The cases `H=1` and `H=C` give,
respectively, the complete graph and a partial matching. This proves
`(QCT2)`.

It remains to audit the bounded Jacobson words. Their reduced values and
active supports are as follows.

| word or value | active support forced by coefficient comparison |
|---|---|
| `s=x_13(S)` | coordinates `1,3` |
| `t=x_23(T)` | coordinates `2,3` |
| `k=x_31(1)` | coordinates `1,3` |
| `st=ts` | coordinates `1,2,3` |
| `sk,ks,[s,k]` | coordinates `1,3` |
| `tk,kt` | coordinates `1,2,3` |
| `[t,k]=x_21(T)` | coordinates `1,2` |
| `[[t,k],s]=x_23(TS)=x_23(1)` | coordinates `2,3` |

The meaning of an active support `A` in this table is exact:

```text
C intersect gCg^(-1)=C_A,                              (QCT4)
```

where `C_A` is the pointwise stabilizer in `C` of the listed scalar
coordinates.

For the single roots and the words involving only `t,k`, this is the
coefficient audit of the dihedral prerequisite. Here is a direct audit of
the new `S` rows. Write `P,Q` for scalar permutation matrices in `C`.
Membership `Q=gPg^(-1)` is equivalent to `gP=Qg`.

For `g=st=I+S E_13+T E_23`, the third column is

```text
g e_3=e_3+S e_1+T e_2,
```

and it is the unique nonmonomial column. Hence `P` and `Q` fix coordinate
`3` and agree off it. Equality of that column, together with independence
of the Jacobson normal forms `1,S,T`, then forces them to fix coordinates
`1,2` as well.

For the remaining new rows, in the ordered `(1,3)` block one has

| word | active matrix |
|---|---|
| `sk` | `[[1+S,S],[1,1]]` |
| `ks` | `[[1,S],[1,1+S]]` |
| `[s,k]=sksk` | `[[1+S+S^2,S^2],[S,1+S]]` |

In each matrix exactly the two active columns are nonmonomial; all their
displayed entries are nonzero by the `F_2`-linear independence of
`1,S,S^2`. The equation `gP=Qg` therefore makes `P` and `Q` preserve
the two-element active set. Elements of `C` have odd order, so neither can
swap its two points. Both fix them pointwise, agree on the complement, and
commute with `g`. This proves `(QCT4)` for `sk,ks,[s,k]`.

The last two commutator values are the Steinberg identities

```text
[t,k]=x_21(T),
[[t,k],s]=x_23(TS)=x_23(1).
```

The raw-root and scalar-root calculations give their rows. This completes
the table.

The explicit affine qutrit action gives a leaf stabilizer

```text
C_(u_1)={J^(b u_1)Z_1^b:b in F_3}.
```

An intersection of the listed point stabilizers is either one such line or
the identity. The line is never `<J>`, because its generator has nonzero
`Z_1`-coordinate. The extra scalar coordinate is fixed by all of `C`
and does not alter this statement. Every `g` in the table commutes with
`C_A`, so `H'=H=C_A`. Thus `(QCT2)` never occurs in the table.

A constant Weyl conjugate merely permutes the active coordinate labels.
Repeating the same point-stabilizer intersection gives the identical
conclusion. This completes the bounded two-symbol no-go.
