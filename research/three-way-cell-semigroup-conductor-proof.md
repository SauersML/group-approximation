---
rg: 2
id: three-way-cell-semigroup-conductor-proof
kind: route
title: Use affine-semigroup normalization and a cyclic twisted ladder
target: three-way-cell-semigroups-have-conductor-but-unbounded-charge
requires:
  - bs14-two-exit-typed-transport-is-not-saturated
  - bs14-native-cell-padding-preserves-lattice-charge
---

## The fixed-support conductor

Write `S=S_E`, `L=L_E`, and `Sbar=C_E intersect L_E`.  By Gordan's lemma,
`Sbar` is a finitely generated affine semigroup.  More precisely, the
normalization of the affine semigroup `S` is finite as an `S`-module, so
there is a finite set `F subset Sbar` with

```text
Sbar=union_(f in F) (f+S).                                  (TSP1)
```

Every `f in F` belongs to the group `L=gp(S)`.  Choose `p_f,q_f in S` with

```text
f=p_f-q_f.                                                  (TSP2)
```

Set

```text
c=sum_(f in F) q_f in S.                                   (TSP3)
```

For each `f in F`,

```text
c+f=p_f+sum_(f'!=f)q_(f') in S.                            (TSP4)
```

If `z in Sbar`, write `z=f+s` using `(TSP1)`.  Then

```text
c+z=(c+f)+s in S,
```

which proves `(TSC2)`.  The argument uses only finiteness of the fixed cell
support.  It gives no uniform bound on the size of `c` when the support
moves.

## A charge of exact order `n`

For the support `(TSC3)`, give every `c_i` coefficient `m/n` and every
`d_i` coefficient `1-m/n`.  At source label `i` the two incident
coefficients sum to one.  At first-exit label `j`, the incident cells are
`c_j` and `d_(j-1)`, whose coefficients also sum to one.  The two
second-exit margins are `m` and `n-m`.  Hence the integral vector `(TSC4)`
lies in the real cone `C_(E_n)`.

Define a homomorphism from the integral margin lattice to `Z/n` by

```text
omega(s,e,k)
 =-sum_(i in Z/n) i s_i
   +sum_(j in Z/n) j e_j
   -k_1                         mod n.                 (TSP5)
```

Every allowed column has zero charge:

```text
omega(c_i)=-i+i=0,
omega(d_i)=-i+(i+1)-1=0.                               (TSP6)
```

Thus `omega` vanishes on `L_(E_n)`.  On `(TSC4)` the first two sums cancel
and

```text
omega(TSC4)=-(n-m)=m mod n.                            (TSP7)
```

For `1<=m<n`, this proves `(TSC4)` is outside the cell lattice, hence cannot
be repaired by adding cells from the same support.

Take `m=1`.  Multiplying the fractional coefficients above by `n` gives
integer coefficients

```text
n*(1/n)=1 on every c_i,
n*(1-1/n)=n-1 on every d_i.                            (TSP8)
```

Therefore `n` times the margin vector belongs to `S_(E_n)`.  Its lattice
class has order at most `n`; `(TSP7)` maps it to `1 in Z/n`, so its order is
at least `n`.  The order is exactly `n`, proving the unbounded-charge
assertion.
