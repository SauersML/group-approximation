---
rg: 2
id: role-hyperoctahedral-type-has-an-orthogonal-amalgam-model
kind: claim
title: The role-hyperoctahedral type realizes every hybrid row locally but its D8 amalgam does not saturate the common source
distinct_from:
  dihedral-spin-packet-supplies-common-partial-swap: that extracts the common partial swap from the whole marked D8 spin sector; this puts a selected hyperoctahedral truth-table type on that swap and then gives an exact orthogonal-carrier countermodel to saturation.
  finite-role-packet-cannot-supply-hybrid-predicate-row: that rules out a hybrid row acting with the prescribed scalar table on every marked representation of one finite packet; this constructs the row on one selected irreducible type and shows exactly why selection does not promote to the marked source.
  all-bcs-contexts-share-one-hyperoctahedral-signed-type: that equalizes the local type dimension and assignment-atom ranks across contexts; this additionally installs the D8 role swap and audits a two-context amalgam over that common D8.
  finite-product-selected-type-mark-does-not-align-carriers: that gives the abstract C2 free-product failure of positive projection products; this preserves the complete regular character on both actual role-hyperoctahedral vertex packets while making their selected D8 source halves orthogonal.
---

Fix a nonempty allowed set

```text
R subset {+1,-1}^k
```

and choose `D>=2` divisible by `|R|`.  Put

```text
X=R times [D/|R|],
Omega={0,1} times X,
m=|Omega|=2D,
H=(C_2)^Omega semidirect S_Omega.                         (RHA1)
```

Let `T` be the tautological signed-permutation representation of `H` on
`C^Omega`.  The following two statements are exact.

1.  The packet `H` contains the D8 common swap, and every Boolean table on
    `R` has a literal role-labelled hybrid row on `T`.
2.  If two copies of `H` are amalgamated only over that D8, there is an exact
    finite-dimensional representation which is regular on both vertex
    packets but in which their selected `T`-source projections are
    orthogonal.

Thus the existing hyperoctahedral selected type and the D8 swap are locally
compatible.  Their bare finite amalgam does **not** prove the missing
selected-type/source-saturation statement.

## The literal local packet

Write a sign vector in `(C_2)^Omega` as its diagonal action on the coordinate
basis.  Define

```text
y(r,a,t)=-1,
z(r,a,t)=(-1)^r,                                         (RHA2)
```

and let `j` be the permutation

```text
j(r,a,t)=(1-r,a,t).                                      (RHA3)
```

Then

```text
y^2=z^2=j^2=1,       y central,       zj=yjz.             (RHA4)
```

Hence `<z,j,y>` is the marked D8 packet.  Relative to the `z` grading of
`T`, the matrix of `j` is

```text
J=[[0,I_D],[I_D,0]],                                     (RHA5)
```

so its off-diagonal block is the full common partial swap.

For a context variable `x_i`, let `d_i` be the diagonal sign

```text
d_i(r,a,t)=a_i.                                          (RHA6)
```

For **any** Boolean function `g:R->{0,1}`, let

```text
e_g(r,a,t)=(-1)^((1-r)g(a)).                             (RHA7)
```

These are literal elements of the diagonal subgroup of `H`.  On `T`,

```text
T(d_i)=diag(A_i,A_i),
T(e_g)=diag((-1)^g(A_1,...,A_k),I_D).                    (RHA8)
```

This is exactly the desired hybrid role row.  In particular, if `g` is the
rejection predicate of `R`, its selected-type compression is the identity,
because the joint spectrum of the `A_i` is precisely `R`.

The representation `T` is irreducible.  Indeed, the diagonal subgroup has
`m` distinct coordinate characters, so an invariant subspace is a sum of
coordinate lines; transitivity of `S_Omega` leaves only zero and the whole
space.  Let

```text
q_T in C[H]                                               (RHA9)
```

be its primitive central idempotent.  Since `y=-I` on `T`,

```text
q_T <= p_-=(1-y)/2.                                      (RHA10)
```

The normalized regular traces are

```text
tau_H(q_T)=m^2/|H|=m^2/(2^m m!),
tau_H(p_-)=1/2.                                          (RHA11)
```

Thus the chosen type has a fixed positive Plancherel mass, but it is a
strictly smaller part of the marked D8 source.  For `m>=4`,

```text
tau_H(q_T)<=1/4.                                         (RHA12)
```

## Exact orthogonal-carrier amalgam

Take two copies `H_1,H_2` of `H`, identify their displayed D8 subgroups, and
form

```text
G=H_1 *_(D8) H_2.                                        (RHA13)
```

There is a representation `pi:G->U(|H|)` such that

```text
pi|_(H_i) is unitarily equivalent to Reg(H)  (i=1,2),
pi(q_(T,1)) pi(q_(T,2))=0.                               (RHA14)
```

Consequently, if

```text
Q_i=pi(q_(T,i)) (1-pi(z))/2                              (RHA15)
```

is the selected initial half of the D8 swap for context `i`, then

```text
Q_1 Q_2=0.                                               (RHA16)
```

### Proof

Start with the left regular representation `lambda` of `H`.  Its restriction
to D8 is `[H:D8]` copies of the D8 regular representation.  The `y=-1`
space is therefore one D8-spin isotypic component

```text
p_- C[H] = C^2 tensor C^M,       M=|H|/4.                (RHA17)
```

Because `q_T` commutes with D8 and lies below `p_-`, Schur's lemma writes

```text
lambda(q_T)=I_2 tensor P                                (RHA18)
```

for a projection `P` on the D8 multiplicity space.  Its rank is
`m^2/2`.  Inequality `(RHA12)` is exactly

```text
2 rank(P)<=M.                                           (RHA19)
```

Choose a unitary `u` on `C^M` which sends `ran(P)` to a subspace orthogonal
to `ran(P)`.  Extend

```text
U=I_2 tensor u                                           (RHA20)
```

by any D8-commuting unitary on the `y=+1` space.  Then `U` commutes with the
whole D8 action and

```text
lambda(q_T) U lambda(q_T) U^*=0.                        (RHA21)
```

Represent `H_1` by `lambda` and `H_2` by `U lambda(.) U^*`.  The two
representations agree on the amalgamated D8, so the universal property of
`(RHA13)` gives `pi`.  Both vertex restrictions are regular, while `(RHA21)`
gives `(RHA14)`.  Since each selected idempotent commutes with the shared
`z`, equation `(RHA16)` follows.

The estimate `(RHA12)` is elementary: at the smallest case `m=4`,
`m^2/(2^m m!)=1/24`; the denominator-to-numerator ratio strictly increases
after that.

## What this proves and what it does not

Every trace test internal to either finite vertex packet is perfect in
`(RHA14)`: nonidentity vertex elements have normalized trace zero.  The
central mark also has its canonical profile, and the common D8 swap is
literal.  Nevertheless the two selected truth-table carriers have no common
source at all.

Therefore neither

```text
common D8 source
+ one common hyperoctahedral type at every context
+ canonical regular trace on every finite packet                         (RHA22)
```

implies the common-source hypothesis required by the game decoder.  A
successful construction must add a genuinely mixed cross-context moment or
an infinite/matrix-only actuator which charges the relative rotation in the
D8 multiplicity space.

This is not a no-go for selected-type compilers.  The first half proves the
local packet exists.  It is a no-go for claiming that finite-packet
amalgamation over the D8 role cell performs source saturation by itself.

## Attempts and firewalls

- **Select by the central sign `y=-1`.**  Equation `(RHA11)` shows that the
  selected tautological type occupies only a small part of that sector.
- **Demand canonical packet traces.**  Both factor restrictions in
  `(RHA14)` are exactly regular, so all such local tests already hold.
- **Use the same D8 generator `j` in every context.**  The conjugating
  unitary `U` commutes with D8, so it fixes `j,z,y` while rotating only the
  external spin multiplicity.
- **Infer common mass from equal selected ranks.**  The two selected
  projections have exactly equal rank and are nevertheless orthogonal.
- **Conclude that no mixed relator can work.**  That is not proved.  A mixed
  relator whose defect detects `U` outside the stabilizer of `P` is precisely
  the missing source-saturation mechanism.
