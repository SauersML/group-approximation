---
rg: 2
id: qutrit-full-leavitt-prefix-conjugator-proof
kind: proof
title: Build the qutrit phase-star conjugator from rectangular prefix equivalences
target: qutrit-full-leavitt-prefix-conjugator-realizes-phase-star
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
  - qutrit-two-to-one-phase-graph-requires-central-line-twist
  - qutrit-jacobson-central-line-twist-is-similarity-impossible
---

## 1. The two scalar normal forms

Write

```text
kappa = [0 1; 1 1] in GL_2(F_2).
```

On a three-cycle with coordinate vectors `v_0,v_1,v_2`, the basis

```text
v_0+v_1+v_2,       v_0+v_1,       v_1+v_2
```

puts the cycle matrix into `1 direct-sum kappa`. The permutation `J` has
nine three-cycles and fixes `star`. Hence an explicit scalar change of
basis `P_J in GL_28(F_2)` gives

```text
P_J^(-1) J P_J = N_J := I_10 direct-sum (I_9 tensor kappa).   (QLP4)
```

The element `h=J^2Z` translates the last coordinate by

```text
r |-> r+2-u_1.
```

It fixes the nine leaves with `u_1=2` and `star` pointwise and has six
three-cycles on the other leaves. The same cycle-by-cycle basis gives
`P_h in GL_28(F_2)` with

```text
P_h^(-1) h P_h = N_h := I_16 direct-sum (I_6 tensor kappa).   (QLP5)
```

The apparent obstruction is precisely the scalar multiplicity mismatch
`10 versus 16` and `9 versus 6`. The full Leavitt algebra removes it by
rectangular equivalences.

## 2. Explicit rectangular prefix matrices

For `m>=2` take the maximal binary comb prefix code

```text
D_m={0,10,110,...,1^(m-2)0,1^(m-1)}.
```

For a binary word `d=d_1...d_l` put

```text
s_d=s_(d_1)...s_(d_l),        t_d=t_(d_l)...t_(d_1).
```

Order `D_m` as displayed and define the row and column

```text
S_m=(s_d)_(d in D_m),         T_m=(t_d)_(d in D_m)^transpose.
```

The prefix relations give, exactly,

```text
T_m S_m=I_m,                  S_m T_m=1.                 (QLP6)
```

For positive `m,n` define the rectangular matrix

```text
A_(n,m)=T_n S_m in M_(n times m)(L).
```

Then

```text
A_(m,n)A_(n,m)=I_m,           A_(n,m)A_(m,n)=I_n.        (QLP7)
```

Now use row blocks `16+12` and column blocks `10+18` and set

```text
D = diag(A_(16,10), A_(6,9) tensor I_2),
D^(-1)=diag(A_(10,16), A_(9,6) tensor I_2).              (QLP8)
```

These are square `28`-by-`28` matrices despite their rectangular
diagonal blocks. Equation `(QLP7)` proves both products in `(QLP8)` are
`I_28`. Since the entries of every `A_(n,m)` are `t_d s_e` and the
scalar entries of `kappa` commute with them,

```text
D N_J=N_h D.                                             (QLP9)
```

Consequently

```text
g=P_h D P_J^(-1),
g^(-1)=P_J D^(-1)P_h^(-1)                               (QLP10)
```

are mutually inverse explicit matrices and `gJg^(-1)=h`. The largest
comb used is `D_16`, so all displayed prefix words have length at most
`15`.

The established equality `GL_28(L)=EL_28(L)` places `g` in the
elementary group. This also gives a literal finite-word statement, not
merely countability. Indeed the finite set

```text
{x_(ij)(a): i!=j, a in {1,s_0,s_1,t_0,t_1}}
```

generates `EL_28(L)`: root additivity makes coefficient sums, the
Steinberg commutator with a third index makes coefficient products, and
constant elementary permutations move between root positions. Thus
every elementary matrix over the finitely generated ring `L`, including
`g`, is a finite word in this fixed finite set. Formula `(QLP10)` is the
bounded-support atlas; no unlisted infinite sum or completion is used.

## 3. The intersection is exactly one line

It remains to exclude `gCg^(-1)=C`. This is where the full scalar
`C`-module, rather than only the fixed-space rank of `J`, is useful.

Over `F_2` the four nontrivial simple types of `C_3^2` correspond to the
four pairs of opposite nonzero characters, equivalently to the four
projective dual lines in `F_3^2`. On a leaf fibre with fixed
`(u_1,u_2)`, the element `J^aZ^b` translates `r` by

```text
a-bu_1.
```

Therefore the 27-leaf permutation module contains the three nontrivial
dual lines

```text
[1,0],             [1,-1],             [1,-2],
```

each with positive multiplicity, and omits exactly `[0,1]`. The fixed
coordinate `star` adds only a trivial summand. Equivalently, among the
four nontrivial central primitive idempotents of `F_2[C]`, exactly the
one indexed by `[0,1]` acts by the zero matrix.

Suppose `gCg^(-1)=C` and let `alpha` be conjugation by `g` on `C`.
Intertwining by an invertible matrix over `L` must permute the four
scalar central idempotent matrices and preserve which one is zero.
Thus `alpha` preserves the unique missing dual line `[0,1]`. Its
annihilator in `C` is `<J>`, so `alpha(<J>)=<J>`. But
`alpha(J)=h=J^2Z` is not in `<J>`, a contradiction.

This zero-versus-nonzero argument remains valid after scalar extension
from `F_2` to `L`; it does not compare finite module ranks. We have now
shown `gCg^(-1)!=C`. Both `C` and `gCg^(-1)` have order nine, and their
intersection contains `<h>`. Any larger intersection would have order
nine and make the two groups equal. Hence

```text
C intersect gCg^(-1)=<h>.                               (QLP11)
```

## 4. Exact Hecke blocks

Let `chi_a` be the character of `C` with
`chi_a(J)=omega` and `chi_a(Z)=omega^a`, and let `e_a` be its central
character projection. For

```text
H=C intersect gCg^(-1)=<h>,
H'=g^(-1)Hg=<J>,
```

the finite-subgroup Hecke criterion says that `e_bge_a` is nonzero
exactly when

```text
chi_b|H=(chi_a after Ad(g^(-1)))|H.
```

On the generator `h` the two sides are

```text
chi_b(h)=omega^(2+b),       chi_a(g^(-1)hg)=chi_a(J)=omega.
```

Thus compatibility is equivalent to `b=2`, independently of `a`. In
the canonical group trace the double-coset calculation gives

```text
||e_2 g e_a||_2^2=|H|/|C|^2=3/81=1/27.                 (QLP12)
```

This proves `(QLP1)` and `(QLP2)`.

## 5. What arbitrary canonical microstates must do

Put

```text
q=e_0+e_1+e_2,             R=e_0+e_1,
r_h=the omega-spectral projection of h.
```

Inside the commuting finite group `C`, on the `q` corner one has

```text
h=J^2Z,                    q r_h=e_2.                    (QLP13)
```

First consider an exact finite-dimensional representation of the finite
head and a unitary `G` satisfying `GJG^*=h`. Spectral projections are
polynomials of degree two, so

```text
GqG^*=r_h.
```

Since `R<=q`, equations `(QLP13)` imply

```text
qGR=e_2GR.
```

The range capacity and Pythagoras identities now give

```text
||qGR||_(2,n)^2 <= tr_n(e_2),
||(1-q)GR||_(2,n)^2
 =tr_n(R)-||qGR||_(2,n)^2
 >=tr_n(R)-tr_n(e_2).                                   (QLP14)
```

In any microstate for the canonical group trace, exactification on the
finite qutrit head gives

```text
tr_n(R)=2/9+o(1),             tr_n(e_2)=1/9+o(1).
```

If the conjugacy is only approximate, applying the degree-two spectral
polynomials changes `(QLP14)` by `o(1)` in normalized Hilbert--Schmidt
norm. Therefore

```text
||(1-q)GR||_(2,n)^2 >=1/9-o(1),                          (QLP15)
```

which is `(QLP3)`. The Hall excess is real, but it is forced to leak out
of `q` rather than producing a violated relator.

There is an exact finite-dimensional firewall. Let `F` be the finite
qutrit head and use its left regular representation. Every `C`-character
projection then has normalized rank `1/9`. The matrices `J` and `h` are
nonidentity elements of order three, so their regular matrices have the
same spectral multiplicities and are unitarily conjugate. Choose the
conjugating unitary on the `J=omega` eigenspace as a three-by-three
Fourier block between

```text
e_0 direct-sum e_1 direct-sum e_2
```

and the three equal-rank joint-character summands of `r_h`. Extend it
on the other two spectral thirds. The resulting unitary `U` satisfies

```text
UJU^*=h,
e_b U e_a=0 for b!=2,
||e_2 U e_a||_(2,n)^2=1/27                              (QLP16)
```

for every `a`. Thus even the complete Hecke norm table has an exact
regular finite-dimensional model when only the conjugacy router is
imposed.

Equivalently, the finitely presented HNN group

```text
widehat(Gamma)=<F,U | UJU^(-1)=h>
```

is an amenable-edge cover of the concrete matrix subgroup `<F,g>`.
The map `U|->g` is surjective onto that subgroup, but injectivity is not
proved. The edge groups `<J>` and `<h>` are finite, so the standard
amenable-edge HNN permanence theorem makes `widehat(Gamma)` hyperlinear.
This precisely locates the remaining burden: one needs an additional
relation in the kernel of this cover, involving the actual prefix
matrix and Leavitt root generators, that prevents the leakage in
`(QLP15)`. The matrix subgroup is faithfully realized and finitely
generated; finite presentability of that subgroup is left open.
