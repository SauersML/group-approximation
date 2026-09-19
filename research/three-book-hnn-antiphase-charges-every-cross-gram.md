---
rg: 2
id: three-book-hnn-antiphase-charges-every-cross-gram
kind: claim
title: A multiple-HNN book tag charges every overlap among the three equal-rank Fanizza exits
distinct_from:
  finite-tag-covariance-cannot-compress-eight-slice-orbit: that rules out placing three disjoint finite types isometrically inside the smaller parent; this allows leakage in exact representations and uses the matrix-only leakage bound to rule it out only in finite microstates.
  shared-context-pairwise-antiphase-v4-routing: that asks for pair-specific phases on five unequal V4 failure occurrences and meets a four-character ceiling; this uses the three already equalized book blocks, which two book axes separate exactly.
  pairwise-antiphase-covariance-controls-cross-gram: that is the abstract analytic estimate for supplied phases; this gives explicit book words, a finite group presentation, and algebraic completeness by Britton embedding.
---

Use the eight-slice sources of
`eight-slice-bookkeeping-symmetrizes-s3-failures`, but label the four book
supports involved in the sources by

```text
eta_0=000,       eta_1=100,       eta_2=010,       eta_3=110. (BHA1)
```

Thus

```text
G_0=F_00 e_(eta_0),
G_1=F_01(e_(eta_1)+e_(eta_2)),
G_2=F_11 e_(eta_3).                                      (BHA2)
```

Let the source book group be

```text
D=<a,b,c | a^2=b^2=c^2=1, [a,b]=[a,c]=[b,c]=1>.          (BHA3)
```

On the three source projections, the two words

```text
x=ab,       y=a                                             (BHA4)
```

have sign profiles

```text
x : (+,-,+),
y : (+,*, -),                                              (BHA5)
```

where the unused middle entry for `y` need not be scalar.  Consequently `x`
separates the pairs `(0,1)` and `(1,2)`, while `y` separates `(0,2)`.

### The finite marked extension

Let `Gamma_0` be any finitely presented marked base containing the embedded
book subgroup `D` and the fixed packet words defining `(BHA2)`.  First take
the direct product with a commuting copy

```text
D'=<a',b',c'> ~= C_2^3
```

so `D'` centralizes every generator of `Gamma_0`, in particular the target
capacity projection `C`.  Then adjoin three stable letters `u_0,u_1,u_2`
with the nine relations

```text
u_i a u_i^(-1)=a',
u_i b u_i^(-1)=b',
u_i c u_i^(-1)=c'             (i=0,1,2).                (BHA6)
```

This is a multiple HNN extension of the base `Gamma_0 times D'` along the two
embedded copies `D,D'`.  Britton's lemma embeds the base.  In particular,
every nontrivial marked word of `Gamma_0` remains nontrivial, and the
extension is finitely presented.  Its left regular representation is an
exact infinite-dimensional marked representation.  More generally, inducing
any exact marked base representation to the HNN extension retains a copy of
the base representation, so no tracial extension of the original witness is
needed.

### Exact and approximate antiphase

In a matrix tuple, after exactifying the fixed book/packet subgroup, put

```text
T_i=U(u_i)G_i.                                            (BHA7)
```

These are partial isometries with `T_i^*T_i=G_i`.  Set

```text
R_01=R_12=U(a'b'),       R_02=U(a').                     (BHA8)
```

The relations `(BHA6)` and signs `(BHA5)` give

```text
R_ij T_i=epsilon_(i,ij) T_i,
R_ij T_j=-epsilon_(i,ij) T_j.                            (BHA9)
```

exactly in an exact packet model.  For an approximate tuple define the six
covariance residuals by the two sides of `(BHA9)`.  Fixed-word telescoping
and fixed finite-group exactification give a constant `K_tag`, independent of
matrix dimension, such that

```text
E_tag=sum_(i<j)(||D_(i,ij)||_2^2+||D_(j,ij)||_2^2)
      <= K_tag E_rel+o(1).                               (BHA10)
```

Here `E_rel` includes the squared defects of the nine named relators and the
fixed packet relations.  Applying
`pairwise-antiphase-covariance-controls-cross-gram` yields

```text
O=sum_(i!=j)||T_i^*T_j||_2^2
 <= E_tag
 <= K_tag E_rel+o(1).                                    (BHA11)
```

Thus **every positive cross-Gram moment already pays ordinary relator
energy**.  No near-full overlap, polar unitary, spectral-cut invariance, or
smaller-reservoir gauge lock is required.

### Why the regular representation is not contradicted

The tag cell does not assert that the three ranges lie in the smaller target
capacity `C`.  In the regular representation `(BHA9)` makes the ranges
pairwise orthogonal, and they may escape into `(1-C)`.  This is precisely the
leakage alternative in `(NCL9)`.  Hence the construction does not violate
`finite-tag-covariance-cannot-compress-eight-slice-orbit`: it never attempts
an exact compression of three source blocks into the smaller parent.

Only the source-specific matrix estimate `(NCL13)` can make that leakage
cheap.  When `(NCL13)` holds, Gram capacity, localized non-CE leakage, and
`(BHA11)` leave neither overlap nor leakage available in matrices.  The exact
regular/infinite model is legal because `(NCL13)` is not a universal tracial
inequality.
