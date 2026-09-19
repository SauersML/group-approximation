# The full two-depth overlap does not contradict finite multiplicities

This audits the proposed terminal step from the newly identified depth-one
and depth-two packets. It computes their actual intersection, gives an exact
finite-dimensional model of every branching restriction across that
intersection, and exhibits a short mixed relation outside those tests.
It does not supply a marked-word kill estimate for the full Leavitt group.

Use the conventions and prefix matrices of
`weighted-leavitt-opposite-root-packets-have-finite-models`. In
`EL_3(L_2(F_p))`, let

```text
F_r=<x_12(t_u), x_23(s_u), x_31(1): |u|=r>
    ~= SL_(2^r+2)(F_p).
```

## 1. The actual overlap is SL2 times SL2

Write `C` for a scalar two-by-two matrix acting on the outer rows `(1,3)`
and write `c_A=sum_(i,j) A_ij s_i t_j` for the level-one core matrix acting
on row `2`. Then

```text
F_1 intersect F_2
 = K
 = {diag_((1,3),2)(C,c_A): C,A in SL_2(F_p)}
 ~= SL_2(F_p) x SL_2(F_p).                            (TO1)
```

Here is the complete intersection calculation. Every element of `F_r`
belongs to the weighted ring with row weights `(0,r,0)`. Entries between
row `2` and the outer rows therefore have degree `r` or `-r`. Membership
in both weighted rings forces those entries to vanish, since the grading
is a direct sum. The outer block is scalar in both finite packets. The
middle entry belongs to the level-one finite core, which embeds into the
level-two core as `A -> A tensor I_2` by prefix refinement. Under the two
finite matrix identifications, the element is consequently

```text
diag(C,A) in SL_4(F_p),
diag(C,A tensor I_2) in SL_6(F_p).
```

Their determinant conditions are

```text
det(C) det(A)=1,       det(C) det(A)^2=1.
```

Thus both determinants equal one. Conversely these conditions put the
displayed block element into both finite groups. The two commuting block
factors embed injectively, proving `(TO1)`. In particular, for `p=2` the
full overlap is `S_3 x S_3`, not merely the cyclic subgroup of the mark.
Both `x_13(1)` and the common opposite root `x_31(1)` lie in its outer
`SL_2` factor.

## 2. Every branching multiplicity constraint has an exact finite solution

Take `N` to be any common multiple of `|F_1|` and `|F_2|`. On `N` points,
let the first action be `N/|F_1|` copies of the regular `F_1` action and the
second be `N/|F_2|` copies of the regular `F_2` action. Their restrictions
to the actual subgroup `K` are both exactly `N/|K|` copies of its regular
action. Choose a `K`-equivariant bijection to identify these two sets.
The resulting permutation matrices obey all identities internal to both
finite groups and agree on every element of the full intersection.

The mark `w=x_13(1)` acts without fixed points, so

```text
tr_N(w)=0,       ||w-I||_2^2=2.                       (TO2)
```

This is already an exact finite model; arbitrary simultaneous amplification
retains the same normalized data. The construction also displays all
complex irreducible multiplicities explicitly. For `sigma` irreducible
in `F_i` and `tau` irreducible in `K`, set

```text
m_i(sigma)=N dim(sigma)/|F_i|,
m_K(tau)=N dim(tau)/|K|.
```

The regular-representation restriction identity gives

```text
sum_sigma m_i(sigma) [Res_K(sigma):tau]=m_K(tau)
```

for each `tau` and for both `i`. These are integral, nonnegative
multiplicities in an actual common matrix space, not merely formal
normalized densities. Thus the finite `SL_4/SL_6` overlap and its complete
branching tables cannot yield any inequality forcing the marked distance
to vanish when chart and overlap defects vanish.

This result concerns the amalgamated finite-chart relations. It does not
assert that this permutation model satisfies the other mixed identities
in `EL_3(L_2(F_p))`.

## 3. A length-eight mixed word is already outside the overlap information

Fix `j in {0,1}` and use the depth-one and depth-two notation

```text
a=X_0=x_12(t_0),          c=X_1=x_12(t_1),
b=Y_(0j)=x_23(s_0 s_j),  d=Y_(1j)=x_23(s_1 s_j).
```

In the Leavitt elementary group,

```text
[a,b]=x_13(s_j)=[c,d],
R_j=[a,b][c,d]^(-1)=1.                                (TO3)
```

But `R_j` is nonidentity in the abstract amalgam `F_1 *_K F_2` with the
actual embeddings `(TO1)`. Indeed its normal form is

```text
a | b | a^(-1) | b^(-1)d | c | d^(-1) | c^(-1).
```

All seven factors lie outside `K`, alternating between the two factors.
For the only combined factor,

```text
b^(-1)d=x_23((s_1-s_0)s_j) notin K.
```

Its coefficient is nonzero: multiplication on the left by `t_1` gives
`s_j`, and `t_j s_j=1`. It is an off-diagonal middle-to-outer entry,
whereas every member of `K` has that entry zero. The other factors are
likewise nonzero native arms outside `K`. The reduced-word theorem for
an amalgam therefore proves nontriviality of `R_j` there.

This identifies an explicit missing datum: equality of two mixed
commutators, whose common value has outer-root coefficient degree one.
Neither the shared mark, the whole common opposite-root `SL_2`, nor any
scalar branching restriction on the full overlap authenticates this
equality. Its matrix defect depends on the relative placement of the two
finite chart representations, which the compatible multiplicities leave
free. No estimate controlling that placement, or proving a positive
normalized defect for a sufficient mixed packet, has been obtained here.
In particular, `(TO3)` alone is not claimed sufficient for marked collapse.

The next terminal argument must use such genuinely mixed occurrence
relations. The two-depth generation theorem supplies their algebraic
reach, but the exact overlap calculation rules out obtaining the desired
uniform contradiction solely from finite subgroup branching multiplicities.
