# The normal lamp kernel cannot supply the missing Kazhdan corner

Date: 2026-08-12

## 1. Exact statement

Let a group `G` act on an infinite set `X`, let `K` be a nontrivial finite
group, and put

`B_sum=directSum_X K`,
`W=B_sum semidirect G`.                                  `(LRT1)`

Then

`(W,B_sum)` does not have relative property `(T)`.       `(LRT2)`

This applies even when `G` has property `(T)` and even when the action on
`X` is transitive.  In particular it applies to the Kun--Thom action
`X=G/Gamma`.

There is also a free-lamp version.  Put

`B_free=freeProduct_(x in X) K_x`,
`H_free=B_free semidirect G`.                           `(LRT3)`

Then

`(H_free,B_free)` does not have relative property `(T)`. `(LRT4)`

## 2. Primary-source proof for the commuting lamps

Neuhauser defines the support length

`s(b,g)=|supp(b)|`                                     `(LRT5)`

on a permutational wreath product.  Proposition 3.2 of *Relative property
(T) and related properties of wreath products* proves that if `s` is
unbounded on a subgroup `U`, then `(W,U)` does not have relative property
`(T)`.

For `U=B_sum`, support length is unbounded because `X` is infinite and
`K!=1`: products of one fixed nonidentity lamp on arbitrarily large finite
subsets have arbitrarily large support.  Neuhauser's proposition therefore
gives `(LRT2)` directly.

The proof is quantitative in the only direction relevant here.  It builds
normalized positive-definite functions which converge pointwise to one on
`W`, while their restrictions to `B_sum` stay uniformly separated from the
cone required by relative property `(T)`.  Thus no choice of Kazhdan set in
the ambient group can restore a spectral gap for the whole normal lamp
kernel.

## 3. Free lamps

There is a quotient

`q:H_free -> W`                                        `(LRT6)`

which is the identity on `G` and abelianizes the distinct lamp factors into
the corresponding commuting coordinates.  It maps `B_free` onto `B_sum`.

Pull back Neuhauser's positive-definite functions along `q`.  They converge
pointwise to one on `H_free`.  If `(H_free,B_free)` had relative property
`(T)`, their restrictions to `B_free` would converge uniformly in the
relative-`(T)` sense.  Since they factor through `B_sum`, this would give the
forbidden conclusion for `(W,B_sum)`.  Hence `(LRT4)` follows.

This quotient argument is also visible at the representation level: the
pulled-back representations have no nonzero `B_free`-fixed vector because
their `B_free`-fixed vectors are exactly their `B_sum`-fixed vectors.

## 4. Consequence for norm-to-trace amplification

The tempting shortcut was to use a norm-continuous projection onto the
lamp-fixed vectors, cut an operator-norm model to its complement, and
renormalize the matrix trace there.  Relative property `(T)` of a pair would
not by itself produce that projection: for a normal subgroup `N normal H`,
the normal-subgroup ideal in `C*_max(H)` is unital exactly when `N` itself
has property `(T)`.  This sharper C-star criterion is proved in
`FALSE_NORMAL_SUBGROUP_CORNER_EQ_PROPERTY_T.md`.  Equations `(LRT2)` and
`(LRT4)` additionally show that even the weaker pair property fails for the
two Kun--Thom lamp kernels.

This rules out a whole-group lamp-corner argument, not every finite-sector
corner.  Central finite torsion still gives an honest spectral projection,
and the global property-`(T)` vertex still gives its ordinary Kazhdan
projection.  What fails is precisely the projection needed to turn the
entire infinite lamp orbit into one uniformly controlled nonfixed sector.

Therefore the live FALSE construction still has to obtain trace mass from
the noncentral paired carry/Frobenius incidence itself.  It cannot get that
mass for free from relative property `(T)` of the normal lamp subgroup.

## Source

M. Neuhauser, *Relative property (T) and related properties of wreath
products*, Math. Z. 251 (2005), 167--177, especially Proposition 3.2 and the
proof of Theorem 1.2.
