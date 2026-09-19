# Sparse syndrome escape forces an infinite-cover obstruction

Date: 2026-08-11

## 1. Outcome

The bounded-weight primary lift obstruction isolated in
`FALSE_DECK_FOURIER_BINARY_REDUCTION.md` cannot be a purely finite-quotient
conditioning phenomenon.  A general compactness theorem shows:

> If binary syndromes have uniformly bounded support in a residual family
> of finite regular covers, belong to the finite-cover lift image, but their
> least integral lift norms tend to infinity, then after translating and
> clustering their supports, at least one fixed finite-support cluster is
> not liftable in the limiting infinite cover.

Applied to the prime-two invariant/anti-invariant cycle map, branch 3 of the
escape dichotomy produces a nonzero finite-support class in the cokernel of

`R_infinity:Z_infinity^+ directSum Z_infinity^-`
`              -> V_infinity`,
`R_infinity(u,v)=red_2(u-v)`,                          `(SSC1)`

where `Z_infinity^+` and `Z_infinity^-` are the integral invariant and
anti-invariant two-cycle lattices for the canonical involution, and
`V_infinity` is the space of finite-support `tau`-invariant mod-two
two-cycles.

Thus a uniform surjectivity theorem for `(SSC1)` on finite-support vectors
would eliminate the entire parity-only branch.  Conversely, if branch 3
really occurs, its source is a genuine local primary homology class in the
limit complex, with finite support independent of the covering level.

This result does not prove FALSE.  It replaces an unbounded sequence of
large finite integer programs by one fixed finite-support obstruction in an
infinite cover, plus a finite number of translates whose classes cancel
only after passage to the finite quotients.

## 2. Residual finite-cover setup

Let `Lambda` be a countable finitely generated group and

`Lambda=Lambda_0>=Lambda_1>=Lambda_2>=...`,
`intersection_n Lambda_n={1}`,                        `(SSC2)`

be normal finite-index subgroups.  Let `X_infinity` be a locally finite
cell complex with a free cocompact cellular `Lambda`-action, and put

`X_n=Lambda_n\X_infinity`.                            `(SSC3)`

Only the following consequences are used.

1. There are finitely many cell types.
2. Every finite set of cells of `X_infinity` embeds in `X_n` for all
   sufficiently large `n`.
3. Deck translation and quotient projection preserve every fixed local
   integral equation under consideration.

Let `V_infinity` be one cellular `F_2`-module of finite-support vectors,
and let `V_n` be its finite quotient.  Let `L_infinity` be an abelian group
of finite-support integral configurations defined by homogeneous,
finite-propagation linear equations, and let `L_n` be the corresponding
solution group on `X_n`.  Suppose there are equivariant homomorphisms

`R_infinity:L_infinity->V_infinity`,
`R_n:L_n->V_n`                                        `(SSC4)`

which commute with quotient projection.  Give `L_n` the Euclidean norm of
its ambient integral cellular coordinates and define

`kappa_n(epsilon)=min {||ell||:ell in L_n,`
`                              R_n(ell)=epsilon}.`     `(SSC5)`

The value is infinity outside the image.

The prime-two application takes

`L_n=Z_n^+ directSum Z_n^-`,
`R_n(u,v)=red_2(u-v)`,                                 `(SSC6)`

with the product Euclidean norm.  The equations defining the two cycle
lattices are local and equivariant, so this is a special case of `(SSC4)`.

## 3. Finite clustering lemma

For a binary vector, write `supp(epsilon)` for its set of nonzero cellular
coordinates and `weight(epsilon)` for its cardinality.

**Lemma 1 (bounded-support cluster extraction).**  Suppose

`weight(epsilon_n)<=M`                                `(SSC7)`

for a fixed `M`.  After passing to a subsequence, there exist

* an integer `1<=r<=M`;
* fixed nonzero finite-support vectors
  `epsilon^(1),...,epsilon^(r) in V_infinity`; and
* deck elements `g_(n,1),...,g_(n,r) in Lambda`

such that, in `V_n`,

`epsilon_n=sum_(j=1)^r g_(n,j) epsilon^(j)`           `(SSC8)`

for all sufficiently large `n`.  Distinct clusters separate:

`g_(n,i)^(-1)g_(n,j)` escapes every finite subset of `Lambda`
for `i!=j`.                                           `(SSC9)`

**Proof.**  Add zero entries if necessary so that every support is listed
by at most `M` typed cells.  Pass to a subsequence on which the number and
types of the support cells are constant.  Choose one support cell as an
anchor.  For each of the finitely many pairs of support cells, diagonalize
again: their relative deck displacement either is eventually one fixed
element of `Lambda`, or escapes every finite subset.

Put two support cells in the same cluster precisely when their relative
displacement is eventually fixed.  This is an equivalence relation.  After
translating one anchor of each equivalence class to a fixed fundamental
domain, its entire finite pattern is eventually constant and defines
`epsilon^(j)` in `X_infinity`.  Cells in different classes satisfy
`(SSC9)`.  Residual injectivity on each fixed cluster gives `(SSC8)` for all
large `n`.  End proof.

No metric growth estimate is hidden here.  The conclusion uses only
finiteness of the support and residual convergence of the covers.

## 4. Sparse lift compactness

**Theorem 2 (sparse syndrome compactness).**  Assume `(SSC2)--(SSC5)`.  Let
`epsilon_n in im(R_n)` satisfy `(SSC7)`.  If

`kappa_n(epsilon_n)->infinity`,                        `(SSC10)`

then in every cluster decomposition `(SSC8)` at least one template obeys

`epsilon^(j) notin im(R_infinity)`.                   `(SSC11)`

**Proof.**  Suppose instead that every template belongs to the image.
Choose fixed finite-support configurations `ell^(j) in L_infinity` with

`R_infinity(ell^(j))=epsilon^(j)`.                    `(SSC12)`

For large `n`, project the translated configurations
`g_(n,j)ell^(j)` to `X_n` and sum them.  Locality and equivariance of the
defining equations put the sum in `L_n`, while `(SSC8)` and `(SSC12)` give

`R_n(sum_j g_(n,j)ell^(j))=epsilon_n`.                `(SSC13)`

Even if quotient projection causes overlaps, the Euclidean norm is bounded
by the integral `L1` norm before projection.  Hence

`kappa_n(epsilon_n)`
` <=sum_j ||ell^(j)||_1`,                              `(SSC14)`

a constant independent of `n`.  This contradicts `(SSC10)`.  End proof.

The contrapositive is often the useful form.

**Corollary 3 (qualitative local decoder).**  If every finite-support vector
in `V_infinity` lies in `im(R_infinity)`, then for every fixed `M`, all
syndromes `epsilon_n in im(R_n)` of weight at most `M` have uniformly
bounded lift cost.

The bound may depend on `M` and on the limiting complex; no quantitative
claim is made.  This qualitative statement is sufficient to rule out the
bounded-weight divergent sequence from the parity-only branch.

## 5. Application to the Laurent prime-two tower

Use

`K_infinity=pi^(-1)(E(2))`, `K_n=pi^(-1)(L_n)`,       `(SSC15)`

and pass from the infinite `K_infinity`-cover to its finite quotients.  The
deck involution `tau` induced by `i_1(h)` commutes with the cellular
boundary.  Define

`Z_infinity^+={u:tau u=u, d u=0}`,
`Z_infinity^-={v:tau v=-v, d v=0}`.                   `(SSC16)`

Put

`V_infinity={epsilon in C_2^(fin)(X_infinity,F_2):`
`              d epsilon=0, tau epsilon=epsilon}`,    `(SSC16a)`

and define `V_n` similarly.  Reduction modulo two turns both signs into
`+1`, so `(SSC1)` lands in `V_infinity`.  The syndromes from the parity
split also lie in `V_n`: their integral boundary is even, and both sector
fills are invariant after reduction modulo two.

Suppose branch 3 of Corollary 6 in
`FALSE_DECK_FOURIER_BINARY_REDUCTION.md` occurs.  Theorem 7 there gives
syndromes `epsilon_n` with

`weight(epsilon_n)<=M`,
`epsilon_n in im(R_n)`,
`kappa_n(epsilon_n)->infinity`.                        `(SSC17)`

The full deck group does not preserve the two fixed `tau`-eigenspaces by
translation, so Theorem 2 must not be applied to `(SSC16)` with arbitrary
deck translates.  Here the affine boundaries are fixed, which gives a
stronger anchored compactness argument.

**Lemma 4 (bounded minimizers cannot wander).**  Let `c_n` be the projection
of one fixed finite-support integral chain `c_infinity`, and let `z_n` be a
minimum-norm integral solution of

`d z_n=c_n`, `tau z_n=+z_n` or `tau z_n=-z_n`.         `(SSC18)`

If `||z_n||<=C`, then after passing to a subsequence the `z_n` are
projections of one fixed finite-support solution on `X_infinity`.

**Proof.**  Join two support two-cells when their cellular boundaries share
a one-cell.  Decompose the support into connected components.  If the
boundary of one component is zero, remove the entire `tau`-orbit of that
component.  This preserves the sign equation and the prescribed boundary
and strictly lowers the norm, contrary to minimality.  Thus every remaining
component has nonzero boundary and hence meets `supp(c_n)`; distinct
components cannot cancel each other's boundary because sharing a boundary
one-cell would make them adjacent.

Every nonzero integral coordinate contributes at least one to squared norm,
so `z_n` has at most `C^2` support cells.  Each component is therefore
contained in the `C^2`-neighborhood of the fixed support of `c_n`.  Residual
injectivity identifies that neighborhood with the corresponding finite
neighborhood in `X_infinity` for all large `n`.  There are only finitely many
integral chains of norm at most `C` in that neighborhood.  Pass to a
constant subsequence.  End proof.

Choose minimum-norm bounded sector fillings `s_n^0,a_n^0` as in Theorem 7
of the preceding note.  Lemma 4 and residual injectivity give, after a
subsequence, fixed lifts `s_infinity^0,a_infinity^0` and hence one fixed
syndrome

`epsilon=red_2(s_infinity^0-a_infinity^0)`            `(SSC19)`

whose projection is `epsilon_n`.

**Corollary 5 (limiting primary obstruction).**  The finite-support vector
`epsilon` in `(SSC19)` is nonzero and satisfies

`epsilon notin`
` red_2(Z_infinity^+)-red_2(Z_infinity^-)`.            `(SSC20)`

Its weight is at most `M`.

**Proof.**  If `(SSC20)` failed, choose a finite-support pair
`(u_infinity,v_infinity)` lifting `epsilon`.  Projecting it to every large
finite cover would give

`kappa_n(epsilon_n)`
` <=sqrt(||u_infinity||_1^2+||v_infinity||_1^2)`,      `(SSC21)`

contrary to `(SSC17)`.  If `epsilon=0`, the zero pair gives the same
contradiction.  End proof.

Thus the parity-only branch implies non-surjectivity of one explicit
infinite-cover primary cycle map.  It is enough to prove the opposite
finite-support statement

`V_infinity`
` =red_2(Z_infinity^+)-red_2(Z_infinity^-)`            `(SSC22)`

to eliminate that branch.

Equation `(SSC22)` is intentionally stated as a target, not as a theorem.
It may fail because boundary and stabilizer homology impose local primary
charges.  If it fails, `(SSC20)` identifies the exact finite-support charge
that must be paired with the marked radical orbit.  If it holds, integral
escape must occur in one of the individual sign-sector radii, where the
Fourier-frame estimates remain available.

## 6. What remains for FALSE

There are now two sharply separated tasks.

1. **Local primary task.**  Decide `(SSC22)` or compute the finite-support
   cokernel class `(SSC20)`.
2. **Marked task.**  If `(SSC20)` exists, prove that its finite-cover
   cancellations have unbounded marked incidence.  If `(SSC22)` holds,
   analyze the escaping invariant or anti-invariant radius instead.

The theorem here prevents a third possibility in which bounded-support
syndrome escape is merely an ill-conditioned sequence with no limiting
algebraic obstruction.
