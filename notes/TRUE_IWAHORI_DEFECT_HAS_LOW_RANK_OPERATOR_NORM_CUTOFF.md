# Iwahori Hilbert--Schmidt defect has a low-rank operator-norm cutoff

Date: 2026-08-14

## 1. Outcome

Let

```text
D_1,...,D_m in M_d(C)                                  (DOC1)
```

be a finite family of matrix defects and use normalized Hilbert--Schmidt
norm.  If

```text
sum_j ||D_j||_2^2 <= delta^2,                           (DOC2)
```

then, for every `t>0`, there are domain and range projections `p,q` with

```text
tr(1-p), tr(1-q) <= delta^2/t^2                        (DOC3)
```

such that, simultaneously for every `j`,

```text
||D_j p||_op <= t,       ||q D_j||_op <= t.             (DOC4)
```

In particular,

```text
||q D_j p||_op <= t.                                    (DOC5)
```

Taking `t=sqrt(delta)` turns a defect of total squared normalized
Hilbert--Schmidt size at most `delta^2` into operator-norm defect at most
`sqrt(delta)` after deleting at most `delta` relative dimension on each
side.

Applied to the Dogon--Vigdorovich Iwahori matching problem, this proves that
every Hilbert--Schmidt near-matching already has an operator-norm near-matching
on large rectangular domain and range spaces.  Thus the unresolved
central-regular sequence cannot hide diffuse operator-norm error throughout
the physical matrix space.

This does **not** finish matching.  The cutoff projections are constructed
from the differences of the two edge representations and need not be
invariant under either representation.  Consequently their ranges are not
smaller edge representations, and arbitrary compression does not preserve
the group law.  The remaining theorem is now an invariant-cutoff repair:
replace these large analytic good spaces by large subrepresentations, using
the fact that the two edge actions extend through the opposite modular
vertices.

## 2. The two-sided cutoff lemma

**Lemma (rank/operator-norm decomposition).**  Let `D_1,...,D_m` be operators
on a `d`-dimensional Hilbert space and suppose `(DOC2)`.  Define

```text
Q_R=sum_j D_j* D_j,       Q_L=sum_j D_j D_j*.            (DOC6)
```

For `t>0`, put

```text
P=1_[t^2,infinity)(Q_R),
R=1_[t^2,infinity)(Q_L),
p=1-P,                    q=1-R.                         (DOC7)
```

Then `(DOC3)--(DOC5)` hold.

**Proof.**  Spectral Markov inequality gives

```text
t^2 tr(P) <= tr(P Q_R) <= tr(Q_R)
             =sum_j ||D_j||_2^2 <=delta^2.              (DOC8)
```

The same calculation with `Q_L` proves the bound for `R`.  Since
`D_j*D_j <= Q_R` and `p` is the spectral projection of `Q_R` below `t^2`,

```text
(D_j p)*(D_j p)=p D_j*D_j p <=p Q_R p <=t^2 p.           (DOC9)
```

Therefore `||D_j p||_op<=t`.  Similarly,

```text
(q D_j)(q D_j)*=q D_jD_j* q <=q Q_L q <=t^2 q,          (DOC10)
```

so `||qD_j||_op<=t`.  Multiplication by a projection is contractive in
operator norm, which gives `(DOC5)`.  This proves the lemma.

The proof is dimension-free and the number of defects enters only through
the total energy in `(DOC2)`.

## 3. Application to exact edge representations

Let

```text
rho,sigma:B->U(d)                                      (DOC11)
```

be the exact restrictions of the two modular-vertex representations and let
`S` be the fixed finite edge generating set used in the matching problem.
Put

```text
D_s=rho(s)-sigma(s),
delta^2=sum_(s in S) ||D_s||_2^2.                       (DOC12)
```

The lemma supplies large projections `p,q` for which

```text
||q rho(s) p-q sigma(s) p||_op <=t                     (DOC13)
```

for every `s in S`.  If `delta_n->0` along a putative negative sequence and
we take `t_n=sqrt(delta_n)`, then

```text
tr(1-p_n),tr(1-q_n)->0,
max_(s in S)||q_n(rho_n(s)-sigma_n(s))p_n||_op->0.       (DOC14)
```

This is stronger than the original normalized Hilbert--Schmidt estimate on
the surviving rectangular block.  It also explains why the remaining
outlier from
`TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md` is necessarily an
invariance problem rather than an operator-norm magnitude problem.

## 4. Why arbitrary compression is invalid

Neither `Q_R` nor `Q_L` generally commutes with `rho(B)` or `sigma(B)`.
Indeed, conjugating one summand `D_s*D_s` by an edge generator changes it
into an expression involving a different pair of group words.  A fixed
finite generating set is not closed under all such conjugations in the
infinite edge group

```text
B/<z> ~= Z*C_2.                                        (DOC15)
```

It follows that `pH` and `qH` need not carry compressed representations.
For example, even though `(DOC13)` is meaningful as a rectangular operator
estimate, the expression

```text
p rho(g) p rho(h) p                                    (DOC16)
```

need not equal or approach `p rho(gh) p` in operator norm unless `p` is
also approximately invariant.  The cutoff lemma therefore cannot be fed
directly into operator-norm stability or a finite-dimensional dimension
count.

Nor can one average the cutoff over `B` by a Følner argument: the relevant
central quotient `(DOC15)` is nonamenable.  This is the same nonamenability
that produced the positive regular spectral bottom in the outlier
localization theorem.

## 5. Exact remaining gate

The analytic part of the desired repair can now be stated without ambiguity.
A positive Iwahori matching theorem would follow from the following
representation-theoretic assertion.

> **Invariant-cutoff repair.**  Suppose exact edge representations `rho_n`
> and `sigma_n` arise by restriction from representations of the two
> opposite copies of `SL_2(Z)` and their finite-generator matching defect
> tends to zero in normalized Hilbert--Schmidt norm.  Then the spectral good
> spaces `p_n,q_n` from `(DOC7)` can, after deleting `o(d_n)` further
> dimensions and making `o(1)` normalized Hilbert--Schmidt perturbations, be
> replaced by equally sized invariant subspaces on which the restricted
> edge representations are unitarily equivalent.

Once such invariant subspaces exist, their complements have dimension
`o(d_n)` and are exactly the flexible padding permitted by the matching
problem.  The large restrictions glue, so the Dogon--Vigdorovich positive
matching criterion applies and their explicit central extension is
nonhyperlinear.

This gate is strictly narrower than general Hilbert--Schmidt stability.  It
only concerns two exact edge representations with modular-vertex origins,
and the cutoff lemma has already upgraded their disagreement to
operator-norm-small on all but vanishing physical dimension.  What remains
is to make that large good geometry representation invariant.

## 6. Relation to the sparse mixed outlier

The mixed-Laplacian reduction showed that the almost-intertwining identity is
concentrated in an `o(d^2)` operator-space outlier.  The present lemma gives
the complementary physical-space statement:

```text
HS-small edge mismatch
 => operator-norm-small mismatch off o(d) domain/range rank. (DOC17)
```

These statements do not imply one another by dimension counting, because an
operator-space line can contain a full-rank matrix.  Together they isolate
the same final phenomenon from both sides.  A negative sequence must carry a
full-rank near-intertwiner in a sparse commutant bimodule while simultaneously
preventing the large operator-norm-good physical block from being replaced
by an invariant block.  Any successful counterexample or repair theorem must
therefore exploit the extension data at the two modular vertices.
