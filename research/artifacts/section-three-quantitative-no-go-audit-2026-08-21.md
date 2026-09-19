# Section 3 quantitative no-go audit

Date: 2026-08-21

This artifact audits three quantitative claims from the supplied Section 3
report against the current Cairn graph.  All norms below are normalized
Hilbert--Schmidt norms.

## 1. Twisted regular predicate traces

The untwisted firewall was already present in
`regular-trace-blocks-exact-local-predicate-return`, and native projective
basis atoms were classified in
`twisted-group-basis-forces-affine-context-support`.  The missing general
calculation is simpler: in a twisted group von Neumann algebra,

```text
p=sum_g c_g u_g,       p=p*=p^2
```

satisfies

```text
tau(p)=||p||_2^2=sum_g |c_g|^2.                       (S3A1)
```

Thus every nonzero finite predicate projection has positive canonical trace,
regardless of the cocycle.  Passing to the corresponding central-character
corner of a central extension makes this an honest group-representation
countermodel.  This is registered as
`twisted-regular-predicate-projections-have-positive-trace`.

## 2. What the inverse-square-root logarithm means

Let

```text
n(d)=2 floor(log_2 d)+4.                               (S3A2)
```

The Clifford capacity bound then asks a `d`-dimensional model to contain a
block of dimension at least

```text
2^(floor(n(d)/2)-1)=2^(floor(log_2 d)+1)>d.            (S3A3)
```

Suppose, as an additional decoder theorem, that `n(d)` challenge rows
`R_1,...,R_n` produce a complete-table Clifford map with error

```text
epsilon <= A (sum_j ||R_j||_2^2)^(1/2).                (S3A4)
```

All quantities in `(S3A4)` are normalized on the decoded invariant corner;
ambient energy additionally needs a positive-density carrier bound.

If every row is at most `delta`, then

```text
epsilon<=A sqrt(n(d)) delta.                           (S3A5)
```

For a central-sign separation `rho`, Gowers--Hatami plus the robust Clifford
capacity lemma applies once

```text
delta < min(1/16,rho/42)/(A sqrt(n(d))).               (S3A6)
```

This is the claimed `Theta(1/sqrt(log d))` same-model threshold.

The qualification in `(S3A4)` is load-bearing.  Current Cairn does not derive
a complete-table map from a growing local Clifford presentation with constant
`A`; the recorded normal-form conversion has an additional polynomial loss in
`n`.  Therefore `(S3A6)` is a correct ledger theorem and target rate, not a
new unconditional Clifford stability theorem.

The rate is sharp for rowwise normalized-HS bookkeeping.  On `n` equal
orthogonal blocks let the `j`th involution be `-1` on block `j` and `+1`
elsewhere.  Each residual from the identity has norm `2/sqrt(n)`, while every
block has one maximal local failure and the total squared row energy is `4`.
This is the orthogonal-block converse: no inference using only the maximum row norm
can replace `1/sqrt(n)` by a smaller order without an anti-localization
hypothesis.  The precise statement is
`clifford-total-energy-ledger-has-inverse-sqrt-log-critical-rate`.

### The exact same-model Dirac converse

The report's more germane converse is also correct.  Given `2m` exact
pairwise anticommuting self-adjoint Clifford generators, put

```text
A=(2m)^(-1/2)sum_i X_i,
Gamma=i^m X_1...X_(2m).
```

Direct Clifford cancellation gives

```text
A^2=1,       {A,X_i}=sqrt(2/m)1,       {A,Gamma}=0.   (S3A7)
```

On the irreducible module `d=2^m`, `A` is therefore a same-model near-extra
generator at error `Theta(1/sqrt(log d))`, with no reducing-block escape.
This is registered separately as
`dirac-average-is-a-sharp-near-extra-clifford-generator`.

The coefficient claim needs a normalization qualification.  The degree-one
Clifford expansion has coefficient `l2` norm exactly `1`, but coefficient
`l1` norm exactly `sqrt(2m)`.  Thus the `sqrt(2m)` upper bound is verified
with equality; any dimension-independent coefficient-mass or word-telescoping
bound must be weakened.  The exact involution identity comes from
anticommutator cancellation, not bounded coefficient mass.

## 3. The block-diagonal spectral-gap wall

For a block-diagonal tuple `U_s=direct_sum_b U_(s,b)`, every block projection
`p_b` commutes with every `U_s`.  Hence the adjoint Laplacian has

```text
span{p_b}_b subset ker Delta_Ad.                       (S3A8)
```

Even if each block has a uniform scalar adjoint gap, the global kernel is the
whole block-scalar algebra, not the global scalars.  A word error confined to
a block of trace `theta` has global norm at most `2 sqrt(theta)`.  Spectral
gap inside the block does not change either fact.

This refines the naturality obstruction in
`word-recursion-cannot-amplify-sublinear-summands`: it identifies the exact
extra zero modes of the proposed spectral-gap operator.  It is registered as
`block-diagonal-adjoint-gap-retains-the-block-scalar-kernel`.

## Dependency verdict

The three calculations are no-gos, not a nonhyperlinearity proof.  They leave
the same positive boundary:

1. twisted packet syntax must use a matrix-only operation rather than a
   universal tracial predicate return;
2. a Clifford challenge needs a dimension-uniform total-energy decoder such
   as `(S3A4)` plus anti-localization; and
3. spectral gap helps only after the block-scalar commutant has been coupled
   or a marked carrier is independently forced to have positive density.
