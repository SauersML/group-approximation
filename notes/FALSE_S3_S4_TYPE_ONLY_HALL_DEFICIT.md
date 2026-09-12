# The `S4 <- S3 -> S4` type graph is Hall-balanced

Date: 2026-08-13

## 1. Question

The raw source word localizes a fixed amount of Hilbert--Schmidt energy to
an `S3` subgroup, while the first hard class-11 pair expands that subgroup
through two `S4` subgroups which together generate `GL3(2)`.  This produces
the finite diagram

```text
S4 <- S3 -> S4.                                      (STH1)
```

Could the ordinary complex restriction types in `(STH1)` already give a
weighted Hall deficit in the finite chart multiplicity algebra?

No.  The exact branching graph is multiplicity-free and the regular vector
is perfectly balanced.

## 2. Branching matrix

Order the irreducibles of `S3` as

```text
1, sign, standard_2
```

and the irreducibles of `S4` as

```text
1, sign, two_dimensional, standard_3, standard_3*sign.
```

Up to the ordering returned by GAP, restriction has the five rows

\[
 \begin{array}{c|ccc}
 &1&\mathrm{sgn}&2\\ \hline
 1&1&0&0\\
 \mathrm{sgn}&0&1&0\\
 2&0&0&1\\
 3&1&0&1\\
 3\otimes\mathrm{sgn}&0&1&1.
 \end{array}
 \tag{STH2}
\]

Equivalently,

```text
1       |-> 1
sign    |-> sign
2       |-> standard_2
3       |-> 1 + standard_2
3 sign  |-> sign + standard_2.                       (STH3)
```

The regular `S4` representation contains these five types with
multiplicities `1,1,2,3,3`.  Applying `(STH2)` gives `S3` multiplicities

\[
 (4,4,8),                                               \tag{STH4}
\]

which are exactly four copies of the regular `S3` representation.

Thus every type weight arriving from an `S4` regular chart is accounted for
without deficit at the `S3` edge.  The same is true on the second `S4`
extension.  Copying or amplifying the diagram preserves this equality.

## 3. Consequence

No argument using only:

1. the three complex `S3` isotypic dimensions;
2. the five complex `S4` isotypic dimensions; and
3. the support incidence of restriction

can produce the required two-to-one Hall obstruction.  The regular chart is
an exact positive integral circulation on the entire graph.

This does not make the `S3` localization useless.  It says exactly what data
must be retained beyond type labels.  The live objects are the block maps on
the multiplicity spaces along the three nontrivial branching overlaps in
`(STH2)`.  In particular, the two three-dimensional `S4` types share the
standard `S3` channel with the two-dimensional type, so a unitary gauge can
mix three extension labels there.  The hard word must distinguish the two
child paths inside that shared channel.

The revised positive endpoint is:

> Extract from the hard prefix and comb relations two inequivalent block
> products through the standard `S3` channel, and prove that their ranges are
> orthogonal or create one-way leakage in the finite external multiplicity
> space.

Type counts alone cannot do this.  Singular values, kernels, or closed-loop
products of the actual branching arrows are required.

## 4. Replay

The exact GAP replay is

```text
experiments/atlas_s4_s3_branching.g
```

with committed output

```text
experiments/atlas-s4-s3-branching.txt
```

It constructs `S3` as a point stabilizer in `S4`, restricts all five complex
irreducible characters, and independently verifies `(STH4)`.

The resulting integral branching identity is independently kernel-checked
in `GroupApproximation/Leavitt/S3S4BranchingBalance.lean` as
`regular_restriction_balanced`.
