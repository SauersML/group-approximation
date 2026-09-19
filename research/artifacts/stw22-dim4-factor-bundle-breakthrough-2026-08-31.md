# STW XXII: all-factor dimension-four breakthrough audit

## New diffuse degree

The universal diffuse Stiefel `S^2` theorem upgrades projection
Grassmannians and corner stabilizers to two-connected equi-`LC^2`
families. Michael selection with `n=2` therefore selects an inclusive
spectral supercarrier over `S^3`; two further `n=2` stabilizer selections
and localized Jekel contractions give a factor-uniform Stiefel `S^3`
modulus. The dyadic relative recursion over `B^4` uses Michael with `n=3`,
and the exact row amplification transfers it to arbitrary weighted copies.
The diffuse weighted modulus is `epsilon_0^3/216000000`.

## Sharp matrix split

For a matrix weighted fibre with total polar rank `k` and unused rank
`c=n-k`, the independently audited matrix theorem proves the weighted
`S^3` modulus `epsilon_0^3/276480` and global three-connectivity when
`c>=2`. For `c=1`, block-SU2 generators are essential and have normalized
radius at most `sqrt(8/n)`, so no modulus exists for all merely-positive
slack values.

The trace theorem avoids exactly that obstruction. Its replication values
satisfy `m>=2` and `m tau(supp(a))<=1/2`. For a nonzero matrix weight,

```text
k=m rank(supp(a))>=2,       k<=n/2,       c=n-k>=2.
```

Thus the diffuse modulus, the smaller of the two positive moduli, works
for every finite factor value used in the gap argument.

## Selection checklist

```text
base:       compact Hausdorff, paracompact, dim <=4
ambient:    one complete (ell^2)^m from countable stabilization
graph:      nonempty closed operator-ball values, type-free lsc
topology:   common LC^0, LC^1, LC^2, LC^3; global C^3
selection:  Michael n=3
recovery:   operator-ball identity returns selected L2 sections to M
```

Factor type and matrix size may vary: the graph estimate was already
type-free, while the topological case split has one common numerical
modulus and is pointwise.

## Gap quantifiers

For every `m>=2`, the spectral cut uses an `m`-dependent neighbourhood and
a central cutoff equal to one at the base point. Hence the quotient class
is unchanged and `m sigma([c])<=||sigma||`. Letting `m` tend to infinity
and then removing the spectral cut kills every bounded positive fibre-gap
trace.

Independently audited inputs: the diffuse Stiefel `S^3` supercarrier, the
relative low-spectrum `B^4` recursion, the rectangular weighted transfer,
the matrix codimension-two carrier/Chern theorem and SU2 obstruction, and
the existing stabilized lower-semicontinuity/operator-recovery theorem.