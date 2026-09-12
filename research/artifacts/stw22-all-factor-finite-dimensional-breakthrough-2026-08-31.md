# Audit: arbitrary mixed finite factors over every finite-dimensional base

## Verdict and scope

For each fixed finite sphere degree `j>=2`, half-slack replication with
`m>=ceil(j/2)` gives one globally `j`-connected, equi-`LC^j` family of
weighted-copy values over every separable-predual finite factor. Consequently
every countably generated factorial tracially complete C-star algebra over
any finite-dimensional compact Hausdorff base has only integral, uniform
traces, even with arbitrary variation of matrix size, diffuse II1
isomorphism class, and matrix/diffuse type.

The conclusion is degreewise. It does not cover infinite-dimensional bases
or non-countably-generated bundles, and it does not assert a positive
modulus uniform over all degrees.

## Matrix-diffuse dichotomy

For the matrix branch write

```text
k=m rank(supp(a)),       c=n-k.
```

Half slack gives `c>=k>=m` for every nonzero weight. Thus
`m>=ceil(j/2)` implies `2c>=j`, exactly the sharp stable range of the
audited matrix carrier/Bott induction. Its degree-`j` weighted radius is

```text
min(epsilon,1)^3/(276480 C_j).
```

The even-degree proof uses the finite-Grassmannian classification by the
trivial complementary bundle after rank promotion; it does not infer
nullity from a potentially unstable even unitary homotopy group. Below the
range, the explicit shrinking generator of
`pi_(2c+1)(V_(n-c)(C^n))=Z` shows why merely positive slack cannot yield a
joint degreewise modulus.

In a diffuse II1 factor, half slack is strict slack and the audited
supercarrier/relative-band induction supplies every finite degree with
radius `min(epsilon,1)^3/216000000`. The smaller of the two radii is common
to both branches. For a fixed `j`, the finite minimum over lower degrees,
together with the existing path and loop estimates, gives the full
equi-`LC^j` package. Countable generation supplies separable-predual
diffuse fibres.

## Selection-index check

For `D>=3`, put `j=D-1`. Michael's theorem with index `j` applies
because

```text
dim(K)=D=j+1,
values are closed and lower semicontinuous in one complete Hilbert target,
values are j-connected and form an equi-LC^j family.
```

Stabilization and operator-ball recovery are independent of factor type.
The cases `D<=2` were already proved. Only the fixed degree dictated by the
given base is used.

## Gap-quantifier check

For each spectral cut and every replication number in the unbounded tail
`m>=ceil((D-1)/2)`, an `m`-dependent neighbourhood and central cutoff
produce a half-slack global weight without changing its fibre-gap class.
The selected range positives are pairwise orthogonal positive contractions,
so their sum is a positive contraction. Hence

```text
m sigma([(b-epsilon)_+])<=||sigma||.
```

Letting `m` tend to infinity along the tail kills the cut; norm convergence
as `epsilon` tends to zero kills the original positive class. The
dependency graph uses claim IDs only. Independent hostile audits
green-lit the diffuse finite-degree induction, the matrix stable-range
carrier/Bott induction, the mixed-type minimum, the Michael index, and these
replication quantifiers.
