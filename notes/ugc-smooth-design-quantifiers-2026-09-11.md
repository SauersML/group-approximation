# Smooth pairing designs: the quantifiers and a finite-parameter construction

Date checked: 2026-09-11. This is a proof and scope audit for the live Cairn
claim `smooth-design-rich-2to1-hardness`, not a proof of that hardness claim
or of Unique Games. No priority claim is made. The construction completes a
weighted version of the sketch already in
`research/artifacts/unique-games-smooth-design-richness-2026-09-11.md`.

## 1. Two different requirements

Write `P_n` for the perfect matchings of `[2n]`. For a probability law `mu`
on `P_n`, let `nu_(mu,m)` be the distribution obtained by giving the pairs
independent uniform colors from `[m]`. Thus

```
nu_(mu,m)(z) = m^(-n) sum_{pi: z is constant on pi} mu(pi).
```

The current hardness claim asks for one distribution at each vertex that is
smooth for **every** test alphabet `m` and balance parameter `K`, with
constants `C(K,m)` independent of `n`. Its construction sketch instead fixes
`K,m,t` before choosing the distribution. These are different assertions.

**Atom bound.** If the balanced set contains a coloring constant on a given
matching `pi`, and `nu_(mu,m)(z) <= C m^(-2n)` throughout that set, then

```
mu(pi) <= C m^(-n).
```

Indeed, choose such a coloring and retain just the summand indexed by `pi`.
The existence of a balanced coloring depends only on the pair-color counts,
not on the matching. For each fixed `m,K`, sufficiently large `n` admits
pair-color counts as equal as possible, hence a roughly balanced coloring
in the sense used by BKM.

Consequently, a sequence satisfying the all-`m` requirement obeys

```
liminf_{n -> infinity} (-log max_pi mu_n(pi))/n = +infinity.
```

For every fixed `m`, the atom bound gives a lower limit at least `log m`;
then let this fixed integer grow. In particular,
`log |supp(mu_n)| / n -> infinity`. A bound `|supp(mu_n)| <= exp(c n)` with
one fixed finite `c` cannot meet the all-`m` requirement. This does not refute
the hardness conjecture: uniform distributions on all matchings have much
larger support. It limits what the fixed-parameter sketch establishes.

## 2. A complete weighted construction for fixed parameters

The following elementary statement avoids needing an unweighted permutation
design theorem. Assume `1 <= t <= n`, fix `m >= 2`, and let `E` be any
coordinate-permutation-invariant set of colorings. Suppose the uniform law
`U` on all matchings satisfies

```
nu_(U,m)(z) <= B m^(-2n)   for z in E,       B >= 1.
```

There is a rationally weighted, exactly `t`-wise uniform matching law `mu`
such that

```
nu_(mu,m)(z) <= 2B m^(-2n)   for z in E,
|supp(mu)| <= M ((2n)_(2t)^2 + 1),
M = ceil(3 m^n (2n log m + log 2)/B).
```

Here `(a)_b` denotes the falling factorial. Thus for fixed `m,t,B` the
support bound is `O(m^n n^(4t+1))`. We count distinct matchings, not the
possibly larger number of parallel edges after clearing denominators.

**Sampling.** Choose `M` independent uniform matchings, retaining repetitions,
and let `Q` be their empirical probability law. For each `z in E`, its number
`X_z` of compatible sampled matchings is binomial, with mean at most
`a = M B m^(-n)`. If `B m^(-n) >= 1/2`, the proposed upper bound
`X_z <= 2a` is automatic. Otherwise a binomial variable with success
probability `B m^(-n)` stochastically dominates `X_z`, and the usual
multiplicative Chernoff bound gives

```
Pr[X_z > 2a] <= exp(-a/3).
```

There are at most `m^(2n)` colorings. The stated `M` therefore makes the
probability of any violation at most `1/2`. Fix a successful multiset.

**Exact moments.** Put `N=2n` and `r=2t`. To each permutation `sigma in S_N`
associate the vector of indicators `1[sigma(a)=b]`, where `a,b` run through
ordered injective `r`-tuples. This vector has `D=(N)_r^2` coordinates.
The uniform average of these vectors is a convex combination of at most
`D+1` of them: repeatedly remove an affine dependence from any larger
support, keeping all coefficients nonnegative and their sum one. Since
the vectors and desired average are rational, take a minimal affinely
independent support; its uniquely determined coefficients are rational.
This gives an exactly `r`-wise uniform rational law `eta` on permutations.
Uniformity for shorter tuples follows by summing over extensions, and the
inverse permutations have the same `r`-wise uniformity.

Sample `sigma` from `eta` and `pi` from `Q` independently; set
`mu = law(sigma(pi))`. For any prescribed partial matching with `k<=t`
pairs, the inverse images of its `2k` endpoints under `sigma` are uniform
ordered distinct points. In a fixed perfect matching their probability
of being paired as prescribed is

```
1 / ((N-1)(N-3)...(N-2k+1)).
```

This is independent of `pi`, proving exact `t`-wise uniformity. Finally,
coordinate permutations preserve `E`, and
`nu_(sigma(Q),m)(z)=nu_(Q,m)(z composed with sigma)`. Averaging the already
valid smoothness bounds proves the asserted inequality for `mu`. The
support size is at most the product of the two support sizes. This proves
the construction without a computation or an efficiency assertion.

For BKM's roughly balanced sets, their density lemma supplies the required
`B=B(K,m)`. The weighted construction above is therefore nonvacuous.

## 3. A weaker hardness formulation sufficient for the existing route

The order needed by the existing smooth-design transfer is

```
for every fixed m,K there exists C=C(m,K), such that
for every source error eta>0 and design strength t,
for every sufficiently large n there are NP-hard instances
whose left pairing distributions are t-wise uniform and
(K,m,C)-smooth.
```

Instances may depend on the fixed `m,K`. One need not require each instance
to be smooth for all test alphabets simultaneously. The crucial uniformity
is that `C` is chosen **before** `eta,t,n`: the transfer uses `C` to select
the high-degree cutoff and hence the required design strength and source
soundness. Allowing `C` to depend on `t` would reintroduce a circular choice.

Conditionally on the existing analytic transfer, the weaker formulation
still implies UGC. Fix the desired output error; BKM fixes `m,K`; select
`C`, then the high-degree tolerance, the degree cutoff, `t`, and the source
error, in that order. Apply the asserted hardness at sufficiently large
`n`, then the transfer. Rational weights are just distributions throughout
the moment and density estimates; clearing denominators gives parallel
edges, with the reduction required to control the resulting encoding size.

Section 2 proves only that suitable weighted pairing distributions exist
for fixed parameters. It does **not** put those distributions on a hard
2-to-1 instance. That outer hardness construction is still missing. Nor
does the argument prove that the weaker and existing hardness formulations
are inequivalent, or that a sparse family is easier to realize in a PCP.

## 4. Sources and novelty boundary

Read on 2026-09-11:

* Braverman, Khot, Minzer, [On Rich 2-to-1 Games, ECCC TR19-141](https://eccc.weizmann.ac.il/report/2019/141/),
  particularly the full-version density comparison and Section 5. This is
  the source for the analytic route and balance convention.
* Kuperberg, Lovett, Peled, [Probabilistic existence of regular combinatorial
  structures](https://arxiv.org/abs/1302.4295). Small exact permutation
  designs, including the weighted convex-hull relaxation, are prior art;
  no novelty is claimed for the symmetrization mechanism above.
* The same-day Cairn artifact cited at the start already sketches sampling
  followed by permutation-design symmetrization. This note supplies explicit
  weights, bounds and quantifiers, and corrects the scope of that sketch.

The elementary derivations in this note establish the stated audit facts.
The repository's UGC and outer-hardness goals remain open.
