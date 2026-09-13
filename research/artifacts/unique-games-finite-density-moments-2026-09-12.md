# Finite density moments suffice after long-code noise

Date checked: 2026-09-12. This proves an analytic weakening of the existing
smooth-design route. It does not construct a hard instance or settle UGC.
There is no priority claim and no proof-assistant certification.

## 1. The useful change

The live artifact `unique-games-smooth-design-richness-2026-09-11.md` uses
pointwise domination of the pull-back law on balanced inputs. The following
argument replaces that domination by a single finite density moment, provided
we apply the lemma to the functions that actually occur in the reduction:
functions with a fixed positive amount of product noise already applied.

Write `U_N` for uniform measure on `[m]^N`. Write `T_rho` for independent
coordinate resampling noise: each coordinate is kept with probability `rho`
and otherwise replaced by an independent uniform symbol. Fourier/ANOVA degree
is the number of nonconstant coordinate factors. Then `T_rho` multiplies a
degree-`k` component by `rho^k`.

**Theorem 1 (finite-moment tail transfer).** For every integer `m >= 2` and
`0 < rho < 1` there is an integer `q = q(m,rho) >= 2` such that the following
holds in every dimension `N`. Let `nu` be any probability law on `[m]^N`,
let `D = dnu/dU_N`, and let `E` be any set. If

```
||1_E D||_(L^q(U_N)) <= C,
```

then for every real `F` and every integer `d >= 0`,

```
E_nu[1_E |(T_rho F)^(>d)|^2] <= C rho^(d+1) ||F||_2^2.       (1)
```

In particular `|F| <= 1` makes the last norm factor at most one. The choices
are `m,rho`, then `q`, then `C`, then `d`; `q` never depends on the dimension,
the moment bound, or the degree cutoff.

### Proof of the finite-alphabet hypercontractivity needed here

We supply the qualitative version rather than import a possibly mismatched
Boolean hypercontractivity constant. Fix `0 < s < 1`. On a single uniform
`m`-point space there is `p > 2` with `||T_s h||_p <= ||h||_2` for every real
`h`. Normalize `||h||_2=1` and write `h=a+v`, where `E v=0` and
`a^2+||v||_2^2=1`. Near either constant function `h=+1` or `h=-1`, Taylor
expansion gives, uniformly for `p` in a sufficiently small fixed interval
above two,

```
||a+s v||_p^2 = a^2 + (p-1)s^2 ||v||_2^2 + O_m(||v||_2^3).
```

The expansion is uniform because `||v||_infinity <= sqrt(m)||v||_2` and `a`
is bounded away from zero in these neighborhoods. Choose a preliminary
interval `2 <= p <= 2+delta` with `(1+delta)s^2<1`. A small enough fixed
neighborhood therefore satisfies the desired inequality throughout that
interval. On the compact complement of the two neighborhoods,

```
||T_s h||_2^2 = 1-(1-s^2)||v||_2^2 < 1
```

with a uniform strict margin. Continuity in `p`, uniformly on that compact
set, gives the inequality there for some `2<p<=2+delta`. This proves the
single-coordinate assertion.

It tensorizes without a dimension factor. For two coordinate blocks with
operators `A,B` individually contractive from `L^2` to `L^p`, apply `A` on
each fixed second coordinate, move the mixed `L^p_y(L^2_x)` norm inside via
Minkowski (valid since `p>=2`), then apply `B` on each fixed first coordinate:

```
||A_x B_y h||_(p_x,p_y)
 <= ||B_y h||_(p_y,2_x)
 <= ||B_y h||_(2_x,p_y)
 <= ||h||_(2_x,2_y).
```

Here the first index is the outer norm. Induction proves
`||T_s h||_p <= ||h||_2` on all product dimensions.

Now take `s=sqrt(rho)`, choose the resulting `p>2`, and choose an integer
`q>=2` such that `r=2q/(q-1)<=p`. Product probability norms are monotone, so
`T_s` is also `L^2 -> L^r` contractive. Noise commutes with degree projection.
Consequently

```
||(T_rho F)^(>d)||_r
 = ||T_s(T_s F^(>d))||_r
 <= ||T_s F^(>d)||_2
 <= s^(d+1)||F||_2.
```

Holder with conjugate exponents `q` and `q/(q-1)` proves (1). No claim of
such a bound for an arbitrary unsmoothed bounded function is needed.

## 2. The exact conditional route to UGC

Let `mu` be a law on perfect matchings of `[2n]`. To draw `nu_(mu,m)`, draw a
matching and assign independent uniform `[m]` colors to its pairs. Its
density relative to `U_(2n)` is

```
D_mu(z) = m^n sum_pi mu(pi) 1[z is constant on each pair of pi].
```

For fixed `K,m`, let `E_(K,m,n)` be the roughly balanced set used by the
existing smooth-design route. The new **open** hardness requirement is:

```
For every m>=2, K>=1 and integer q>=2 there exists C=C(m,K,q)>=1,
such that for every 0<eta<1/2, t>=1 and n0,
at some n>=max(n0,t), Gap-2-to-1_n[1-eta,eta] is NP-hard on
regular instances whose left pairing laws are t-wise uniform and satisfy
||1_E D_mu||_q <= C at every left vertex.
```

An instance only has to satisfy the chosen `m,K,q`, not all of them at once.
The constant `C` is independent of `eta,t,n`. We retain the existing regular
game convention; a different weighted encoding requires its own reduction
and is not silently assumed here.

**Why sufficient.** In the published Section 5 analysis the scalar functions
are `T_(1-epsilon) F_(u,r)` with `F_(u,r)` Boolean. In the existing transfer,
the only use of pointwise domination for the actual pairing law is the
expected restricted high-degree energy in Lemma 4.12 (ITCS Lemma 37). All
other pairing-law replacements use degree at most `8d+1` moments. These
facts are audited in the September 11 artifact. The new estimate (1)
supplies precisely that energy bound with `C rho^(d+1)` in place of the
old density constant times the unweighted tail energy. The imbalanced
part still has the same mass for every matching law.

Thus fix the desired output gap, fix its noise `rho` and test alphabet `m`,
then its analytic tolerances and balance parameter `K`. Choose `q(m,rho)`
from Theorem 1, then obtain `C(m,K,q)` from the open hardness hypothesis.
Choose `d` large enough that `C rho^(d+1)` is below the required energy
tolerance (and any unweighted tail requirements also hold). Set `t=8d+1`,
choose the list-rounding source error `eta` after `d`, and finally choose
an alphabet above the analytic lower bound. This is an acyclic parameter
choice. The existing completeness and rounding arguments now give UGC.

The original pointwise smooth-design hardness implies this finite-moment
hardness, since `1_E D<=B` gives `||1_E D||_q<=B` for every finite `q`.
Conversely the preceding route gives UGC, which already implies the
original smooth-design hardness by the repository's padding route. These
are conditional equivalences, not proofs of any hardness hypothesis. Nor
does pointwise domination follow for individual laws from a finite moment.

## 3. A combinatorial certificate for the new condition

For an integer `q>=2`, take independent `pi_1,...,pi_q~mu` and let `H` be
their union multigraph on `[2n]`. Let `N_E(H)` count assignments of one color
in `[m]` to each connected component of `H` for which the resulting vertex
coloring lies in `E`. Multiple edges do not change this count. Then

```
||1_E D_mu||_q^q = m^((q-2)n) E[N_E(H)].                       (2)
```

Indeed expand the `q`th power of the finite nonnegative sum defining `D_mu`
and exchange the sums. A coloring is constant on every sampled matching
exactly when it is constant on each union component. There are `N_E(H)`
such colorings and each has uniform mass `m^(-2n)`, while the density
expansion contributes `m^(qn)`. This proves (2), including repeated
matchings and arbitrary probability weights. For `E` the whole space it
reduces to `m^((q-2)n) E[m^(number of components of H)]`.

This reframes the missing outer condition as an average overlap count:
`E[N_E(H)] <= C^q m^(-(q-2)n)`. It does not show that existing hard
instances satisfy that condition. For `q>2` the required average is
exponentially small; rare tuples of matchings may dominate it.

## 4. The entropy barrier survives

Let `S` be the support of `nu_(mu,m)` and let `theta=nu_(mu,m)(E)>0`.
If `mu` has `M` distinct support matchings then `|S|<=M m^n` and
`U_(2n)(S)<=M m^(-n)`. Holder gives

```
theta = E_U[1_(E intersect S) D_mu]
      <= C U(E intersect S)^(1-1/q),
M >= (theta/C)^(q/(q-1)) m^n.                                (3)
```

For the balanced sets `theta` is bounded below at the chosen sufficiently
large `K`. Thus finite-moment control still rules out subexponential
pairing support. This weakening concerns the form of the outer certificate,
not removal of the established entropy obstruction.

## 5. Verification, sources, and unresolved work

The proof above is analytic and finite-sum algebra. The companion exact
replay `verify-ugc-finite-density-moments.py` checks (2) with rational
nonuniform weights, repeated matchings, several alphabets and both full
and permutation-invariant restricted coloring sets. Its bounded output
is a regression check, not a proof of the all-dimensional statements.
Execution is through the MSI wrapper only; the integration report records
the actual run and result.

Repository search on 2026-09-12 covered the smooth-design, pairing,
unique-games, and UGC claims/artifacts and the September 11 quantifier
note. Relevant primary sources checked on that date:

* Braverman, Khot, Minzer, [On Rich 2-to-1 Games, full version](https://eccc.weizmann.ac.il/report/2019/141/)
  and [ITCS 2021 version](https://drops.dagstuhl.de/storage/00lipics/lipics-vol185-itcs2021/LIPIcs.ITCS.2021.27/LIPIcs.ITCS.2021.27.pdf),
  especially the high-degree step and the noise in Section 5.2.
* The [current OpenTCS problem page](https://www.opentcs.cc/problems/unique-games-conjecture/)
  still presents the UGC question as unresolved. Khot's
  [survey](https://cs.nyu.edu/~khot/papers/UGCSurvey.pdf) supplies primary
  background; it is not used as evidence of a recent status change.

Searches for Rich 2-to-1 density moments, Lp variants, and released code
did not identify an exact prior statement of this adaptation. This is
not an exhaustive novelty proof; no novelty claim is made. The proof uses
standard Holder, finite-space hypercontractivity and tensorization.

The remaining high-impact task is still an outer PCP construction giving
near-perfect versus near-zero hardness with exact pairing moments and
the overlap bound (2), with `C` independent of the source error and design
strength. Neither the moment identity nor Theorem 1 constructs it.
