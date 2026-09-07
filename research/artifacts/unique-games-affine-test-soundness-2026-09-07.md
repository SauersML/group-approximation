# Low-value affine games defeat the folded long-code noise test

Date: 2026-09-07. Status: complete mathematical proof of the obstruction
stated below, with supplementary exact finite checks. **This is not a proof
or a disproof of the Unique Games Conjecture.** It does not contradict the
Rich 2-to-1 theorem, whose full-richness hypothesis is essential here.
No proof-assistant verification or claim of priority is made.

## 1. The precise result

For every `N=4^r`, `r>=1`, we construct a finite, uniformly weighted,
biregular 2-to-1 game `G_N`. Each left vertex sees the affine pairings
`{x,x+b}` for all nonzero `b` exactly once. Its value satisfies

```text
val(G_N) <= (1+sqrt(1+12N))/(2N) <= 2/sqrt(N).                  (1)
```

For every output alphabet `Z_m`, `m>=2`, and every fixed `0<rho<1`,
apply the three-noise folded long-code test defined in Section 4. There
is an explicit folded labeling of its output game `R_(rho,m)(G_N)` with

```text
val(R_(rho,m)(G_N))
  >= 1/m + (1-1/m)rho^3 - 2(N-1)exp(-N rho^4/32).              (2)
```

Thus, for fixed `rho,m`, source value tends to zero while output value
stays bounded away from zero. More strongly, for any `eta,epsilon>0`
and `m>=2`, some rational `rho<1` and some `N=4^r` give

```text
val(G_N) <= eta,          val(R_(rho,m)(G_N)) >= 1-epsilon.     (3)
```

For a concrete finite instance, `N=16384` and `rho=99/100` give
source value at most `1/64` and output value greater than `97/100`,
for every `m>=2`. Section 7 verifies these constants without floating point.

The obstruction concerns a uniform soundness claim for this particular
test on **all affine-rich inputs**. It does not rule out another test,
an enrichment step, or a restricted family with extra structure. In
particular, constructing low-value instances does not establish NP-hardness.

## 2. An explicit source game and its value bound

Let `F` be the field of size `N=2^(2r)`. Only characteristic two, the field
axioms, and the bijectivity of squaring are used. Such a field can be
constructed as the roots of `t^N-t` in an algebraic closure of `F_2`:
Frobenius shows closure under addition and multiplication, nonzero roots
are closed under inversion, and derivative `-1` gives exactly `N` distinct
roots. Fix a binary basis and the induced ordering of `F`.

The left vertices and their label alphabet are both `F`. The right vertices
are `F*`. At vertex `b`, the right alphabet is `F/<b>`, where
`<b>={0,b}`. This is one alphabet of size `N/2`: to obtain a common
numbered alphabet, order the cosets by their least binary representatives,
so the zero coset always has index zero. The graph is `K_(N,N-1)` and
the projection on edge `(u,b)` is

```text
pi_(u,b)(a) = [a+u b^2]_b.                                   (4)
```

Its fibers are exactly the pairs `{x,x+b}`. Each projection is 2-to-1;
each left vertex has the uniform distribution on the `N-1` affine
directions. This is the `F_lin` pairing condition. It is not the uniform
distribution on all perfect pairings when `N>=16`.

Consider any labeling `a_u` on the left and any coset labeling on the
right. If two distinct left vertices `u,v` both satisfy their edges to
the same `b`, their projected cosets coincide, and hence

```text
a_u+a_v+(u+v)b^2 is in {0,b}.                                 (5)
```

Write `D=u+v != 0` and `C=a_u+a_v`. Equation (5) requires either
`D b^2=C` or `D b^2+b=C`. The first equation has at most one root:
squaring is injective since `x^2=y^2` implies `(x+y)^2=0` and `x=y`.
The second has at most two roots, by the degree bound for roots of a
nonzero polynomial over a field. That bound follows by repeatedly
factoring `t-b` at a root. Therefore two distinct left vertices have
at most three common satisfied right neighbors. This conclusion holds
for every choice of their labels, not just the labeling used later.

Let `d_b` be the number of satisfied edges incident to `b`, and
`E=sum_b d_b`. Counting pairs of satisfied edges at a right vertex gives

```text
sum_b binom(d_b,2) <= 3 binom(N,2).
```

Since `sum_b d_b^2 >= E^2/(N-1)` by Cauchy--Schwarz,

```text
E^2/(N-1)-E <= 3N(N-1).
```

The satisfied fraction `s=E/[N(N-1)]` consequently obeys
`N s^2 <= s+3`. Solving this quadratic gives the first bound in (1).
Since `s<=1`, the same inequality gives `N s^2<=4`, proving the
second bound. Maximizing over labelings proves (1).

If equal degrees on the two sides are required, replace every left vertex
by `N-1` clones and every right vertex by `N` clones, with all pairs of
clones connected along each original edge, carrying its projection. Both
sides now have `N(N-1)` vertices and degree `N(N-1)`. The affine pairing
distribution is unchanged. Value is unchanged as well: independently choose
one clone per original vertex; the expected satisfied fraction of the
resulting original labeling is the cloned labeling's satisfied fraction.
The reverse inequality follows by copying an original optimal labeling.
The output lower bound below also lifts by copying each folded function.

## 3. A decoder for an arbitrary cyclic output alphabet

Let `A=Z_m`, with all additions to output symbols taken modulo `m`.
The noise kernel is

```text
K_rho(s,t) = rho 1_(s=t) + (1-rho)/m.
```

Thus a coordinate is retained with probability `rho`, and otherwise
replaced by an independent uniform symbol. Noise on different coordinates
is independent. For `Y in A^F` and nonzero `c`, define

```text
S_c(Y) = (1/N) sum_(x in F) 1_(Y_x=Y_(x+c)).
bhat(Y) = the least c maximizing S_c(Y).                        (6)
```

Fix a planted direction `b`. Start with a uniformly random vector that
is constant on each `b`-pair, independently across pairs, and apply
ambient `K_rho` noise to obtain `Y`. Put
`lambda=(1-1/m)rho^2`. Two members of a planted pair agree with
probability `1/m+lambda`; coordinates from different pairs agree with
probability `1/m`.

The true score `S_b` is the average of `N/2` independent indicators,
with mean `1/m+lambda`. For `c!=0,b`, decompose `F` into the
`N/4` cosets of the two-dimensional binary space `<b,c>`. On a coset
represented by `x`, use the block variable

```text
W_x = (1_(Y_x=Y_(x+c)) + 1_(Y_(x+b)=Y_(x+b+c)))/2.
```

It lies in `[0,1]`, has mean `1/m`, and is independent of blocks on
other cosets. Counting each undirected `c`-edge twice shows that `S_c`
is the average of these `N/4` block variables.

For independent variables in `[0,1]`, the probability their average
exceeds its mean by `t` is at most `exp(-2kt^2)`, with `k` variables;
the same holds for the lower tail. Here is a derivation. The second
derivative of the logarithmic moment generating function is the variance
under exponential tilt, at most `1/4`: for any variable `V in [0,1]`,
`E[V^2]<=E[V]` gives `Var(V)<=E[V](1-E[V])<=1/4`.
Integrating twice gives `E exp(z(V-EV))<=exp(z^2/8)`. Independence,
Markov's inequality, and optimization at `z=4t` give the asserted tail.

At the separating threshold `1/m+lambda/2`, it follows that

```text
Pr[S_b <= threshold] <= exp(-N lambda^2/4),
Pr[S_c >= threshold] <= exp(-N lambda^2/8)       (c!=0,b).
```

When neither event occurs for any wrong direction, the maximizer is
uniquely `b`. Ties are covered by the weak inequalities in the bad
events. A union bound, without assuming independence between scores, gives

```text
Pr[bhat(Y)!=b]
 <= (N-1)exp(-N lambda^2/8)
 <= (N-1)exp(-N rho^4/32) =: e_N,                              (7)
```

because `1-1/m>=1/2`. This holds separately for every planted direction.
It extends the Boolean noisy-direction calculation already recorded in
[the earlier counterexample](unique-games-noisy-direction-counterexample-2026-09-07.md).

## 4. The exact transformation being tested

We specify the test to remove any ambiguity about where noise occurs.
Write `M=N/2`. It is the folded long-code test of Braverman, Khot and
Minzer, Section 5, with correlation parameter `rho=1-epsilon`:

1. Choose right vertex `b` uniformly and left neighbors `u,v`
   independently and uniformly.
2. Choose `A` uniformly in `(Z_m)^M`; obtain `B` by coordinatewise
   `K_rho` noise on `A`.
3. Pull back to `P_x=A_(pi_(u,b)(x))` and
   `Q_x=B_(pi_(v,b)(x))` for all `x in F`.
4. Apply independent coordinatewise `K_rho` noise to `P,Q`, obtaining
   `X,Y`. Accept if `F_u(X)=F_v(Y)`.

Source: [On Rich 2-to-1 Games, ITCS 2021, Section 5, pp. 27:16--27:19](https://drops.dagstuhl.de/storage/00lipics/lipics-vol185-itcs2021/LIPIcs.ITCS.2021.27/LIPIcs.ITCS.2021.27.pdf).
Their proved soundness statement assumes full richness. We apply this
explicit transformation to the different source family (4).

To spell out the output game, store a variable for `(u,xbar)` with
`xbar=x-x_0 1`, so `xbar_0=0`. A label `ell_(u,xbar) in Z_m` extends
uniquely to the folded function

```text
F_u(x) = ell_(u,xbar)+x_0.
```

Each sampled equality is the permutation constraint

```text
ell_(u,xbar)-ell_(v,ybar) = y_0-x_0 (mod m).                   (8)
```

Use the sampling probabilities as edge weights. This is a finite weighted
unique game. Rational `rho` gives rational weights, so parallel edges
after clearing denominators give the same value. If a bipartite convention
is desired, put copies of all variables on two sides and use the copied
labeling below; its satisfied fraction is the same. No small-alphabet
algorithm or polynomial running time as `N` grows is asserted.

## 5. An explicit folded labeling with high acceptance

For every left vertex `u`, define on the entire ambient cube

```text
F_u(Y) = Y_(u bhat(Y)^2).                                     (9)
```

Adding a constant symbol to every coordinate does not change equality
scores or their tie-breaking. Thus
`F_u(Y+t 1)=F_u(Y)+t`. This proves that (9) is a valid folded labeling
of (8), including inputs on which the decoder fails.

On edge `(u,b)`, the coordinate `q_(u,b)=u b^2` maps to zero:
`pi_(u,b)(u b^2)=[0]_b`. The pullback of a uniform virtual vector in
Section 4 is uniform on pair-constant vectors in direction `b`, since
(4) bijects those pairs with the right coordinates. Accordingly (7)
applies to each query. The marginal law of `B` is also uniform, since
`K_rho` preserves the uniform measure.

Let ideal outputs be `I=X_(u b^2)` and `J=Y_(v b^2)`. Each is exactly
the output in (9) when its query decodes `b` correctly. A union bound
therefore gives

```text
Pr[F_u(X)=F_v(Y)] >= Pr[I=J] - 2e_N.                          (10)
```

This comparison is unconditional. It does not assume that the decoder
success event is independent of the selected symbols.

Both ideal outputs read right coordinate zero. There are three noise
steps in their joint law: from `A_0` to `I`, from `A_0` to `B_0`,
and from `B_0` to `J`. Algebraically, if `U` is the matrix with all
entries `1/m`, then `K_rho=rho I+(1-rho)U`, `U^2=U`, and
`K_s K_t=K_(st)`. The kernel is symmetric and `A_0` is uniform, so
the conditional law of `J` given `I` is `K_(rho^3)`. Consequently

```text
Pr[I=J] = 1/m+(1-1/m)rho^3.                                  (11)
```

Equations (7), (10), and (11) prove (2). Dependence between the two
decoding errors, repeated choices `u=v`, and coincident queries do not
change this argument; the two ambient noise samples are independent.

## 6. Quantifiers and the limit

For fixed `rho>0`, `e_N -> 0`: writing `c=rho^4/32`, the power
series gives `exp(cN)>=(cN)^2/2`, hence
`e_N <= 2/(c^2 N) -> 0`. This elementary bound suffices for the limit,
although (7) is much sharper.

For (3), it suffices to take `0<epsilon<1` and `eta>0`. Choose a
rational `rho` with `1-epsilon/6<rho<1`. Then
`rho^3>1-epsilon/2`, by `(1-t)^3>=1-3t` on `[0,1]`. Take a large
enough power of four that `2/sqrt(N)<=eta` and `e_N<=epsilon/4`.
Using (1) and (2), and `1/m+(1-1/m)rho^3>=rho^3`, proves (3).
The statement for larger epsilon follows from any smaller positive one.

Even if `m` is selected after `rho`, bound (7) is uniform in `m>=2`.
Thus increasing the output alphabet cannot restore a soundness bound
tending to zero with the source value for this test and input family.

## 7. Exact replay and a finite gap

At `N=16384`, `rho=99/100`, rational arithmetic gives
`N rho^4/32>32`. Since `e>2`,

```text
e_N < N/2^32 = 1/262144,
2/sqrt(N) = 1/64,
rho^3-2/262144 > 97/100.
```

This proves the concrete finite gap in Section 1 without enumerating the
exponentially large output game.

[The exact checker](../../scripts/check_unique_games_affine_soundness.py)
and [its deterministic report](unique-games-affine-test-replay-2026-09-07.json)
provide supplementary checks. They verify finite fields of sizes
`4,16,64,256`, exhaust the common-neighbor polynomial count, check every
edge projection for `N=4,16`, and exhaust the complete source labeling
optimization at `N=4`. They also enumerate the entire three-noise test at
`N=4`, `m=2,3`, with rational probabilities, check folding and the
decoder-error coupling, independently check the ideal three-kernel law,
and verify the concrete large-instance bounds above. The `N=4` source
is fully satisfiable; it tests normalization, not the asymptotic gap.
None of these finite checks replaces the all-dimension proof.

Run from the repository root:

```sh
python3 scripts/check_unique_games_affine_soundness.py --check
```

## 8. Research status and provenance

This construction applies the earlier noisy-direction idea to a concrete
game. The additional ingredients are the explicit shift `u b^2`, a
polynomial root count, pair counting, and an equality-score decoder for
arbitrary cyclic output alphabets. The proof identifies the exact
published test and gives an explicit valid output labeling, which the
earlier analytic counterexample did not do.

On 2026-09-07, repository searches and primary-paper searches were made
for affine-pairing soundness, noisy long-code counterexamples, and
finite-field 2-to-1 constructions. The BKM paper's definitions and Section 5
were checked directly. These limited searches do not certify novelty;
no priority claim or exhaustive review of unpublished work or software is
made. The current UGC frontier was checked against
[Dawar and Molnar, arXiv:2504.03523v2](https://arxiv.org/html/2504.03523v2),
revised 2026-03-01, which treats UGC as open.

The established statement is (1)--(2), not NP-hardness and not an
efficient algorithm for arbitrary unique games. UGC and the Rich 2-to-1
Games Conjecture remain open in Cairn. This result closes the proposed
direct reuse of this test under only affine richness; it supplies no
replacement proof of either conjecture.
