---
rg: 2
id: proper-torus-reynolds-is-edge-refinement
kind: claim
title: A proper-subtorus Reynolds complex has an explicit divergent square-free Green family
distinct_from:
  full-torus-reynolds-is-multipartite-curl: that identifies the full-torus column with an ordinary clique-complex curl; this compares a proper subtorus with the full-torus edge and triangle sets.
  multipartite-triangle-curl-has-uniform-infinity-green-bound: that constructs a uniformly bounded Green operator for the base clique complex; this proves why that operator does not lift to the extra-label sector.
  right-u-reynolds-has-torus-hecke-blocks: that decomposes the proper-subtorus domain into explicit torus-character blocks; this gives the global labeled-edge geometry and the obstruction to a covering-space contraction.
  fourth-power-mersenne-reynolds-levels-have-diagonal-crt-coupling: that produces an explicit unbounded-index composite family and isolates its right-unipotent blocks; this gives the exact edge-refinement model shared by all proper-subtorus levels.
  flat-gain-multipartite-covers-have-uniform-green-bound: that proves every genuine flat gain cover is gauge-trivial and retains the base Green bound; this proves the Reynolds refinement is not such a cover.
  signed-orbit-averaging-does-not-divide-green-cost: that proves averaging a generic electrical routing over the growing signed torus orbit has norm one rather than inverse-orbit-size cost; this identifies the labeled geometry.
---

**ESTABLISHED; EXPLICIT LOGARITHMIC DIVERGENCE.**  Let `Q` be a finite congruence
quotient with split projective torus `T`, let `H<T` be normalized by the
Weyl involution `w`, and put `i=[T:H]`.  Use the sign character of
`<H,w>` (respectively `<T,w>`) which is trivial on the torus and sends `w`
to `-1`.  The scalar input modules are

```text
E_H=Ind_(<H,w>)^Q sign,
E_T=Ind_(<T,w>)^Q sign.                                (PSE1)
```

The quotient of left cosets gives an `i`-to-one map of signed oriented
edge coordinates

```text
pi:E(H) -> E(T).                                       (PSE2)
```

Thus `E(H)` is the full-torus oriented-edge set with one extra label in
`T/H` (with the Weyl involution reversing the edge and inverting the
label).  Pullback along `(PSE2)` is an isometric inclusion

```text
pi^*:E_T -> E_H                                        (PSE3)
```

for the scalar infinity norm.

The two triangle sets do **not** acquire this label.  Put

```text
A=XS^2,             B=XRS,             A^3=B^3=1.
```

After removing the harmless threefold row repetition, the triangle rows
for both columns are the same two sets

```text
F_A=<A>\Q,             F_B=<B>\Q,                      (PSE4)
```

independent of `H` and `T`.  The three `H`-edge labels in a row are the
specific cosets represented by the three translates in `(DSS3)`.  Their
images under `(PSE2)` are exactly the three full-torus edges of the same
row.  Consequently

```text
C_H pi^* = C_T.                                        (PSE5)
```

Equation `(PSE5)` proves that the bounded full-torus Green theorem controls
the fiber-constant subspace of the proper-subtorus column.  It also proves
that the remaining issue is precisely the fiber-mean-zero edge sector.

Crucially, `(PSE2)` is not the one-skeleton of an `i`-sheeted cover of the
two-dimensional complex when `i>1`.  Such a cover would have `i|F_A|`
and `i|F_B|` lifted triangle rows.  The actual row sets `(PSE4)` have only
`|F_A|` and `|F_B|` rows: each base triangle selects one correlated triple
of edge labels rather than all `i` deck translates.  Hence no simplicial
lift of the bounded contraction from
`multipartite-triangle-curl-has-uniform-infinity-green-bound` is defined
on the extra-label sector.

For the explicit composite family

```text
M_n=4^n-1,       Q_n=SL_2(Z/M_n Z)/{+-I},
H_n=<h(2)>,      T_n=the split projective torus,
```

`fourth-power-mersenne-reynolds-levels-have-diagonal-crt-coupling` gives

```text
i_n=[T_n:H_n]=phi(M_n)/(4n) -> infinity.               (PSE6)
```

Thus `(PSE2)--(PSE5)` are an explicit growing labeled-edge family with no
corresponding growth in triangle lifts.  This is a rigorous obstruction to
the proposed **covering-space** proof of a uniform Green bound.  By itself
the edge count does not decide whether the selected label triples couple
the fiber-mean-zero sector efficiently.  The finite concrete alternative
is to prove a uniform bound on that sector or construct `f_n` with

```text
||f_n||_infinity /
max(||C_(1,H_n)f_n||_infinity,||C_(2,H_n)f_n||_infinity)
 -> infinity.                                          (PSE7)
```

The base multipartite contraction settles none of `(PSE7)` because its
entire image lies in the fiber-constant summand `(PSE3)`.  The square-free
construction below resolves `(PSE7)` in the divergent direction.

`signed-orbit-averaging-does-not-divide-green-cost` also rules out a
different shortcut based only on the large order of `H`.  The restricted
Moore--Penrose inverse is the signed Reynolds compression of the full
`A/B` Green operator, but that Reynolds projection has infinity norm one,
not `1/|H|`.  A routing proof needs an additional arithmetic congestion
estimate for the translated flows.

Nor can divergence be attributed merely to a large deck group or to
unitary character phases.  `flat-gain-multipartite-covers-have-uniform-green-bound`
proves that every genuine flat gain cover of the multipartite clique
complex is gauge-trivial and has exactly the base Green norm, independently
of the deck degree.  The arithmetic sector in `(PSE7)` is load-bearing
precisely because `(PSE4)` omits the other deck translates of each
triangle; it is an incomplete, curved label system rather than a flat
local system.

The growing orbit itself supplies no compensating infinity-norm factor.
`signed-orbit-averaging-does-not-divide-green-cost` proves that
the signed Reynolds projection onto `<H,w>`-equivariant functions has
exact infinity and cb norm one, and that disjoint translated Green rows
retain their full `l_1` mass after normalized averaging.  Hence a putative
generic `O(log|Q|)` routing cost is not reduced formally by `|H|`; a
positive proof would need arithmetic cancellation or a genuinely new
constrained routing.  The relative-girth and super-approximation argument
below proves that such cancellation does not occur uniformly.

## Exact relative-girth theorem for the selected complex

The selected incidence complex nevertheless has a strong real-space
feature which was not visible in the edge-count comparison.  Work first in
`PSL_2(Z[1/2])` and use

```text
x=w,       s=u(1/2),       r=h(2),
A=xs^2,    B=xrs.
```

The two order-three groups appearing in the **normal operator** are

```text
K_1=s^2<A>s^(-2)=<a>,       a=u(1)w,
K_2=s<B>s^(-1)=<b>,         b=u(1/2)wh(2).             (PSE8)
```

With determinant-one representatives,

```text
a=[[1,-1],[1,0]],          b=[[1,-1/2],[2,0]].         (PSE9)
```

Put `Lambda=<a,b>` and `N=<h(2),w>`.  Then

```text
Lambda = <a>*<b> ~= C_3*C_3,
Lambda cap N={1}.                                      (PSE10)
```

Here is a proof.  In the Bruhat--Tits tree of `PGL_2(Q_2)`, `a` fixes the
standard vertex and its reduction modulo `2` cyclically permutes the three
incident edges.  If `d=diag(1,2)`, then

```text
b=dad^(-1),
```

so `b` has the same action at the adjacent vertex `d v_0`.  The Bass--Serre
tree of `<a>*<b>` maps locally bijectively to the 3-regular Bruhat--Tits
tree, hence isomorphically.  This proves the first assertion in `(PSE10)`.

For the intersection assertion, set

```text
c=ab^(-1)=[[2,-1/2],[0,1/2]],       c(z)=4z-1.         (PSE11)
```

The element `c` is primitive hyperbolic of syllable length two.  The
stabilizer in the free product `Lambda` of its boundary fixed point
`infinity` is therefore exactly `<c>`.  Since `a^2(infinity)=0`, every
element of `Lambda` carrying `infinity` to `0` has the form `a^2c^k`.
But

```text
c^k(0)=(1-4^k)/3,
a^2(z)=1/(1-z),                                        (PSE12)
```

so `a^2c^k(0)=infinity` would require `4^k=-2`, which is
impossible.  Likewise, `c^k(0)=0` only for `k=0`.  Thus the only element of
`Lambda` preserving the unordered pair `{0,infinity}` is the identity.
The stabilizer of this pair inside `PSL_2(Z[1/2])` is exactly the split-
torus normalizer `<h(2),w>` (the units of `Z[1/2]` are `+-2^k`).  This proves
the second assertion of `(PSE10)`.

This intersection statement has a quantitative congruence consequence.
Let `M` be odd and let a nonempty reduced word `W` in the syllables
`a^(+-1),b^(+-1)` have length `L`.  Replace each syllable matrix by twice
that matrix.  The resulting integer matrix represents the same projective
transformation and has every entry bounded in absolute value by `6^L`.
If the reduction of `W` modulo `M` lies in the image `N_M`, then this
integer matrix is projectively diagonal or antidiagonal modulo `M`.
Accordingly, either both off-diagonal entries or both diagonal entries are
divisible by `M`.  If `6^L<M`, those entries vanish over the integers, so
`W` lies in the split-torus normalizer already over `Q`; because its entries
belong to `Z[1/2]`, it lies in `N`.  Equation `(PSE10)` then forces `W=1`,
contradicting reduced normal form.  Therefore

```text
W mod M in N_M, W nonempty   =>   L>=log_6 M.          (PSE13)
```

For `M_n=4^n-1`, this is a relative injectivity radius linear in `n`.
Equivalently, in the bipartite `K_1/K_2` incidence graph, balls of radius
less than `(1/2)log_6 M_n` around distinct edges in one `N_n`-orbit are
pairwise disjoint.  Thus the arithmetic selected complex really does
contain linearly deep disjoint tree neighborhoods; the missing-triangle
geometry is not merely a counting artifact.

Relative girth alone does not control the globally supported electrical
tails.  On a square-free family, however, super-approximation supplies the
missing decay and proves that `(PSE7)` **diverges**.

For every `k>=2`, choose a primitive prime divisor

```text
ell_k | 4^k-1,
```

and put

```text
M_n=product_(k=2)^n ell_k,       L_n=lcm(2,...,n).      (PSE14)
```

Zsigmondy's theorem supplies `ell_k`; the primes are distinct and
`ord_(ell_k)(4)=k`.  Hence `M_n` is odd and square free.  Moreover

```text
log M_n >= sum_(k=2)^n log(k+1)=n log n-O(n),
|<h(2)> in Q_(M_n)| <=2L_n=exp(O(n)).                  (PSE15)
```

The second bound holds because `4^(L_n)=1` at every prime factor, so
`h(2)^(2L_n)=1`; the standard Chebyshev estimate gives `log L_n=O(n)`.
The split-torus index tends to infinity, since

```text
|T_(M_n)|/|<h(2)>|
 >= product_(k=2)^n k /(4L_n) -> infinity.             (PSE16)
```

Let `Y_n` be the bipartite incidence graph with edge set `Q_(M_n)` and
vertex sets

```text
K_1\Q_(M_n)       and       K_2\Q_(M_n).
```

It is 3-regular on every connected component.  Multiplying one vertex
class by `-1` conjugates the two signless Reynolds rows to the ordinary
oriented incidence operator; this changes neither the normal operator nor
any infinity norm.  Write `P_(cut,n)` for its electrical cut projection.

The group `Lambda` is Zariski dense in `PSL_2`: by `(PSE10)` it is a
non-elementary free product, whereas every proper algebraic subgroup of
`PSL_2` is finite or virtually solvable.  Super-approximation for finitely
generated subgroups of `GL_2(Z[1/2])` with perfect connected Zariski closure,
applied to the square-free moduli `(PSE14)`, gives a uniform Cayley spectral
gap.  This is exactly the square-free case of Salehi Golsefidy,
*Super-approximation II*, JEMS 21 (2019), Theorem 1: it covers every
square-free modulus coprime to the localization integer `2`, not merely
primes or moduli whose prime factors tend to infinity.  Equivalently, one
may omit any finite initial set of primitive primes without changing
`(PSE15)--(PSE16)`.

Here is the transfer from that theorem to `Y_n`.  Every component is the
incidence graph with edge set `Gamma_n=pi_(M_n)(Lambda)` and vertex sets

```text
<a>\Gamma_n       and       <b>\Gamma_n.
```

The edge-to-edge walk which chooses one of the two endpoints and then one
of its three incident edges is

```text
(1/6)(2I+L_a+L_(a^2)+L_b+L_(b^2)),
```

an affine rescaling of the Cayley walk for the fixed symmetric generating
set `{a,a^2,b,b^2}`.  Thus Cayley expansion gives a uniform gap for this
walk, and the standard incidence singular-value correspondence gives a
constant `rho<1` such that the lazy vertex walk on every component of
`Y_n` has nonconstant spectrum in `[0,rho]`.

This spectral gap gives the required off-diagonal electrical decay.  If
`partial` is the oriented vertex-edge incidence and `P` is lazy random
walk, then on a component

```text
(partial partial^*)^dagger
  =(1/6) sum_(t>=0)(P^t-Pi),                            (PSE17)
```

where `Pi` projects onto constants.  The constant term cancels between
the two endpoints of an edge.  Finite propagation and the spectral bound
therefore give constants `C<infinity`, `rho<1`, independent of `n`, with

```text
|P_(cut,n)(e,f)|<=C rho^(dist(e,f))                    (PSE18)
```

for distinct edges in the same component; it is zero between components.

Now let `N_n=<h(2),w>` and let `chi` be its Weyl sign.  Fix an edge `e` and
form the unnormalized signed orbit source

```text
x_n=sum_(g in N_n) chi(g) delta_(ge),
y_n=P_(cut,n)x_n.                                      (PSE19)
```

The orbit points are distinct.  By `(PSE13)`, two which lie in the same
component have distance at least

```text
R_n=floor(log_6 M_n).
```

The diagonal leverage of `P_(cut,n)` is the same on all edges.  Indeed,
right multiplication by `Q_(M_n)` acts transitively on edges and permutes
the connected components.  If one component has `E` edges, it has `2E/3`
vertices, so the cut space there has rank `2E/3-1`; hence

```text
P_(cut,n)(f,f)=(2E/3-1)/E=2/3-1/E.                    (PSE20)
```

Equations `(PSE15)`, `(PSE18)`, and `(PSE20)` imply, uniformly for every
orbit edge `ge`,

```text
|chi(g)y_n(ge)-2/3|
 <=o(1)+C|N_n|rho^(R_n)=o(1),                         (PSE21)
```

because `|N_n|<=4L_n=exp(O(n))` while
`R_n=Omega(n log n)`.  In particular, for large `n`, at least `1/4` unit of
the dipole at every orbit edge is carried away from that edge.

The last step is a real-space flux identity, not a decay heuristic.  Fix an
orbit edge `f=ge=(u,v)` and set `sigma_f=chi(g)=x_n(f)`.  Orient `f` from
`u` to `v` after multiplying the orientation by `sigma_f`.  Remove `f`.
For each integer `j<R_n/4`, sum

```text
partial(y_n-x_n)=0                                    (PSE22)
```

over the radius-`j` tree ball about `u` in `Y_n-f`.  Ordinary girth follows
from `(PSE13)` by taking the identity element of `N_n`, so this ball is a
tree.  No other orbit source lies in it.  The discrete divergence theorem
then says that the current on the other boundary edges sums, with signs,
to `sigma_f-y_n(f)`.  Therefore those edges have total absolute current at
least

```text
|sigma_f-y_n(f)|=|1-sigma_f y_n(f)|>=1/4.              (PSE23)
```

The shell edge sets are disjoint as `j` varies.  The radius-`R_n/4`
endpoint neighborhoods belonging to distinct orbit edges are also disjoint
after decreasing the universal radius constant: otherwise a path joining
them would contradict `(PSE13)`.  Summing `(PSE23)` first over shells and
then over the orbit gives

```text
||y_n||_1 >= c |N_n| R_n.                              (PSE24)
```

Finally, `P_chi` commutes with `P_(cut,n)` by the reducing-space identity
`(SOG3)`, and

```text
(P_chi P_(cut,n))delta_e=y_n/|N_n|.
```

The product is self-adjoint, so its infinity norm is the maximum `l_1`
column norm.  Hence `(PSE24)` proves

```text
||P_chi P_(cut,n)||_(infinity -> infinity)
 >=c R_n>=c' log M_n.                                  (PSE25)
```

On the selected space,

```text
C_(H_n)^dagger C_(H_n)=P_chi P_(cut,n).
```

Since the two Reynolds rows have a dimension-independent infinity norm,
`(PSE25)` yields

```text
||C_(H_n)^dagger||_(infinity -> infinity)
 >=c'' log M_n -> infinity.                            (PSE26)
```

The fiber-constant block `(PSE3)` has a uniformly bounded inverse by the
full-torus theorem, and its projection is the norm-one average over
`T_n/H_n`.  Splitting `C_(H_n)^dagger` with this projection shows that the
fiber-mean-zero block has norm at least the left side of `(PSE26)` minus a
fixed constant.  Thus the divergent alternative in `(PSE7)` occurs on the
explicit square-free proper-subtorus family `(PSE14)`, not merely somewhere
in the full selected space.  In view of
`right-displacement-reynolds-scalar-cb-complete`, the exact-endpoint scalar
and completely bounded inverse gate is false.  This does not address a
different passive construction which avoids these congruence endpoints,
but it closes the proposed uniform Reynolds/Newton route through them.
