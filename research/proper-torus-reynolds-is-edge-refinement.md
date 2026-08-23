---
rg: 2
id: proper-torus-reynolds-is-edge-refinement
kind: claim
title: A proper-subtorus Reynolds complex refines edges but does not cover triangles
distinct_from:
  full-torus-reynolds-is-multipartite-curl: that identifies the full-torus column with an ordinary clique-complex curl; this compares a proper subtorus with the full-torus edge and triangle sets.
  multipartite-triangle-curl-has-uniform-infinity-green-bound: that constructs a uniformly bounded Green operator for the base clique complex; this proves why that operator does not lift to the extra-label sector.
  right-u-reynolds-has-torus-hecke-blocks: that decomposes the proper-subtorus domain into explicit torus-character blocks; this gives the global labeled-edge geometry and the obstruction to a covering-space contraction.
  fourth-power-mersenne-reynolds-levels-have-diagonal-crt-coupling: that produces an explicit unbounded-index composite family and isolates its right-unipotent blocks; this gives the exact edge-refinement model shared by all proper-subtorus levels.
  flat-gain-multipartite-covers-have-uniform-green-bound: that proves every genuine flat gain cover is gauge-trivial and retains the base Green bound; this proves the Reynolds refinement is not such a cover.
  signed-orbit-averaging-does-not-divide-green-cost: that proves averaging a generic electrical routing over the growing signed torus orbit has norm one rather than inverse-orbit-size cost; this identifies the labeled geometry.
---

**ESTABLISHED; COVERING-TRANSFER NO-GO.**  Let `Q` be a finite congruence
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
the proposed **covering-space** proof of a uniform Green bound.  It is not
a divergent Green mode: the Moore--Penrose inverse may still be uniformly
bounded because the selected label triples can couple the fiber-mean-zero
sector efficiently.

The exact remaining theorem is therefore finite and concrete.  On the
orthogonal complement of `(PSE3)` and of `ker(C_(H_n))`, prove a uniform
infinity Green bound, or construct `f_n` in that sector with

```text
||f_n||_infinity /
max(||C_(1,H_n)f_n||_infinity,||C_(2,H_n)f_n||_infinity)
 -> infinity.                                          (PSE7)
```

The base multipartite contraction settles none of `(PSE7)` because its
entire image lies in the fiber-constant summand `(PSE3)`.

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
positive proof needs arithmetic cancellation or a genuinely new
constrained routing.

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

This theorem still does not by itself prove the divergent alternative in
`(PSE7)`.  Let `P_cut` be the Moore--Penrose cut projection for the
unconstrained `K_1/K_2` incidence graph and let `P_chi` be the signed
`N_n` Reynolds projection.  The exact compression identity is

```text
C_(H_n)^dagger C_(H_n)=P_chi P_cut
```

on the selected input space.  Relative girth separates the centers of the
translated electrical rows, but electrical rows have global support.
Their tails may enter the other orbit neighborhoods and cancel after the
signed average.  Hence disjoint **balls** do not justify the disjoint-
support equality `(SOG8)`.  To turn `(PSE13)` into divergence one still
needs a quantitative off-diagonal decay/lower-current theorem strong enough
to show

```text
||P_chi P_cut||_(infinity -> infinity)
  >= c log M_n.                                        (PSE14)
```

Conversely, a uniform bound must exploit cancellation between precisely
these globally supported translated electrical rows.  The exact frontier
is therefore narrower than `(PSE7)`: prove or refute `(PSE14)` using the
arithmetic Green kernel.  Neither a base simplicial contraction nor relative
girth alone decides it.
