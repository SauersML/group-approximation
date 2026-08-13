# A bounded-degree expander cannot by itself give the integral parity decoder

Date: 2026-08-11

## Outcome

The bounded Schreier relations in
`TRUE_PROJECTIVE_SINGLETON_CENTRALIZER_ORBITS.md` solve two things:

1. they identify all ordinary singleton classes uniformly;
2. congruence expansion gives a uniformly bounded **real** `L2`
   pseudoinverse.

They cannot, by themselves, give the required integral decoder.  For every
connected graph of maximum degree at most `Delta`, every integral right
inverse of its incidence map has normalized operator norm at least

`c_Delta sqrt(log |V|)`.                                           `(BPD1)`

The obstruction already occurs on one demand `delta_u-delta_v` between
distant vertices.  Thus adding more expander edges of bounded degree does
not cross the circle-valued carry gap.  A successful TRUE proof must use the
additional Wall relations, a genuinely nonlinear paired-discriminant
decoder, or another mechanism not factoring through ordinary graph
incidence.

## 1. Integral flows contain paths

Let `Gamma=(V,E)` be a finite connected graph, orient its edges arbitrarily,
and let

`partial:Z^E -> Z^V_0`                                             `(BPD2)`

be the incidence map.  Fix vertices `u,v`.  If

`partial f=delta_u-delta_v`,                                      `(BPD3)`

then the support of `f` contains a path from `u` to `v`.

Indeed, if no such path existed, let `C` be the union of support components
containing `u`.  Summing `(BPD3)` over `C` gives one.  The sum of the
incidence of every supported edge over `C` is zero, a contradiction.
Consequently

`|supp(f)| >= dist_Gamma(u,v)`.                                   `(BPD4)`

Since every nonzero integral coefficient has absolute value at least one,

`||f||_2^2 >= dist_Gamma(u,v)`.                                   `(BPD5)`

## 2. Bounded degree forces a distant pair

If the maximum degree is `Delta>=3`, a ball of radius `r` contains at most

`1+Delta sum_(j=0)^(r-1)(Delta-1)^j`.                             `(BPD6)`

Hence a graph on `N` vertices has two vertices at distance at least
`c_Delta log N`.  The cases `Delta<=2` have an even larger linear diameter.
Combining with `(BPD5)`, some unit demand has minimum integral filling norm
at least `c_Delta^(1/2) sqrt(log N)`.

## 3. Normalization does not remove the divergence

Equip source and target with normalized counting norms.  If
`|E|<=Delta |V|/2`, then

`||f||_(2,E)^2=||f||_2^2/|E|`,
`||delta_u-delta_v||_(2,V)^2=2/|V|`.                              `(BPD7)`

Equations `(BPD5)--(BPD7)` give

`||f||_(2,E)/||delta_u-delta_v||_(2,V)
   >= sqrt(dist_Gamma(u,v)/Delta)`.                               `(BPD8)`

Taking a distant pair proves `(BPD1)`.  Notice that a real electrical flow
does not obey `(BPD4)`: it can split into many fractional paths.  This is
exactly why a spectral gap controls the real pseudoinverse but not an
integral section.

## 4. Consequence for the projective singleton fibre

The ordinary singleton fibre has `p+1` vertices.  A fixed finite family of
centralizer homotopies supplies a bounded-degree congruence Schreier graph,
and its real spectral gap is uniform.  If one attempts to decode parity
demands using only the incidence chains attached to those edges, `(BPD8)`
forces an integral norm loss at least

`c sqrt(log p)`.                                                  `(BPD9)`

Therefore the proposed graph must be viewed only as the real skeleton of a
decoder.  The remaining arithmetic proof must show that the other
degree-three Wall generators create bounded integral shortcuts after
coupling to auxiliary coordinates, or solve the paired discriminant problem
without choosing graph paths.

The same sparse-support argument in fact applies to a right inverse of the
**full** HAP degree-three boundary on all ordinary singleton differences.
That stronger statement is proved next.  It still does not rule out the TRUE
route, because the global carry theorem only needs a decoder on its
restricted harmonic/carry input lattice, not a right inverse on every
primary boundary.

## 5. The full HAP boundary also has no uniform integral right inverse

Put `N=p^2+p+1`.  Modulo two the specialized full boundary

`D_p:F_2^(20N) -> F_2^(10N)`                                  `(BPD10)`

has source-row weight at most `306` and target-column weight at most `101`.
These are the fixed Schur counts of the integral HAP resolution.  Form its
bipartite Tanner graph, with one side the `20N` source coordinates and the
other the `10N` target coordinates.  Its degrees are bounded independently
of `p`.

Every ordinary singleton cycle is nonzero.  Indeed coefficient augmentation

`F_2[P^2(F_p)] -> F_2`                                           `(BPD11)`

sends it to the first degree-two generator of the trivial-coefficient HAP
complex.  Exact augmentation gives boundary ranks `4,4` in dimensions

`F_2^4 <- F_2^10 <- F_2^20`,                                    `(BPD12)`

so trivial-coefficient `H_2` has dimension two, and stacking the first
degree-two basis vector onto `D_3` raises its rank.  Thus that generator is
not a boundary.  The exact certificate is
`experiments/sl3_trivial_mod2_h2_exact.g`, with stdout
`experiments/sl3-trivial-mod2-h2-exact.txt`.

On the other hand, centralizer homotopies prove that every difference of two
ordinary singleton cycles belongs to `im(D_p)`.  Hence all `p+1` ordinary
target vertices lie in one Tanner component.  A bounded-degree ball contains
only exponentially many vertices, so two of these distinguished vertices
`u,v` have Tanner distance at least `c log p`.

Let `x` be any mod-two source with

`x D_p=e_u+e_v`.                                                `(BPD13)`

The subgraph formed by the selected source coordinates and all their
neighbors must connect `u` to `v`.  Otherwise its component containing `u`
would by itself have boundary `e_u`, contradicting the nonvanishing proved
from `(BPD11)`.  Therefore

`|supp(x)| >= c' log p`.                                        `(BPD14)`

Every integral filling reduces to such an `x`, and every odd integral
coefficient contributes at least one to its squared Euclidean norm.  With
the natural normalized norms on the full HAP modules,

`||x||_(C3)^2 >= c' log(p)/(20N)`,
`||e_u-e_v||_(C2)^2 = 2/(10N)`.                                 `(BPD15)`

Thus every integral right inverse defined on all these pair differences has

`||S_p|| >= c'' sqrt(log p)`.                                   `(BPD16)`

This is a genuine no-go for the previously proposed full primary boundary
section.  The viable TRUE target is narrower: prove that the paired
discriminant classes actually produced by the compact harmonic plane avoid
the distant sparse demands in `(BPD13)`, or decode that restricted lattice
by a nonlinear arithmetic construction.
