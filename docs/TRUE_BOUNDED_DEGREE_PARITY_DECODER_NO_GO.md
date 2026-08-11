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

This note does **not** assert a lower bound for the full HAP boundary matrix:
its higher-support rows can pass through auxiliary coordinates and need not
factor through graph incidence.  It rules out only the otherwise tempting
but insufficient expander-incidence finish.
