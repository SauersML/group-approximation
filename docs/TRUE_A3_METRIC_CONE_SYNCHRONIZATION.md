# The `A_3(F_q)` cone synchronizes unitary and permutation connections metrically

Date: 2026-08-11

## Outcome

Dinur--Meshulam prove support-norm nonabelian cosystolic expansion for the
spherical building `A_3(F_q)` by constructing, for every edge, an explicit
contractible filling containing at most nine triangles.  Their published
statement uses the discrete length `1_(g!=1)`.

The same construction works for **every conjugation-invariant subadditive
length**.  For every `1<=r<infinity`, every group `Lambda` with such a length,
and every `Lambda`-valued edge connection `phi` on `A_3(F_q)`, there is a
vertex gauge `a` satisfying

```text
||a dot phi||_(L^r(edges))
   <=9 ||curv(phi)||_(L^r(triangles)).                (AMC1)
```

The constant is independent of `q`, `Lambda`, and the dimension of a matrix
or permutation representation.  In particular `(AMC1)` applies to

```text
Lambda=U(d),       ell(U)=||U-I||_(2,d),
Lambda=Sym(d),     ell(sigma)=d_Ham(sigma,1),         (AMC2)
```

with the same constant `9` for every `d`.

This removes the apparent `d/2` fixity loss that arises if one passes from
the support norm to normalized Hamming distance only after applying the
published theorem.  It supplies a dimension-free metric synchronization
gadget, and it also gives a direct nonlinear circle-repair theorem on these
buildings.

It does **not** prove that every hyperlinear group is sofic.  The missing
universal step is to encode an arbitrary normal-`0/1` matrix table into this
simply connected building connection while retaining its marked witness.
Becker--Lubotzky's non-stability theorem proves that one cannot simply replace
the building by the presentation complex of an infinite property-`(T)` group
and expect the same statement for all approximate representations.

A further theorem below shows that the witness need not be protected on a
closed loop.  If it is repeated over a balanced orbit of bounded-length open
paths, synchronization preserves its average holonomy with a dimension-free
constant.  The live encoding target is therefore an orbit-redundant open-path
encoding, not an unspecified relative stability theorem.

## 1. Metric cochains

Let `X` be a finite pure two-dimensional simplicial complex with the standard
probability weights

```text
c_X(tau)=1/|X(2)|,
c_X(e)=|{tau in X(2):e subset tau}|/(3|X(2)|).        (AMC3)
```

Let `Lambda` be a group and let

```text
ell:Lambda->[0,infinity)                              (AMC4)
```

satisfy

```text
ell(1)=0,
ell(g^(-1))=ell(g),
ell(hgh^(-1))=ell(g),
ell(gh)<=ell(g)+ell(h).                               (AMC5)
```

Thus `d(g,h)=ell(g^(-1)h)` is a bi-invariant pseudometric.

An oriented edge cochain satisfies

```text
phi(v,u)=phi(u,v)^(-1).                               (AMC6)
```

For an oriented triangle `tau=(u,v,w)`, put

```text
K_phi(tau)=phi(u,v)phi(v,w)phi(w,u).                  (AMC7)
```

A vertex gauge `a:X(0)->Lambda` acts by

```text
(a dot phi)(u,v)=a(u)phi(u,v)a(v)^(-1).              (AMC8)
```

The conjugacy invariance in `(AMC5)` makes the curvature norm gauge
invariant.  For `1<=r<infinity`, define

```text
||phi||_(r,E)^r=sum_(e in X(1)) c_X(e) ell(phi(e))^r,
||K_phi||_(r,T)^r=sum_(tau in X(2)) c_X(tau)
                                      ell(K_phi(tau))^r. (AMC9)
```

## 2. A metric cone lemma

The proof uses a quantitative form of nonabelian Stokes.

**Lemma 1 (bounded filling).**  Suppose an oriented loop `gamma` is the
boundary of a triangulated disk containing at most `m` triangles.  Then

```text
ell(Hol_phi(gamma))
   <=sum_(tau in disk) ell(K_phi(tau)).               (AMC10)
```

Consequently

```text
ell(Hol_phi(gamma))^r
   <=m^(r-1) sum_(tau in disk) ell(K_phi(tau))^r.     (AMC11)
```

**Proof.**  Peel boundary triangles from the disk.  At every step the
boundary holonomy changes by multiplication by a conjugate of one face
holonomy or its inverse.  This expresses the original holonomy as a product
of conjugates of the face curvatures.  Equation `(AMC10)` follows from
`(AMC5)`.  Equation `(AMC11)` is the convexity inequality

```text
(x_1+...+x_m)^r<=m^(r-1)(x_1^r+...+x_m^r).           (AMC12)
```

End proof.

Dinur--Meshulam associate to each auxiliary ordering `s` and each edge `e`
an explicit contractible subcomplex `Y_s(e)` and a vertex gauge `a_s`.  Their
displayed eight-edge loop has holonomy

```text
(a_s dot phi)(e),                                    (AMC13)
```

and is filled by `Y_s(e)`.  Let

```text
m=max_(s,e)|Y_s(e)(2)|,                              (AMC14)
D=max_tau E_s sum_(e:tau in Y_s(e)) c_X(e)/c_X(tau). (AMC15)
```

**Theorem 2 (metric cone synchronization).**  With the preceding data, some
gauge `a_s` satisfies

```text
||a_s dot phi||_(r,E)^r
   <=m^(r-1) D ||K_phi||_(r,T)^r.                    (AMC16)
```

**Proof.**  Apply `(AMC11)` to `(AMC13)`, multiply by `c_X(e)`, sum over
edges, and average over `s`:

```text
E_s ||a_s dot phi||_(r,E)^r
 <=m^(r-1) E_s sum_e c_X(e)
                    sum_(tau in Y_s(e))ell(K_phi(tau))^r
 <=m^(r-1)D sum_tau c_X(tau)ell(K_phi(tau))^r.       (AMC17)
```

At least one `s` is no larger than the average.  End proof.

This is the metric version of the cone calculation.  The support norm is
the special case `ell(g)=1_(g!=1)`, but the metric proof uses the actual
face lengths and therefore does not pass through a minimum identity gap.

## 3. The spherical building constant

Let `X=A_3(F_q)`, the order complex of the proper nonzero subspaces of
`F_q^4`.  In the proof of their Theorem 6, Dinur--Meshulam establish

```text
|Y_s(e)(2)|<=9,                                      (AMC18)
E_s sum_(e:tau in Y_s(e))c_X(e)/c_X(tau)<=9          (AMC19)
```

for every triangle `tau`.  The first inequality is visible in their
explicit cone and the second is their transitivity/counting computation.

**Theorem 3 (dimension-free `A_3` metric repair).**  For every group with an
invariant length satisfying `(AMC5)`, every `1<=r<infinity`, and every edge
cochain on `A_3(F_q)`, there exists a vertex gauge `a` such that

```text
||a dot phi||_(r,E)^r<=9^r||K_phi||_(r,T)^r,         (AMC20)
||a dot phi||_(r,E)<=9||K_phi||_(r,T).               (AMC21)
```

**Proof.**  Substitute `m=D=9` into `(AMC16)`.  End proof.

The construction gives a coboundary directly; no separate cohomology-
vanishing argument is needed.

### Matrix and permutation consequences

For normalized Hilbert--Schmidt distance,

```text
ell_d(U)=||U-I||_(2,d)                                (AMC22)
```

satisfies `(AMC5)`.  Hence every almost-flat `U(d)` connection on
`A_3(F_q)` is within normalized RMS distance at most nine times its normalized
RMS curvature defect from a pure gauge, uniformly in `d,q`.

The same statement holds for `Sym(d)` with normalized Hamming length.  This
is stronger than applying the published support theorem followed by the
pointwise comparison

```text
(2/d)1_(sigma!=1)<=d_Ham(sigma,1)<=1_(sigma!=1),     (AMC23)
```

whose left inequality is sharp on a transposition and introduces the false
appearance of a `d/2` loss.

For `Lambda=T^d` with the normalized chordal `L^2` length, `(AMC21)` is an
exact nonlinear circle-valued repair theorem.  Integer wraps never appear:
the proof stays on the compact group and uses only invariant metric
inequalities.

## 4. Interface with almost invariant masas

Sinclair--Smith prove for a masa `A` in a separably acting type-`II_1`
factor and a unitary `u` that

```text
d_2(u,N(A))/31
 <=||E_A-E_(uAu^*)||_(infinity,2)
 <=4 d_2(u,N(A)).                                    (AMC24)
```

Thus strong approximate preservation of one identified masa converts an
edge unitary into a nearby normalizer edge.  In finite matrices,
`TRUE_CARTAN_MONOMIAL_GATE.md` proves the more directly usable average-atom
estimate

```text
inf_(M monomial)||U-M||_(2,d)^2<=2 kappa_D(U).       (AMC25)
```

These results can be combined quantitatively with Theorem 3.  Let `U_e` be
an oriented `U(d)` connection on `A_3(F_q)`, and choose monomial `M_e` with
`M_(bar e)=M_e^*`.  Put

```text
epsilon^2=sum_e c_X(e)||U_e-M_e||_(2,d)^2,
delta^2=sum_tau c_X(tau)||K_U(tau)-I||_(2,d)^2.      (AMC26)
```

For a triangle, telescoping and `(x+y+z)^2<=3(x^2+y^2+z^2)` give

```text
||K_M||_(2,T)<=delta+3epsilon.                       (AMC27)
```

Here `(AMC3)` gives

```text
sum_tau c_X(tau)sum_(e subset tau)||U_e-M_e||_2^2
  =3 sum_e c_X(e)||U_e-M_e||_2^2.                   (AMC28)
```

Theorem 3 supplies a monomial vertex gauge `b` with

```text
||b dot M||_(2,E)<=9(delta+3epsilon).                (AMC29)
```

Therefore

```text
||b dot U||_(2,E)<=9delta+28epsilon.                 (AMC30)
```

Using `(AMC25)` edgewise yields the explicit sufficient estimate

```text
||b dot U||_(2,E)
 <=9delta+28 sqrt(2 sum_e c_X(e)kappa_D(U_e)).       (AMC31)
```

This synchronizes both the atom permutations and their phases.  It still
assumes the edge tables are organized over the `A_3` building and that the
same diagonal has been identified at the endpoints.

## 5. What the other supplied papers do and do not add

### Becker--Lubotzky: a necessary boundary

Becker--Lubotzky, Theorem 1.3, prove that an infinite hyperlinear
property-`(T)` group is not normalized-HS stable, and an infinite sofic
property-`(T)` group is not permutation stable.  In particular this applies
to `SL_n(Z)`, `n>=3`.

Therefore `(AMC21)` cannot hold for the presentation complex of such a group
for **all** approximate representations.  The spherical building works
because it has an explicit bounded contraction.  Any universal use in the
hyperlinear-to-sofic problem must be restricted to the normal-`0/1`/marked-
radical tables, allow flexible enlargement, or use the building as an
auxiliary synchronization gadget rather than assert ordinary group
stability.

### Kaufman--Oppenheim--Weinberger: promising for permutations, not yet metricized

Their Theorem 6.2 gives

```text
H^1(X_(n,p)^(s),Lambda)=0                            (AMC32)
```

when `Lambda` has no element of order `p`; Theorem 6.3 combines this with
nonabelian cosystolic expansion to obtain support-norm coboundary expansion.
For `Lambda=Sym(d)`, choosing `p>d` removes the torsion obstruction.  Thus
growing permutation degree is not by itself incompatible with their
cohomology-vanishing theorem.

However, the published expansion norm is
`1_(lambda!=1)`, not normalized Hamming distance.  Unlike the explicit
`A_3` cone, their global argument does not immediately provide `(AMC10)`
with uniformly bounded metric filling congestion.  A useful next theorem is
a metric version of their local-to-global cosystolic step.  If proved, it
would yield uniform Hamming synchronization complexes for growing `d` after
choosing `p>d`.

For `Lambda=U(d)` or `T^d`, the hypothesis of `(AMC32)` always fails because
these groups contain elements of order `p` for every prime.  The result cannot
directly repair arbitrary unitary or circle connections.

### Sinclair--Smith: correction, not Cartan construction

Equation `(AMC24)` is exactly a unitary-to-normalizer correction theorem once
one common masa is already approximately invariant in the strong
`infinity-to-2` metric.  It neither constructs that masa for an arbitrary
hyperlinear table nor controls fixed-point phase cancellation.  The matrix
estimate `(AMC25)` uses a weaker averaged atom displacement, but has the same
logical prerequisite: a common Cartan must first be found.

## 6. Open-path holonomies survive synchronization

Although a pure gauge has trivial holonomy on every closed loop, its open
path holonomies need not be trivial: they are the relative vertex gauges.
The following estimate shows how to retain them quantitatively.

Let `mu` be a probability distribution on oriented edge paths `P` in `X`,
each of length at most `L`.  Write `N_e(P)` for the number of occurrences of
the unoriented edge `e` in `P`, and define the weighted edge congestion

```text
C_mu=max_e E_(P~mu)N_e(P)/c_X(e).                    (AMC33)
```

For two connections `phi,theta`, put

```text
d_e(phi,theta)=ell(phi(e)^(-1)theta(e)).             (AMC34)
```

**Theorem 4 (balanced open-path transfer).**  For `1<=r<infinity`,

```text
E_(P~mu) ell(Hol_phi(P)^(-1)Hol_theta(P))^r
 <=L^(r-1) C_mu sum_e c_X(e)d_e(phi,theta)^r.        (AMC35)
```

**Proof.**  Telescoping the two path products expresses their relative
holonomy as a product of conjugates of the edgewise discrepancies.  Hence

```text
ell(Hol_phi(P)^(-1)Hol_theta(P))
 <=sum_(e in P)d_e(phi,theta).                       (AMC36)
```

Raise this to the `r`th power using `(AMC12)`, average over `P`, and use
`(AMC33)`.  End proof.

Apply this to the pure-gauge connection

```text
theta_a(u,v)=a(u)^(-1)a(v)                           (AMC37)
```

produced by Theorem 3.  Conjugacy invariance gives

```text
d_e(phi,theta_a)=ell((a dot phi)(e)).                (AMC38)
```

Combining `(AMC21)` and `(AMC35)` yields

```text
||Hol_phi(P)^(-1)a(start(P))^(-1)a(end(P))||_(L^r(mu))
 <=9 L^(1-1/r) C_mu^(1/r)||K_phi||_(r,T).            (AMC39)
```

### Uniform automorphism orbits in `A_3(F_q)`

Take one path `P_0` of length at most `L` and let `mu` be the uniform orbit
of `P_0` under `GL_4(F_q)`.  The building has three unoriented edge types,
according to the two dimensions in a comparable pair.  The automorphism
group is transitive on each type, and every chamber contains one edge of
each type.  Therefore the total edge weight of every type is `1/3`.  If
`P_0` uses `n_t` edges of type `t`, then every edge of that type has load
ratio exactly `3n_t`.  Consequently

```text
C_mu=3 max_t n_t<=3L.                                (AMC40)
```

Equation `(AMC39)` becomes

```text
||Hol_phi(P)^(-1)a(start(P))^(-1)a(end(P))||_(L^r(mu))
 <=9 . 3^(1/r) L ||K_phi||_(r,T).                   (AMC41)
```

For normalized Hilbert--Schmidt RMS error this is

```text
path RMS error<=9 sqrt(3) L . curvature RMS error.   (AMC42)
```

Normalized trace is one-Lipschitz for Hilbert--Schmidt distance, and
fixed-point fraction is one-Lipschitz for Hamming distance.  Thus any trace
or fixed-point witness repeated over this path orbit survives in the endpoint
gauge differences whenever the curvature tends to zero.

The theorem does not create that repeated encoding.  It proves that once an
encoding distributes a fixed tested word over a bounded-length automorphism
orbit, metric synchronization will not erase its average witness signal.

## 7. Remaining universal bridge

Theorem 3 provides a new reusable component:

> finite unitary or permutation data already organized as an almost-flat
> `A_3(F_q)` connection can be synchronized with a dimension-free constant.

To affect the full open problem, one still needs a **witness-preserving
encoding theorem** taking an arbitrary finite normal-`0/1` hyperlinear table
to such a connection and returning a finite action after synchronization.
The encoding cannot put a nontrivial witness on a closed loop of the simply
connected building: exact synchronization would kill it.  Theorem 4 shows
that it is enough to repeat the witness as relative/open-path data on a
bounded-congestion path orbit.  A controlled presentation sector is another
possibility.

This is sharper than asking for ordinary HS or permutation stability, which
is false by Becker--Lubotzky.  The metric relative estimate is now
`(AMC39)--(AMC42)`; the next legitimate target is an **orbit-redundant
open-path encoding** of the finite-prefix table into the building.

## Primary sources

* Oren Becker and Alexander Lubotzky,
  [*Group stability and Property (T)*](https://arxiv.org/abs/1809.00632),
  Theorems 1.3 and 1.4.
* Irit Dinur and Roy Meshulam,
  [*Near Coverings and Cosystolic Expansion -- an example of topological
  property testing*](https://arxiv.org/abs/1909.08507), Theorems 4--8 and
  Figure 1.
* Tali Kaufman, Izhar Oppenheim, and Shmuel Weinberger,
  [*Coboundary expansion of coset complexes*](https://arxiv.org/abs/2411.02819),
  Theorems 2.10, 6.2, and 6.3.
* Allan M. Sinclair and Roger R. Smith,
  [*Unitary perturbations of masas in type `II_1` factors*](https://arxiv.org/abs/math/0111330),
  Theorem 5.3.
