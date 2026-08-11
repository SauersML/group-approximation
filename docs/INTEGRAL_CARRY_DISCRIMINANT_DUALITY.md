# Integral carry transversality is a discriminant-lattice distortion

Date: 2026-08-11

## 1. Purpose

`TRUE_INTEGRAL_CARRY_TRANSVERSALITY.md` reduces exact-chart circle-cocycle
repair to the constant

`Theta(W)=sup_(z in Z^m minus L) dist(z,L)/dist(z,W)`,
`L=W intersect Z^m`,                                    `(ICD1)`

where `W=ran(d1)` is a rational subspace of the real relator-cell space.
This note gives an exact finite description of `Theta` in terms of the
discriminant gluing between the saturated range lattice and the integral
cycle lattice.

The description separates two invariants which should not be conflated:

* Smith factors of `d1` measure the finite quotient
  `L/d1(Z^edges)`;
* carry transversality is controlled by the embedding of the **saturated**
  lattice `L` in the ambient unimodular cell lattice.

In particular, saturation of the integer image does not bound `Theta`.

## 2. Orthogonal primitive lattices

Let

`Lambda=Z^m subset R^m`                                `(ICD2)`

with its standard Euclidean inner product, and let `W` be a proper rational
subspace.  Put

`L=Lambda intersect W`,
`K=Lambda intersect W^perp`.                           `(ICD3)`

Both `L` and `K` are primitive sublattices of `Lambda`.  Write

`L^#={a in W : <a,L> subset Z}`,
`K^#={u in W^perp : <u,K> subset Z}`                  `(ICD4)`

for their Euclidean dual lattices, and

`D_L=L^#/L`, `D_K=K^#/K`                              `(ICD5)`

for the finite discriminant groups.  Let `p_W,p_K` be the two orthogonal
projections.

**Proposition 1 (unimodular gluing).**

`p_W(Lambda)=L^#`, `p_K(Lambda)=K^#`.                 `(ICD6)`

Moreover, projection induces isomorphisms

`Lambda/(L directSum K) ~= D_L ~= D_K`.               `(ICD7)`

Consequently there is a canonical gluing isomorphism

`gamma:D_K -> D_L`                                   `(ICD8)`

characterized as follows: if `z in Lambda`, `a=p_W z`, and `u=p_K z`, then

`gamma(u+K)=a+L`.                                     `(ICD9)`

**Proof.**  If `z in Lambda` and `ell in L`, then

`<p_W z,ell>=<z,ell> in Z`,                           `(ICD10)`

so `p_W(Lambda) subset L^#`.  Conversely, an element `a in L^#` defines an
integer homomorphism `ell |-> <a,ell>` on `L`.  Primitivity makes
`Lambda/L` free abelian, so this homomorphism extends to `Lambda`.  The
standard lattice `Lambda` is self-dual; hence the extension is
`x |-> <z,x>` for some `z in Lambda`.  Its restriction to `L` says
`p_W z=a`.  This proves the first equality in `(ICD6)`; the second is
identical.

The map

`Lambda/(L directSum K) -> D_K`, `z |-> p_Kz+K`       `(ICD11)`

is surjective by `(ICD6)`.  If `p_Kz in K`, then
`p_Wz=z-p_Kz` is integral and belongs to `W`, hence lies in `L`; its kernel
is therefore exactly `L directSum K`.  This proves the right isomorphism in
`(ICD7)`, and the left one is identical.  Pair the two projections of the
same `z` to obtain `(ICD8)--(ICD9)`.  End proof.

In particular,

`|D_L|=|D_K|=[Lambda:L directSum K]`.                 `(ICD12)`

This is the discriminant order of either primitive orthogonal lattice.

## 3. Exact formula for `Theta`

For a class `c` in either discriminant group, define its shortest-coset
radius by

`rho_L(c)=min{||a||:a in L^#, a+L=c}`,               `(ICD13)`

and similarly `rho_K`.  These minima exist because the lattices are
discrete.

**Theorem 2 (discriminant formula).**  If `W` is proper, then

`Theta(W)^2`
` =max(1, max_(0!=c in D_K)`
`       (1+rho_L(gamma(c))^2/rho_K(c)^2)).`           `(ICD14)`

In particular,

`Theta(W)=1` if and only if `D_K` is trivial.          `(ICD15)`

**Proof.**  Projection in Proposition 1 identifies every coset
`z+L in Lambda/L` with the unique vector

`u=p_Kz in K^#`.                                      `(ICD16)`

The zero vector corresponds exactly to `z in L`.  Orthogonality gives

`dist(z,W)=||u||`,                                    `(ICD17)`

and

`dist(z,L)^2`
` =||u||^2+dist(p_Wz,L)^2`
` =||u||^2+rho_L(gamma(u+K))^2`.                      `(ICD18)`

For a fixed nonzero discriminant class `c=u+K`, the numerator contributed
by the `W` component in `(ICD18)` is fixed, while the ratio is maximized by
choosing the shortest representative of `c` in `K^#`.  This gives the
second maximum in `(ICD14)`.  If `u` is a nonzero element of `K`, its
discriminant class is zero and `(ICD18)` gives ratio one.  Taking the maximum
proves `(ICD14)`.  A nonzero discriminant class has positive shortest radius
on both sides, proving `(ICD15)`.  End proof.

Thus the apparently infinite supremum `(ICD1)` is a finite collection of
shortest-vector-in-coset problems, one for each nonzero discriminant class.
No enumeration of arbitrary integral carries is logically necessary once
the gluing is known.

### Exact Gram-matrix coordinates

Let the columns of an integer matrix

`C in M_(m x r)(Z)`                                   `(ICD14a)`

be a `Z`-basis of the primitive cycle lattice `K`, and put

`G_K=C^T C`.                                          `(ICD14b)`

Then

`D_K ~= Z^r/G_K Z^r`.                                `(ICD14c)`

Explicitly, `q in Z^r` represents the dual-lattice vector

`u_q=C G_K^(-1) q in K^#`;                           `(ICD14d)`

changing `q` by `G_K n` changes `u_q` by the cycle `Cn`.  Its shortest
radius is the exact quadratic closest-vector problem

`rho_K(q)^2`
` =min_(n in Z^r) (q+G_K n)^T G_K^(-1)(q+G_K n)`.    `(ICD14e)`

Primitivity of `K` makes `C^T:Z^m->Z^r` surjective.  Choose any integral
`z_q` with

`C^T z_q=q`.                                         `(ICD14f)`

Then

`a_q=z_q-u_q in L^#`                                 `(ICD14g)`

represents `gamma(q)`, and

`rho_L(gamma(q))=dist(a_q,L)`.                        `(ICD14h)`

Equations `(ICD14c)--(ICD14h)` turn Theorem 2 into an exact finite
integer/rational certificate.  The Smith normal form of the **cycle Gram
matrix** `G_K` enumerates the relevant discriminant classes; the Smith form
of the original relator map enumerates the different quotient `(ICD19)`
below.

## 4. Smith saturation is a different invariant

Let `A:Z^e->Z^m` be an integral matrix with real range `W`.  Its nonunit
Smith factors determine

`L/A(Z^e)`, `L=W intersect Z^m`.                      `(ICD19)`

The group in `(ICD19)` records failure of the integer image to be saturated.
By contrast, `(ICD14)` depends only on the primitive embedding

`L subset Z^m`                                       `(ICD20)`

and its orthogonal cycle lattice `K`.  It is unchanged if `A(Z^e)` is
replaced by any finite-index sublattice of `L`.

The bounded-degree expander example from
`TRUE_INTEGRAL_CARRY_TRANSVERSALITY.md` is decisive.  For the oriented
incidence map of a connected graph,

`A(Z^edges)={z in Z^n:sum z_i=0}=L`,                 `(ICD21)`

so every nonzero Smith factor is one.  Nevertheless

`W=1^perp`, `K=Z 1`,
`D_K=(1/n)Z 1 / Z 1 ~= Z/n`,                         `(ICD22)`

and the class of `u=(1/n)1` is glued to the class of

`a=e_1-(1/n)1`.                                      `(ICD23)`

Their shortest radii are

`rho_K=1/sqrt(n)`, `rho_L=sqrt(1-1/n)`.              `(ICD24)`

More generally, for the class `k mod n` put
`r=min(k,n-k)`.  Its two squared radii are `r^2/n` and
`r(n-r)/n`, so its squared ratio in `(ICD14)` is `n/r`.  The maximum occurs
at `r=1`.  Formula `(ICD14)` therefore gives exactly

`Theta(W)=sqrt(n)`.                                   `(ICD25)`

Therefore `image_is_saturated=true` is compatible with divergent carry
distortion.  Conversely, nonunit Smith factors do not by themselves force
large `Theta`.

## 5. Consequences for the current `SL_3(Z)` search

For a finite `SL_3(Z)` chart and `A=d1`, define

`L=ran_R(d1) intersect Z^cells`,
`K=ker(d1^T) intersect Z^cells`.                      `(ICD26)`

The current exact Smith calculation correctly measures `L/d1(Z^edges)`.
Its factor `3` at `p=3` is real information about saturation, but it is not
the discriminant group in `(ICD14)` and cannot certify bounded or unbounded
circle repair.

The leverage and LLL searches target the right geometric quantity more
directly.  For an integral carry `z`,

`u=p_Kz`                                              `(ICD27)`

is a vector of `K^#`, and its residual norm is exactly
`dist(z,ran_R(d1))`.  If `u!=0`, integrality gives the coarse bound

`dist(z,L)>=1`, hence `Theta>=1/||u||`.               `(ICD28)`

The exact formula shows how to turn such a candidate into a complete
certificate:

1. compute or characterize the primitive cycle lattice `K`;
2. identify the class `c=u+K` and its glued class `gamma(c)`;
3. certify the two coset minima `rho_K(c)` and `rho_L(gamma(c))`;
4. control every nonzero discriminant class, using chart symmetry rather
   than an unrestricted floating LLL search.

Stable one-cell leverage near `4.543` proves only that those particular
coordinate classes do not exhibit divergence.  Coordinated carries can lie
in other discriminant classes with much shorter `K^#` representatives.
Conversely, a large-coefficient LLL vector with small floating residual is
not a proof until its residual is certified and its paired `L^#/L` coset is
controlled.

The next theoretical target is therefore the discriminant module of the
`SL_3(Z)` relator-cycle lattice as a module for the finite chart symmetry.
Showing that the ratios in `(ICD14)` stay bounded would close exact-chart
circle repair.  Producing classes for which the ratio diverges would give a
concrete nonlinear instability architecture for the FALSE lane.

## 6. A transfer-divisibility criterion for divergent carries

The discriminant formula also gives a cheaper exact obstruction which does
not require constructing a basis of the full chart cycle lattice.

Let `X` be a transitive finite exact action of size `n`.  Write

`C_2(X)=Z^(R times X)`, `C_2(1)=Z^R`                 `(ICD29)`

for the chart and trivial-coefficient relator-cell lattices.  Let

`K_X=ker(d1_X^T) intersect C_2(X)`,
`K_1=ker(d1_1^T) intersect C_2(1)`.                  `(ICD30)`

Define the constant lift and transfer

`J:C_2(1)->C_2(X)`, `(Jv)_(r,x)=v_r`,
`S:C_2(X)->C_2(1)`, `(Sk)_r=sum_(x in X) k_(r,x)`.   `(ICD31)`

Naturality of the presentation boundary gives

`J(K_1) subset K_X`, `S(K_X) subset K_1`,
`S J=n id`.                                           `(ICD32)`

**Theorem 3 (transfer annihilator obstruction).**  Suppose there are an
integer `m>1` and a nonzero primitive `v in K_1` such that

`<v,S k> in m Z` for every `k in K_X`.                `(ICD33)`

Then

`Theta(ran_R(d1_X)) >= m/(sqrt(n)||v||)`.             `(ICD34)`

Consequently, if bounded-norm `v_X` satisfy `(ICD33)` along a family with
`m_X/sqrt(|X|)->infinity`, exact-chart circle repair is not uniform on that
family.

**Proof.**  Put

`u=(1/m)Jv in (K_X)_R`.                               `(ICD35)`

For every `k in K_X`, equations `(ICD31)` and `(ICD33)` give

`<u,k>=(1/m)<v,S k> in Z`.                            `(ICD36)`

Hence `u in K_X^#`.  Since `v` is primitive and `n>1`, `u` is not integral,
so it represents a nonzero discriminant class.  Proposition 1 supplies an
integer carry `z` whose orthogonal projection to `(K_X)_R` is `u`.  This
carry does not lie in the saturated range lattice.  Distinct integral
vectors have Euclidean distance at least one, and therefore

`dist(z,L_X)>=1`.                                     `(ICD37)`

On the other hand,

`dist(z,ran_R(d1_X))=||u||=sqrt(n)||v||/m`.           `(ICD38)`

Their ratio is `(ICD34)`.  End proof.

Condition `(ICD33)` is a finite modular statement.  Reducing modulo `m`, it
says that the class of `v` annihilates the transferred cycle module

`S(K_X) mod m subset K_1 mod m`.                      `(ICD39)`

This is the correct low-dimensional preliminary test for an
`m/sqrt(n)`-scale carry obstruction.  It differs from computing the rank of
`d1_X` modulo small primes: that rank detects divisibility in
`L_X/d1_X(Z^edges)`, while `(ICD39)` detects the gluing of the orthogonal
cycle lattice.  Failure of `(ICD33)` does not prove bounded `Theta`; it only
rules out this invariant-cycle mechanism.

There is a directly checkable sufficient condition for `(ICD33)`.

**Corollary 4 (modular image certificate).**  If

`Jv in im(d1_X: (Z/m)^edges -> (Z/m)^cells)`,          `(ICD40)`

then `(ICD33)` holds and hence so does `(ICD34)`.

**Proof.**  Write `Jv=d1_X a` modulo `m`.  For an integral
`k in ker(d1_X^T)`,

`<Jv,k>=<a,d1_X^T k>=0 mod m`.                        `(ICD41)`

Apply Theorem 3.  End proof.

Thus one need not compute the full modular rank.  One should test membership
of the finitely many constant lifts `Jv`, for a basis or short vectors of
`K_1`, in the modular column space of `d1_X`.  A modulus
`m` growing faster than `sqrt(|X|)` gives a divergent carry certificate.

For the graph-incidence calibration, `K_1=Z`, the chart cycle lattice is the
constant vector `Z 1`, and transfer has image `nZ`.  Taking `v=1` recovers
`Theta=sqrt(n)`.  For the `SL_3(Z)` charts, computing the subgroup
`S(K_X) subset K_1` is therefore a more targeted exact audit than further
maximal-minor searches in the relator image.
