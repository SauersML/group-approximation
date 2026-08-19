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

The companion note `TRUE_NONLINEAR_DISCRIMINANT_REPAIR_FORMULA.md` upgrades
this statement from `Theta` to the optimal nonlinear circle-repair constant
itself.  It expresses the defect at every point of `W` as the lower envelope
of the finitely many glued discriminant wells and gives the improved bounds
`sqrt(Theta^2-1)/||A|| <= C_circ <= Theta/sigma_+`.

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

Hence `u in K_X^#`.  Since `v` is primitive and `m>1`, `u` is not integral,
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

## 7. The modular certificate is virtual divisibility in degree two

The modular image condition `(ICD40)` has an exact topological meaning.
This makes the source of a possible growing modulus visible and supplies a
necessary arithmetic test before any large modular calculation.

Let `P` be the presentation `2`-complex, with one vertex, whose cellular
degree-one coboundary is `d1_1`.  If the transitive action is `X=G/H`, let

`p:P_H -> P`                                          `(ICD42)`

be the corresponding `n=[G:H]` sheeted cover.  We identify cellular
`2`-chains and `2`-cochains using the oriented cell basis.  Under this
identification, the constant lift `J` in `(ICD31)` is the cochain pullback
`p^*`, while `S` is cochain transfer.  The extra condition
`v in K_1=ker(d1_1^T)` says that the same vector is also an integral
`2`-cycle.

**Proposition 5 (finite-cover divisibility criterion).**  Let
`0!=v in K_1` be primitive and `m>1`.  The following are equivalent:

1. `Jv in im(d1_X)` modulo `m`;
2. `p^*([v])=0` in `H^2(P_H,Z/m)`;
3. the integral class `p^*([v]) in H^2(P_H,Z)` is divisible by `m`.

Whenever these conditions hold,

`m divides n ||v||^2`.                                `(ICD43)`

In particular, if `gcd(m,||v||^2)=1`, then `m divides n`.

**Proof.**  Since `P_H` has no cells above dimension two,

`H^2(P_H,Z/m)`
` =C^2(P_H,Z)/(im(d1_X)+m C^2(P_H,Z))`.              `(ICD44)`

Thus the vanishing in (2) is exactly the modular column-space statement in
(1).  The same quotient is

`H^2(P_H,Z)/m H^2(P_H,Z)`,                           `(ICD45)`

which proves the equivalence with (3).

For the divisibility assertion, choose integral cochains `a,z` such that

`Jv=d1_X a+mz`.                                      `(ICD46)`

Pair `(ICD46)` with the integral cycle `Jv`.  Naturality gives
`d1_X^T Jv=0`, so

`n||v||^2=||Jv||^2`
` =<Jv,d1_X a>+m<Jv,z>`
` =m<Jv,z>`.                                         `(ICD47)`

This proves `(ICD43)`.  Equivalently, applying cochain transfer to the
divisibility in (3) gives `n[v]=m p_!(beta)` and evaluating on the cycle
`[v]` gives the same formula.  End proof.

Combining Proposition 5 with Corollary 4 gives the exact implication

`p^*([v]) in m H^2(P_H,Z)`
`  ==> Theta(ran_R(d1_X)) >= m/(sqrt(n)||v||).`       `(ICD48)`

This is a finite-cover **virtual divisibility** problem for one fixed
presentation-complex class.  A sequence with

`m_H/sqrt([G:H]) -> infinity`                         `(ICD49)`

would disprove uniform circle repair on those covers.  Formula `(ICD43)`
shows that the largest possible scale for fixed `v` is linear in the cover
degree, so the graph-incidence value `m=n` is extremal up to the fixed
factor `||v||^2`.

This does not yet characterize all of `Theta`.  The classes detected in
`(ICD48)` lie in the invariant-transfer sector `J(K_1)` of the much larger
cycle lattice `K_X`; unrelated discriminant classes can still dominate
`(ICD14)`.  Conversely, failure of virtual divisibility for every base
cycle only closes this particular divergence mechanism.

It is also distinct from the fixed finite-image coefficient theorem in the
notepad.  That theorem concerns restriction of a group-cohomology class
with a fixed nontrivial finite-image coefficient module.  Here the
coefficient is trivial, the class lives a priori in the cohomology of the
presentation `2`-complex, and its cycle representative is used essentially
in `(ICD47)`.  Unless the presentation complex is already a `K(G,1)` in
degree two, presentation-relation classes need not come from `H^2(G,Z)`.

For the selected `SL_3(Z)` charts the next exact question can therefore be
stated without lattice numerics:

> For a short primitive `v in ker(d1_1^T)`, how divisible can the pullback
> of `[v]` become in `H^2(P_H,Z)` as `H` ranges over the chosen congruence
> stabilizers?

Any proposed modulus must first divide `[G:H]||v||^2` by `(ICD43)`.  A
positive answer at scale larger than `sqrt([G:H])` gives an explicit
divergent carry through `(ICD48)`; a uniform square-root bound closes the
entire invariant-transfer sector but not the remaining discriminant module.

## 8. Saturation torsion is exactly the gap between the two tests

The annihilator hypothesis `(ICD33)` and the modular image hypothesis
`(ICD40)` need not be equivalent.  The exact difference is the saturation
quotient already computed in the chart experiments.

For one chart abbreviate

`A=d1_X`, `K=ker(A^T) intersect Z^cells`,
`L=ran_R(A) intersect Z^cells`,
`T_X=L/A(Z^edges)`.                                  `(ICD50)`

The top cellular cohomology of the presentation cover is

`H^2(P_H,Z)=Z^cells/A(Z^edges)`.                     `(ICD51)`

Evaluation on integral `2`-cycles gives an exact sequence

`0 -> T_X -> H^2(P_H,Z)`
`  --ev--> Hom(K,Z) -> 0`.                           `(ICD52)`

**Proof of `(ICD52)`.**  The evaluation map sends the class of an integral
cell vector `z` to `k |-> <z,k>`.  Its kernel consists exactly of integral
vectors orthogonal to `K`, namely

`K_R^perp intersect Z^cells=L`,                      `(ICD53)`

and quotienting by `A(Z^edges)` gives `T_X`.  Every integer homomorphism on
`K` extends to the ambient cell lattice because `K`, as the kernel of an
integer map, is primitive.  Self-duality of the ambient standard lattice
then realizes that extension as pairing with an integral cell vector.
Hence evaluation is surjective.  End proof.

This is the degree-two universal-coefficient sequence written directly in
the presentation matrix.  In particular, `T_X` is the torsion subgroup of
`H^2(P_H,Z)`.  It is exactly the group measured by the nonunit Smith factors
of `d1_X`, not the discriminant group `D_K`.

Now take `v in K_1` and let

`alpha=p^*([v]) in H^2(P_H,Z)`.                      `(ICD54)`

Under `(ICD52)`, its evaluation functional is

`ev(alpha)(k)=<Jv,k>=<v,Sk>`.                        `(ICD55)`

Therefore `(ICD33)` says precisely that `ev(alpha)` is divisible by `m` in
the free group `Hom(K,Z)`.  Choose a lift `beta in H^2(P_H,Z)` of
`ev(alpha)/m`.  The remaining element

`t_(v,m)=alpha-m beta in T_X/mT_X`                   `(ICD56)`

is independent of the choice of `beta`.  It vanishes if and only if
`alpha` itself is divisible by `m`, equivalently if and only if the modular
image certificate `(ICD40)` holds.

**Corollary 6 (when annihilator and modular image agree).**  Under
`(ICD33)`, condition `(ICD40)` follows whenever multiplication by `m` is
surjective on `T_X`.  In particular this holds if either

`T_X=0`, or `gcd(m,|T_X|)=1`.                         `(ICD57)`

Thus the exact `p=5` certificate

`L_5=d1_5(Z^edges)`                                  `(ICD58)`

proves that the transfer-annihilator and modular-column-space tests are
equivalent on that entire chart, for every base cycle and every modulus.
At `p=3`, where `T_X~=C_3`, they are still equivalent for moduli coprime to
three; only the `3`-primary part can separate them.

### A fixed-rank transfer computation

There is no need to construct the full discriminant lattice in order to
audit this sector.  Put

`M_X=S(K_X)=p_*H_2(P_H,Z) subset K_1`.               `(ICD59)`

Equations `(ICD32)` imply

`nK_1 subset M_X subset K_1`,                        `(ICD60)`

so `M_X` has the fixed rank `rank(K_1)` and `K_1/M_X` is killed by `n`.
For `v in K_1`, define

`m_X(v)=gcd{<v,w>:w in M_X}`.                        `(ICD61)`

The set in `(ICD61)` is nonzero because it contains the pairings with
`nK_1`.  The largest modulus satisfying `(ICD33)` is exactly `m_X(v)`, and
Theorem 3 gives

`Theta(ran_R(d1_X))`
` >= m_X(v)/(sqrt(n)||v||)` whenever `m_X(v)>1`.      `(ICD62)`

Also

`m_X(v) divides n||v||^2`,                           `(ICD63)`

which recovers `(ICD43)` at the maximal annihilator.

For the chosen presentation, `rank(K_1)` is fixed while the chart cell
space grows with `|X|`.  Hence this sector reduces to finding the image of
the integer kernel under the fixed-rank map `S`, followed by Hermite or
Smith arithmetic in `K_1`; it does not require a Gram basis for all of
`K_X`.  On a saturated chart, `(ICD61)` simultaneously determines the
largest modular-image modulus for each `v`.  This is the rigorous
low-dimensional successor to both the maximal-minor saturation audit and
the full discriminant search.

## 9. The transfer quotient injects into augmentation homology

The fixed-rank subgroup `(ICD59)` has a standard homological description
which isolates the remaining integral input.  Let

`I_X=ker(S:Z[X]->Z)`                                  `(ICD64)`

be the augmentation lattice of the transitive action.  Apply cellular
homology of `P` to the coefficient sequence

`0 -> I_X -> Z[X] --S--> Z -> 0`.                    `(ICD65)`

The relevant part of the long exact sequence is

`H_2(P,Z[X]) --S--> H_2(P,Z)`
` --delta_X--> H_1(P,I_X)`.                          `(ICD66)`

Under the cell identifications already used above,

`H_2(P,Z[X])=K_X`, `H_2(P,Z)=K_1`,                  `(ICD67)`

and the first arrow is the coordinate sum `S`.  Therefore

`K_1/M_X ~= im(delta_X) subset H_1(P,I_X)`.          `(ICD68)`

This recovers `(ICD60)` from a different direction: the constant lift `J`
satisfies `S J=n`, so the finite group in `(ICD68)` is killed by `n`.

For a property-`(T)` group, the ambient group in `(ICD68)` is finite.
Indeed `I_X tensor R` is a finite-dimensional orthogonal representation.
Transitivity says that it has no invariant vectors.  Property `(T)` gives

`H^1(G,I_X tensor R)=0`.                             `(ICD69)`

Finite-dimensional duality gives the corresponding vanishing of
`H_1(G,I_X tensor R)`, and degree-one cellular homology of the presentation
complex agrees with group homology.  Hence

`H_1(P,I_X) tensor R=0`.                             `(ICD70)`

The group in `(ICD70)` is finitely generated, so it is finite.

Let

`e_X=exp H_1(P,I_X)`                                 `(ICD71)`

and, for fixed `v in K_1`, let

`g(v)=gcd{<v,w>:w in K_1}`.                          `(ICD72)`

Since `(ICD68)` is killed by `e_X`, one has

`e_X K_1 subset M_X`.                                `(ICD73)`

Taking pairings in `(ICD61)` gives the necessary bound

`m_X(v) divides e_X g(v)`.                           `(ICD74)`

Together with `(ICD63)`,

`m_X(v) divides gcd(n||v||^2,e_X g(v))`.             `(ICD75)`

Thus property `(T)` proves finiteness of the integral obstruction on each
chart, exactly as it proves a real spectral gap on each chart, but it does
not bound that obstruction uniformly.  A divergent invariant-transfer
carry for a fixed `v` forces

`e_X/sqrt(|X|) -> infinity`                          `(ICD76)`

along a subsequence, up to the fixed factor `g(v)`.  Conversely, a uniform
bound on the exponents `(ICD71)` closes this entire mechanism.

For `X=G/H`, Shapiro rewrites the next terms of `(ICD66)` as

`K_X -> K_1 -> H_1(P,I_X) -> H_1(H,Z) -> H_1(G,Z)`. `(ICD77)`

Property `(T)` makes the last two abelianizations finite, but their
finiteness alone does not control the exponent of the middle term.  At this
stage the apparent arithmetic target is therefore:

> Bound the exponent of the augmentation homology
> `H_1(P,I_X)`, or at least of its subgroup `im(delta_X)`, uniformly (or by
> `O(sqrt(|X|))`) for the selected congruence actions.

This formulation is strictly smaller than the full discriminant problem
and strictly stronger than the real Hodge gap.  It also explains why the
circle obstruction is integral: after tensoring with `R`, property `(T)`
kills `(ICD68)` completely; only its finite torsion survives.

The next proposition supplies the missing uniform exponent bound for
`SL_3(Z)` without calculating `(ICD71)`.

## 10. A finite Schur multiplier closes the invariant-transfer sector

There is a stronger presentation-independent bound.  Let

`Sigma_P=im(pi_2(P)->H_2(P,Z)) subset K_1`           `(ICD78)`

be the spherical subgroup.  The Hopf exact sequence gives

`K_1/Sigma_P ~= H_2(G,Z)`.                           `(ICD79)`

**Theorem 7 (Schur-multiplier bound).**  For every connected finite cover
`p:P_H->P`,

`Sigma_P subset M_X=p_*H_2(P_H,Z)`.                 `(ICD80)`

Consequently

`K_1/M_X` is a quotient of `H_2(G,Z)`.               `(ICD81)`

If the Schur multiplier `H_2(G,Z)` has finite exponent `E`, then, uniformly
over every finite transitive `G`-set,

`E K_1 subset M_X`,                                  `(ICD82)`

`m_X(v) divides E g(v)` for every `v in K_1`.        `(ICD83)`

**Proof.**  A spherical class in `(ICD78)` is represented by a map

`f:S^2->P`.                                          `(ICD84)`

Since `S^2` is simply connected, `f` lifts to every connected cover:

`f=p compose f_tilde`, `f_tilde:S^2->P_H`.          `(ICD85)`

On integral homology,

`f_*[S^2]=p_* f_tilde_*[S^2]`,                      `(ICD86)`

so every spherical class belongs to `M_X`.  Quotienting the inclusion
`Sigma_P subset M_X subset K_1` by `Sigma_P` and using `(ICD79)` proves
`(ICD81)`.  If `E` kills `H_2(G,Z)`, it kills its quotient `K_1/M_X`, which
is `(ICD82)`.  Pairing `(ICD82)` with `v` and taking the gcd as in
`(ICD61)` proves `(ICD83)`.  End proof.

This theorem completely rules out divergent carries of the
invariant-transfer form whenever the Schur multiplier is finite.  Indeed,
for fixed `v`, equations `(ICD62)` and `(ICD83)` leave only the fixed set of
possible annihilator moduli dividing `E g(v)`; none can grow faster than
`sqrt(|X|)`.

For the group used in the selected-chart program, van der Kallen computed

`H_2(SL_3(Z),Z) ~= C_2 directSum C_2`.               `(ICD87)`

See W. van der Kallen, [*The Schur Multipliers of `SL(3,Z)` and
`SL(4,Z)`*](https://doi.org/10.1007/BF01343979), Math. Ann. 212 (1974),
47--50.  Therefore `E=2`, and for every finite exact `SL_3(Z)` chart,

`m_X(v) divides 2 g(v)`.                             `(ICD88)`

In particular, Corollary 4 cannot produce a growing-modulus obstruction on
the selected congruence charts.  At `p=5`, saturation makes the modular
image and annihilator tests equivalent, so every modular-image modulus for
a fixed base cycle already obeys `(ICD88)`.  At nonsaturated charts the
modular test is even stronger and hence obeys the same bound.

This closes the low-dimensional invariant-cycle mechanism proposed after
`(ICD40)`.  It does **not** prove bounded `Theta`: Theorem 2 ranges over all
classes of the full discriminant group `D_(K_X)`, and most chart cycles do
not descend from `K_1`.  Any divergent `SL_3(Z)` carry must therefore be a
genuinely new-cover discriminant class, invisible to constant base cycles
and to the transfer subgroup `(ICD59)`.

## 11. The new-cover cycle quotient is the Schur multiplier of the stabilizer

The phrase "genuinely new-cover cycle" has an exact group-homological
meaning.  Continue to write `P_H -> P` for the connected cover associated
to a finite-index subgroup `H <= G`, and identify

`K_X=H_2(P_H,Z)`                                      `(ICD89)`

using the fact that the presentation complex has no cells above dimension
two.  Let

`Sigma_X=im(pi_2(P_H)->H_2(P_H,Z)) subset K_X`        `(ICD90)`

be its spherical subgroup.

**Theorem 8 (cover Hopf quotient).**  There is a natural exact sequence

`pi_2(P_H) -> K_X -> H_2(H,Z) -> 0`,                 `(ICD91)`

and hence a natural isomorphism

`K_X/Sigma_X ~= H_2(H,Z)`.                           `(ICD92)`

Under the canonical identification

`pi_2(P_H)=pi_2(P)`                                  `(ICD93)`

coming from their common universal cover, `Sigma_X` is obtained by taking
the same spherical identities among the base relators and all their lifts
to the cover.

**Proof.**  The fundamental group of `P_H` is `H`.  The Hopf exact sequence
for a connected CW complex `Y`,

`pi_2(Y) -> H_2(Y,Z) -> H_2(pi_1(Y),Z) -> 0`,        `(ICD94)`

applied to `Y=P_H`, is `(ICD91)`.  Its first image is precisely the group
defined in `(ICD90)`, proving `(ICD92)`.  A covering map induces
isomorphisms on all homotopy groups in degrees at least two; equivalently,
`P_H` and `P` have the same universal cover.  This proves `(ICD93)` and the
last assertion.  End proof.

There is also a finite-local form of this statement.  Suppose the chosen
presentation is the two-skeleton of a `K(G,1)` with finite three-skeleton.
If the attaching maps of its finitely many three-cells represent

`sigma_1,...,sigma_q in pi_2(P)`,                    `(ICD95)`

then their `G`-translates generate `pi_2(P)` as a `Z[G]`-module.  Therefore
the lifts of the same `q` bounded spherical templates, based at the points
of `X=G/H`, generate `Sigma_X`.  The number and support size of the
templates are independent of the cover.  The group `SL_3(Z)` is of type
`F_infinity`, so the selected-chart program may use such a finite list.

Theorem 8 sharpens, but does not close, the discriminant problem.  It
separates the full cycle lattice into two remaining mechanisms:

1. metric gluing inside the lattice generated by the bounded spherical
   templates;
2. lifts of the stabilizer Schur multiplier `H_2(H,Z)`.

Neither mechanism is controlled by the base Schur multiplier in Theorem 7.
In particular, `(ICD87)` bounds the quotient of **transferred base cycles**,
not `H_2(H,Z)` as `H` varies.  A proof of bounded `Theta` must therefore
give an integral, norm-controlled decoder for the spherical-template
lattice and control the discriminant geometry of the stabilizer homology.
Real degree-one Hodge expansion only controls the orthogonal projection
onto `K_X`; it supplies neither of these two integral statements.

## 12. Scalar involutions turn discriminant gluing into nearest-code decoding

The scalar-involution computation in `experiments/sl3_carry_results.md` has
a standard exact lattice interpretation.  Let `T` be an isometric
involution of the ambient standard lattice `Lambda`, assume `T(K)=K`, and
write

`V_+=ker(T-1)`, `V_-=ker(T+1)`,                       `(ICD96)`
`K_+=K intersect V_+`, `K_-=K intersect V_-`,
`K_0=K_+ orthogonalDirectSum K_-`.                    `(ICD97)`

Every `k in K` satisfies

`2k=(k+Tk)+(k-Tk) in K_0`.                           `(ICD98)`

Hence

`C=K/K_0`                                            `(ICD99)`

is a finite elementary abelian two-group.  For any integral lattice `M`,
write

`b_M:D_M times D_M -> Q/Z`,
`b_M(x+M,y+M)=<x,y> mod Z`                           `(ICD100)`

for its discriminant pairing.

**Theorem 9 (involution overlattice formula).**  Projection of the
overlattice `K` into `D_(K_0)` embeds `C` as an isotropic subgroup for
`b_(K_0)`.  Moreover,

`K^#/K_0 = C^perp subset D_(K_0)`,                   `(ICD101)`

and therefore

`D_K ~= C^perp/C`.                                   `(ICD102)`

For `xi in C^perp`, decompose its class under

`D_(K_0)=D_(K_+) directSum D_(K_-)`                  `(ICD103)`

as `xi=(xi_+,xi_-)`.  Then its shortest radius in the quotient class is

`rho_K(xi+C)^2`
` =min_(c in C) (`
`    rho_(K_+)(xi_+-c_+)^2`
`   +rho_(K_-)(xi_--c_-)^2).`                        `(ICD104)`

**Proof.**  Since `K` is integral and lies between `K_0` and `K_0^#`, the
pairing of any two elements of its image `C` is integral.  This is exactly
isotropy in `(ICD100)`.  An element `x in K_0^#` lies in `K^#` if and only
if it pairs integrally with every element of `K`, equivalently if and only
if `x+K_0` lies in `C^perp`.  This proves `(ICD101)`.  Quotienting by
`K/K_0=C` gives `(ICD102)`.

The lattice `K` is the union of the `K_0`-cosets indexed by `C`.  Thus the
distance from a representative of `xi` to `K` is the minimum, over
`c in C`, of its distance to that `K_0`-coset.  The eigenspaces in
`(ICD96)` are orthogonal and `K_0` is their orthogonal direct sum, so the
squared distance to each coset is the sum of the two sector distances.
This is `(ICD104)`.  End proof.

Two consequences matter for the current charts.

First, for every odd prime `ell`, localization at `ell` kills the index in
`(ICD98)`.  Therefore

`D_K[ell^infinity]`
` ~= D_(K_+)[ell^infinity] directSum`
`     D_(K_-)[ell^infinity].`                        `(ICD105)`

Thus scalar gluing is a purely two-primary phenomenon.  The odd-primary
factors seen in both exact `p=3` sector Gram matrices are genuine sector
obstructions; no binary gluing argument can remove them.

Second, suppose `T` exchanges `N` disjoint pairs of standard coordinates.
The map which records, modulo two, the sum on each pair identifies `(ICD99)`
with the gluing code computed by `sl3_carry_gluing_code.py`.  If a codeword
`c` has Hamming weight `w`, then every representative has half-integral
`+` and `-` projections on those `w` pairs.  Consequently

`rho_(K_+)(c_+)^2 >= w/2`,
`rho_(K_-)(c_-)^2 >= w/2`,
`rho_(K_0)(c)^2 >= w`.                               `(ICD106)`

High support is therefore expensive before quotienting.  What remains is
not generation of `C` by low-weight words: equation `(ICD104)` asks for the
distance of every class in `C^perp` to the **whole code** in the sector Gram
metrics.  A successful symmetry proof must bound this weighted nearest-code
problem simultaneously with the corresponding glued radius on the
orthogonal range lattice.  Code dimension, minimum Hamming weight, and a
sparse generating basis do not determine either radius in Theorem 2.

## 13. The gluing code is a mod-two homology image

There is a topological description of the code in Theorem 9.  Suppose the
involution `T` acts freely on every cell of a finite presentation cover
`P_H` and commutes with the covering action.  Put

`P_J=P_H/<T>`,                                        `(ICD107)`

so in the scalar chart `H` is the stabilizer of a vector and `J` is the
stabilizer of its sign-orbit.  On cellular chains define

`q:C_*(P_H,Z)->C_*(P_J,F_2)`                         `(ICD108)`

by adding the two coefficients in every `T`-orbit and reducing modulo two.
The pairwise sum and difference subcomplexes are

`C_*^+=ker(T-1)`, `C_*^-=ker(T+1)`.                  `(ICD109)`

They are respectively the integral chains of `P_J` with the trivial and
sign local systems.  Pairwise parity gives a short exact sequence of chain
complexes

`0 -> C_*^+ directSum C_*^- -> C_*(P_H,Z)`
`  --q--> C_*(P_J,F_2) -> 0`.                        `(ICD110)`

**Theorem 10 (homological gluing code).**  For a two-dimensional
presentation complex, the code `C=K/K_0` in `(ICD99)` satisfies

`C=im(H_2(P_H,Z) --q_*--> H_2(P_J,F_2))`             `(ICD111)`

and, if `delta` is the connecting map of `(ICD110)`,

`C=ker(delta:H_2(P_J,F_2)`
`             ->H_1(C_*^+ directSum C_*^-)).`        `(ICD112)`

Let `Sigma_J^(2)` denote the spherical subgroup of
`H_2(P_J,F_2)`.  Naturality of the Hopf maps further gives

`C/(C intersect Sigma_J^(2))`
` ~= im(H_2(H,Z)->H_2(J,F_2)).`                      `(ICD113)`

**Proof.**  On one paired cell orbit, the kernel of

`Z^2 -> F_2`, `(a,b) |-> a+b mod 2`                 `(ICD114)`

is generated by `(1,1)` and `(1,-1)`.  The boundary commutes with `T`, so
these orbitwise sequences assemble to `(ICD110)`.  Its homology sequence
contains

`H_2(C_*^+ directSum C_*^-) -> H_2(P_H,Z)`
` --q_*--> H_2(P_J,F_2) --delta--> ...`.             `(ICD115)`

There are no three-cells.  Hence the first two groups in `(ICD115)` are
`K_0` and `K`, and the first arrow is their inclusion.  Exactness proves
`(ICD111)--(ICD112)`.

The covering map induces the inclusion `H->J`.  Naturality of the Hopf
exact sequences gives a commutative square from `q_*` to the coefficient
reduction of

`H_2(H,Z)->H_2(J,F_2)`.                              `(ICD116)`

The vertical Hopf map from `H_2(P_H,Z)` is surjective by Theorem 8, so the
image of `C` in `H_2(J,F_2)` is exactly the image in `(ICD116)`.  The
kernel of the lower Hopf map is `Sigma_J^(2)`.  Restricting that map to
`C` and applying the first isomorphism theorem proves `(ICD113)`.  End
proof.

Thus the weight-one words in the measured code need not signal a global
failure: they can lie in the spherical subgroup.  After the finitely many
bounded spherical templates are separated, every nonspherical gluing word
comes from the explicit stabilizer-homology image in `(ICD113)`.  Combining
Theorems 9 and 10 leaves a concrete two-part task: price the spherical code
by a local integral decoder, and price the image of stabilizer homology by
the `+/-` sector Gram forms.  This is narrower than unrestricted CVP in the
full cycle discriminant group.

## 14. Projective charts remove scalar gluing from the selected family

The scalar code is unavoidable if one insists on the charts

`X_p=F_p^3 minus {0}`.                               `(ICD117)`

It is not unavoidable in a selected-chart argument.  Let

`Y_p=P^2(F_p)=X_p/F_p^*`.                            `(ICD118)`

Reduction modulo `p` gives an exact action of `SL_3(Z)` on `Y_p`, and these
actions form an asymptotically free family.

**Proposition 11 (projective selected charts).**  For every fixed
`1!=g in SL_3(Z)`,

`|Fix_(Y_p)(g)|/|Y_p| -> 0`                          `(ICD119)`

as `p` tends to infinity through primes.  The relator maps on `Y_p` are the
trivial scalar-character blocks of the maps on `(ICD117)`.  Consequently
the universal rational Hodge certificate in `TRUE_SL3_HODGE_SOS.md` gives
the same uniform positive real degree-one gap on the projective family,
while the involution code `C` in Theorems 9 and 10 is absent.

**Proof.**  A non-scalar matrix in `SL_3(F_p)` fixes only its eigenlines.
The largest possible fixed projective locus is a projective line together
with one further point, so

`|Fix_(Y_p)(g)| <= p+2`, `|Y_p|=p^2+p+1`.            `(ICD120)`

For a fixed integral matrix `g`, scalar reduction modulo infinitely many
primes would force every off-diagonal entry and every difference of
diagonal entries of `g` to vanish over `Z`.  The only integral scalar in
`SL_3(Z)` is the identity.  Thus `(ICD120)` applies for all but finitely
many primes and proves `(ICD119)`.

Scalar multiplication commutes with every elementary generator.  Passing
from `(ICD117)` to `(ICD118)` is therefore precisely restriction to the
trivial scalar local system.  The group-ring sum-of-squares inequality is
valid in every unitary representation, hence also in these permutation
representations.  There is no residual scalar cover in `(ICD118)`, so no
scalar gluing code occurs.  End proof.

This does not prove bounded carry transversality.  The projective cycle
lattice can still have large odd-primary discriminant and nontrivial
stabilizer homology; at `p=3` it is exactly the `+` sector in the stored
sector calculation.  It does, however, remove the entire two-primary
nearest-code problem from any argument that only needs one asymptotically
free exact chart family.  The nonzero-vector charts remain useful for
testing twisted scalar local systems, but controlling every scalar character
is stronger than what such a selected-family proof requires.

## 15. Short dual cycles are forced into stabilizer homology

The finite spherical templates in Theorem 8 give one uniform metric
consequence without any closest-vector computation.  Suppose

`sigma_1,...,sigma_q in K_univ`                      `(ICD121)`

are integral spherical templates whose translates generate `Sigma_X` in
every finite cover, and put

`0<B=max_i ||sigma_i||`.                             `(ICD122)`

Translation preserves the Euclidean norm, so every lifted generator has
norm at most `B`.

**Proposition 12 (short-vector localization).**  If `u in K_X^#` and

`||u||<1/B`,                                         `(ICD123)`

then `u` is orthogonal to `Sigma_X`.  Under the real Hopf quotient,

`K_(X,R)/span_R(Sigma_X) ~= H_2(H,R)`,               `(ICD124)`

so all such `u` lie in the orthogonal harmonic representative of the
stabilizer homology.  In particular, if

`H_2(H,R)=0`,                                        `(ICD125)`

then every nonzero discriminant class `c in D_(K_X)` satisfies

`rho_(K_X)(c)>=1/B`.                                 `(ICD126)`

**Proof.**  For every lifted spherical generator `sigma`, dual-lattice
membership gives

`<u,sigma> in Z`.                                    `(ICD127)`

Cauchy--Schwarz and `(ICD123)` give

`|<u,sigma>| <= ||u|| ||sigma|| <1`,                 `(ICD128)`

so the integer in `(ICD127)` is zero.  The generators span `Sigma_X`,
proving the first assertion.  Tensoring `(ICD92)` with `R` proves
`(ICD124)`.  Under `(ICD125)`, the spherical subgroup spans all of
`K_(X,R)`, so the first assertion forces `u=0`.  A shortest representative
of a nonzero class cannot be zero, proving `(ICD126)`.  End proof.

This isolates the two possible sources of divergent ratios in `(ICD14)`.
If the denominator radii tend to zero, Proposition 12 forces those classes
into nonzero real `H_2(H,R)`.  If the stabilizers are rationally
two-acyclic, denominator collapse is impossible and any divergence must
instead come from glued range radii tending to infinity while the cycle
radii stay uniformly positive.  Controlling only small leverage scores
therefore addresses the first mechanism but not the second.
