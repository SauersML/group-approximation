---
rg: 2
id: fixed-holonomy-character-regularization-and-quantum-fiber-proof
kind: proof
title: Fixed-holonomy character regularization and an exact quantum-fiber countermodel
proves:
  - property-t-does-not-kill-boolean-fiber-holonomy
uses:
  - boolean-atom-overlap-spatializes-arrows-but-full-corners-stay-diffuse
  - finite-schreier-holonomy-rounding-criterion
  - coset-wreath-wall-survives-full-commutant-corners
---

# Fixed-holonomy character regularization and an exact quantum-fiber countermodel

All Hilbert--Schmidt norms below are normalized by the ambient matrix
dimension.

## 1. A finite action-groupoid cocycle is stabilizer holonomy

Let §K§ act on a finite set §Y§ and suppose first that the action is
transitive.  Give each §y in Y§ a Hilbert space §V_y§ of dimension §r§.
Let

~~~text
c(g,y):V_y -> V_(gy)
~~~

be unitary and satisfy

~~~text
c(gh,y)=c(g,hy)c(h,y).                                  (1)
~~~

Fix §o in Y§.  For every §y§ choose §a_y in K§ with
§a_y o=y§ and §a_o=1§.  Use §c(a_y,o)§ to identify
§V_o§ with §V_y§.  In these coordinates the chosen arrows are identities.
For an arbitrary arrow §g:y->gy§ put

~~~text
h(g,y)=a_(gy)^(-1) g a_y in H:=Stab_K(o).               (2)
~~~

Repeated use of (1) shows that the coordinate matrix of §c(g,y)§ is

~~~text
rho(h(g,y)),             rho(h)=c(h,o).                 (3)
~~~

Equation (1) says exactly that §rho:H->U(V_o)§ is a representation.
A different family of identifications conjugates §rho§ and applies a
block-diagonal gauge to §c§.

If §c§ is monomial in point bases of the fibers, its restriction to the root
is a monomial representation of §H§.  Conversely, a monomial basis for
§rho§, transported to every §V_y§ by the chosen arrows, makes every matrix
in (3) monomial.  Thus

~~~text
c is gauge-monomial iff rho is monomial.                 (4)
~~~

For a nontransitive action this argument applies independently on every
orbit.  Notice that §rho§ can be arbitrarily far from the identity.  It is
not an additive cocycle in a unitary representation, so the vanishing of
Hilbert-space first cohomology supplied by property (T) does not apply.
Linearizing by a logarithm would require a prior small-norm hypothesis and
therefore cannot remove the exact holonomy in (3).

## 2. A uniform nonmonomial amplification criterion

Let §H§ be finite and let §rho§ be an irreducible representation of
dimension §s>1§.  Assume

~~~text
[H:L]>s^2 for every proper subgroup L<H.                 (5)
~~~

We first prove that no §rho^(direct_sum k)§ is monomial.

A monomial representation has a basis whose lines are permuted by §H§.
Split those lines into §H§-orbits.  The representation on one orbit is

~~~text
Ind_L^H(theta),                                          (6)
~~~

where §L§ stabilizes one line and §theta§ is the scalar character on that
line.  If a direct sum of such orbit representations were isotypic of type
§rho§, then each summand in (6) would itself be isotypic:

~~~text
Ind_L^H(theta) = k_L rho.                                (7)
~~~

Frobenius reciprocity gives

~~~text
k_L=dim Hom_L(Res_L(rho),theta) <=s.                     (8)
~~~

Taking dimensions in (7) yields

~~~text
[H:L]=k_L s<=s^2.                                        (9)
~~~

Condition (5) forces §L=H§.  But then (6) is one-dimensional and cannot be
isotypic of the §s§-dimensional §rho§.  This is a contradiction.

There are only finitely many transitive monomial representations (6), up to
equivalence.  Let §M_H§ be the convex hull of their normalized characters.
Every monomial representation has normalized character in §M_H§.  Moreover,

~~~text
chi_rho/s notin M_H.                                    (10)
~~~

Indeed, irreducible multiplicities are nonnegative.  If a convex combination
of normalized monomial characters equalled §chi_rho/s§, every summand with
positive coefficient would have zero multiplicity at every irreducible
other than §rho§.  Some transitive monomial representation would then be
isotypic of type §rho§, contrary to (9).

Because §M_H§ is compact, the number

~~~text
Delta=min_(z in M_H) max_(h in H)|chi_rho(h)/s-z(h)|     (11)
~~~

is positive.  Let §S§ generate §H§ and let §L_S§ be the maximum, over
§h in H§, of its word length in §S union S^(-1)§.

Set §sigma_k=rho^(direct_sum k)§, of dimension §ks§.  Allow arbitrary
padding §alpha_k§ of dimension §p_k=o(ks)§ and put
§sigma_tilde_k=sigma_k direct_sum alpha_k§.  Its normalized character
differs pointwise from §chi_rho/s§ by at most §2p_k/(ks+p_k)§.  Hence for
every monomial representation §mu_k§ of the same padded dimension there is
§h in H§ with

~~~text
|tr(sigma_tilde_k(h))-tr(mu_k(h))|
 >=Delta-2p_k/(ks+p_k).                                  (12)
~~~

Normalized trace is dominated by normalized Hilbert--Schmidt norm.  If
§Z§ is any unitary and the two exact representations are within §eta§ on
every generator, telescoping along a shortest word for §h§ gives distance
at most §L_S eta§ at §h§.  Therefore

~~~text
max_(a in S)||Z sigma_tilde_k(a) Z^*-mu_k(a)||_2
 >=(Delta-2p_k/(ks+p_k))/L_S.                            (13)
~~~

This proves the padding-stable separation in the claim.

For a concrete group, take §H=SL(2,5)§ and its natural binary-icosahedral
representation §rho:H->SU(2)§.  This representation is irreducible of
dimension two, and §H§ is perfect.  A proper subgroup of index at most four
would give a nontrivial transitive image of the perfect group §H§ in
§S_4§.  But §S_m§ has no nontrivial perfect subgroup for §m<=4§.
Consequently every proper subgroup has index at least five, so (5) holds.
The finite group §H§ has property (T).

## 3. Exact quantum fibers despite property (T)

Fix a Boolean pattern set §Y={+1,-1}^m§ and let §H§ act trivially on it.
On

~~~text
V=ell^2(Y) tensor C^(2k)
~~~

let §P_y§ be the coordinate projections and put

~~~text
U_h=I_(ell^2(Y)) tensor rho(h)^(direct_sum k).            (14)
~~~

The §P_y§ have trace §2^(-m)§.  Consequently the commuting lamp signs
§v_j=sum_y y_j P_y§ have exactly the canonical independent Bernoulli
moments.  The actor equations are exact, and

~~~text
U_h P_y U_h^*=P_y                                        (15)
~~~

gives exact lamp covariance for this finite pattern action.

Nevertheless, on each fiber the holonomy is
§rho^(direct_sum k)§.  By (13), no block gauge can make it close to a
monomial representation, even after an §o(k)§ padding of that fiber.  If a
different gauge and monomial representation are chosen independently on
each Boolean atom, (13) still gives a global obstruction: summing the
squared fiber inequalities and then maximizing over the finite set §S§
loses at most the factor §sqrt(|S|)§.

Thus property (T), exact multiplication, exact coarse covariance, and
canonical lamp moments do not spatialize the diffuse fiber.  The model does
not have the canonical actor trace: the normalized trace of §U_h§ is the
normalized character of §rho(h)§.  Nor does it have the canonical mixed
crossed-product trace.  This omission is precisely what the next step uses.

If an infinite property-(T) actor is desired, replace §H§ by
§K_0 direct_product H§ for any infinite property-(T) group §K_0§ and let
the representation factor through §H§.  The same obstruction remains.
Again, this is a limitation on property (T), not a candidate hyperlinear
model of the pinned wreath.

## 4. Canonical character regularizes a fixed finite holonomy

Let §H§ now be any fixed finite group and
§sigma:H->U(r)§ any exact representation.  Denote the irreducible
characters by §chi_pi§, their dimensions by §d_pi§, and the multiplicity of
§pi§ in §sigma§ by §m_pi§.  Put

~~~text
c(h)=tr_r(sigma(h)),       q=sum_(h!=1)|c(h)|.            (16)
~~~

Character orthogonality gives

~~~text
m_pi
 =(r/|H|)(d_pi+sum_(h!=1)c(h) conjugate(chi_pi(h))).     (17)
~~~

Using §|chi_pi(h)|<=d_pi§ and
§sum_pi d_pi^2=|H|§, we obtain

~~~text
(1/r)sum_pi d_pi |m_pi-r d_pi/|H|| <=q.                 (18)
~~~

Let

~~~text
k=floor(r/|H|),          t=r-k|H|,        0<=t<|H|,      (19)
mu=k lambda_H direct_sum 1^t.                            (20)
~~~

The multiplicity of §pi§ in §mu§ is
§n_pi=k d_pi+t 1_(pi=trivial)§.  Rounding §r/|H|§ to §k§ costs less than
§|H|/r§ in the left side of (18), and adding the §t§ trivial summands costs
another §|H|/r§.  Hence

~~~text
A:=(1/r)sum_pi d_pi |m_pi-n_pi|
 <=q+2|H|/r=:delta.                                      (21)
~~~

The largest common subrepresentation of §sigma§ and §mu§ has dimension

~~~text
R=sum_pi d_pi min(m_pi,n_pi)
 =r-(1/2)sum_pi d_pi|m_pi-n_pi|
 >=r(1-delta/2).                                         (22)
~~~

Choose a unitary §Z§ which intertwines the two representations on that
common subspace.  The two conjugated unitary matrices agree there for every
§h§.  On its orthogonal complement their difference has operator norm at
most two.  Therefore, simultaneously for every §h in H§,

~~~text
||Z sigma(h) Z^*-mu(h)||_2^2
 <=4(r-R)/r
 <=2delta,                                               (23)
~~~

and in particular the weaker clean bound §2 sqrt(delta)§ in the claim
holds.  The representation §mu§ is monomial because the regular
representation is a permutation representation.

If §H§ is fixed, §r_n->infinity§, and
§tr(sigma_n(h))->0§ for each §h!=1§, then the finite sum §q_n§ tends to
zero and (23) makes §sigma_n§ asymptotically monomial.  This conclusion
uses the whole conditional character, not property (T).

## 5. What the pinned wreath supplies, and what it does not

After the pairwise Boolean-atom spatialization theorem, consider a loop
§h§ which fixes a coarse atom §P_y§.  If the loop matrices have been
exactified to a representation on §P_y C^D§, their normalized fiber
character is

~~~text
c_y(h)=tr_D(P_y U_h)/tr_D(P_y).                          (24)
~~~

In the canonical crossed-product trace,
§tau(a u_h)=0§ for every lamp-algebra element §a§ and every nonidentity
actor §h§.  Thus (24) tends to zero for each fixed nonidentity loop in a
hyperlinear model.  On any one fixed finite exact loop group, Section 4
then rounds the entire holonomy to a monomial action.

There are two nonuniformities.  If §|c_y(h)|<=epsilon§ on a finite group
§H§, (21) only gives

~~~text
delta <=(|H|-1)epsilon+2|H|/r.                           (25)
~~~

Thus a growing family requires the uniform rates
§|H|epsilon->0§ and §|H|/r->0§.  Pointwise hyperlinear convergence gives
neither.  Moreover actor microstates are only approximately multiplicative.
Exactifying the loop data for groups whose presentations grow with the
tested actor window is a source-specific Hilbert--Schmidt stability problem;
property (T) by itself is not such a stability theorem.

The rank scale is independent and equally explicit.  In a matrix corner of
dimension §D§, a canonical atom cut out by §m§ independent lamps has

~~~text
r approximately D 2^(-m).                                (26)
~~~

Combining (25) and (26), the fixed-holonomy character argument needs

~~~text
|H|epsilon->0,          |H|2^m/D->0.                     (27)
~~~

If instead one tries to remove every internal fiber by lamp refinement
alone, requiring §r<=K§ forces

~~~text
m>=log_2(D)-log_2(K).                                    (28)
~~~

The canonical moment conditions are available only after fixing §m§ and
the finite word set.  They contain no diagonal rate at the logarithmic
scale (28), and no summable rate over the growing loop set in (27).

The result therefore removes one tempting route and opens a narrower one.
Spectral gap cannot scalarize exact holonomy.  Canonical mixed traces do
spatialize every fixed finite exact holonomy.  A genuine obstruction, or a
successful hyperlinear-to-sofic proof, must live in the joint regime of
growing loop presentations, approximate exactification, and moving lamp
windows.  No assertion here settles hyperlinearity of the Kun--Thom wreath.
