# Cuntz comparison from fibers and compact equality strata

Date: 5 September 2026. Complete proof independently reviewed internally
by two agents, conditional on the reviewed exact relative-embedding input.
No external verification or publication-priority claim is made.
This is a comparison theorem, not a range theorem for arbitrary prescribed
fiber and bundle data.

## 1. The theorem

Let D be separable, simple, stably finite, pure, and real rank zero.
Let X be second-countable locally compact Hausdorff with finite covering
dimension, and put B=D tensor K. For a,b in C0(X,B)_+, assume first the
fiberwise inequalities [a(x)]<=[b(x)]. For a nonzero projection class
v in V(D), define the equality stratum

    S_v = {x : [a(x)]=v=[b(x)]}.

At each point of S_v, both positive elements have support projections.
Their supports are continuous on S_v; write them r_a and r_b.

**Theorem.** The global comparison [a]<=[b] holds if and only if:

1. [a(x)]<=[b(x)] for every x in X; and
2. for every nonzero v in V(D) and every compact subset K of S_v,
   the projections r_a|K and r_b|K are Murray--von Neumann equivalent
   in C(K,B).

In the second condition the equivalence is over the same base K.
It is not merely equality of their fiber classes. Equivalence on each
compact subset is the compact-restriction convention for V_c; a single
equivalence over all of a noncompact stratum is not required.

Consequently two positive sections have the same global Cu class
exactly when their fiber classes agree everywhere and their support
bundles agree on every compact subset of each compact-value stratum.
This determines the order on actual classes. It does not assert that
arbitrary compatible-looking data are realized by a positive section.

The shape of the criterion is prior art: Tikuisis's Theorem 4.1 proves
it for simple unital Z-stable ASH coefficients over arbitrary
second-countable locally compact bases. Here the coefficient may be
nonnuclear and nonunital, with real rank zero and pureness; the base
has finite dimension. The proof below uses the already established
strict-relative embedding theorem, rather than an ASH presentation.

## 2. Inputs and the support continuity check

We use the internally reviewed
[exact strict-relative embedding theorem](stw99-lxxvi-rr0-cutoff-relative-selection-audit-2026-09-05.md):
over finite-dimensional compact metric T, if positive contractions c,d
satisfy [c(t)]<=[d(t)] everywhere and strict inequality off a closed Y
whenever c(t) is nonzero, any continuous boundary vector z_Y with
z_Y*z_Y=c|Y and range in the target hereditary module extends exactly
over T. Its proof verifies the hypotheses of Michael's finite-dimensional
selection theorem. The root rechecked that primary theorem and the
strict-only selection hypotheses for this argument.

We also use the stable-finite compact-class criterion: for h in B_+,
[h] is compact if and only if h has a spectral gap at zero, in which
case its support is a projection in B. This is Brown--Ciuperca,
Theorem 3.5, also stated as Proposition 2.7 in Tikuisis's paper.

Here is the continuity consequence needed for the theorem. Suppose
h is a continuous positive field on a space T and all its fiber
classes equal one fixed finite projection class v. At t0, choose a
spectral gap for h(t0). On a neighborhood, a smaller interval remains
a spectral gap and its upper spectral projection q(t) is continuous.
The projection q(t) is equivalent to supp(h(t0)) after shrinking the
neighborhood. For each t there, q(t)<=supp(h(t)), and both have class
v. Finiteness forces equality. Thus supp(h(t))=q(t) locally, so the
support is continuous. On compact T these local gaps give one uniform
gap. Apply this separately to a and b on S_v.

The strata S_v are locally closed. Indeed, compactness of v makes
{x:v<=[a(x)]} open. Also {x:v<[b(x)]} is open: at a strict point,
projection approximation of Her(b(x)) gives a projection class w
with v<w<=[b(x)]; a fixed positive cutoff witnesses w<=[b(y)] nearby.
Under fiberwise comparison,

    S_v = {x:v<=[a(x)]} minus {x:v<[b(x)]}.

This also verifies that the usual locally compact stratum notation
is legitimate. The proof below only needs compact subsets of them.

## 3. Necessity

Global comparison restricts to every compact K. On K contained in S_v,
support continuity and the compact-class criterion identify [a|K]
and [b|K] with their support projections. Projection comparison gives
a partial isometry from r_a|K onto a subprojection of r_b|K.
At each point its range and r_b have the same finite projection
class v, so the range equals r_b pointwise. The continuous projections
therefore agree globally. This is the required bundle equivalence.

## 4. The closed core of a cutoff

For sufficiency, rescale a,b to contractions, which does not change
their Cu classes. Fix 0<eta<1, and put

    c=(a-eta)_+,
    E_eta={x : [c(x)]=[b(x)] is nonzero},
    K_eta=closure(E_eta) in X.

At x in E_eta we have

    [c(x)] <= [a(x)] <= [b(x)] = [c(x)].

The common class is compact because [(a(x)-eta)_+]<<[a(x)].
Let q_x and r_x be the supports of c(x) and a(x). They are finite
projections with q_x<=r_x and equal Cu classes. Hence q_x=r_x, so

    spec(a(x)) is contained in {0} union (eta,infinity),
    ||a(x)||>eta.

Spectral continuity at limits gives, for every y in K_eta,

    spec(a(y)) is contained in {0} union [eta,infinity),
    ||a(y)||>=eta.

The set K_eta is compact: it is closed and is contained in the
compact set {x:||a(x)||>=eta}, since a vanishes at infinity.
Functional calculus gives the continuous support projection

    r=supp(a|K_eta) in C(K_eta,B).

Fiberwise equality [a(y)]=[b(y)] persists on K_eta. For a fixed y
and delta>0 choose x in E_eta so near y that b(x) is delta-close
to b(y) and r(x) is norm-distance less than one from r(y). Then

    [(b(y)-delta)_+] <= [b(x)] = [r(x)] = [r(y)].

Take the supremum over delta. Together with [a(y)]<=[b(y)], this
proves equality. This is the same closed-core calculation as in the
[full order-reflection proof](stw99-lxxvi-rr0-full-order-reflection-audit-2026-09-05.md),
now used without a first-factor comparison as a hypothesis.

## 5. Recover the boundary from the stated invariant

The class of the continuous projection r is locally constant on
K_eta: norm-close projections are equivalent. Compactness implies
that only finitely many classes v_1,...,v_l occur. Their level sets
K_1,...,K_l form a finite clopen partition of K_eta, and each K_j
is a compact subset of S_(v_j).

Condition 2 and the support continuity check therefore give partial
isometries t_j on K_j with

    t_j*t_j=r|K_j,
    t_j t_j*=supp(b|K_j).

Their union is a continuous t on K_eta. It supplies the exact
boundary vector

    z_K=t(c|K_eta)^(1/2),
    z_K*z_K=c|K_eta,
    z_K(y) in closure(b(y)B).

Off K_eta every nonzero c(x) has class strictly below [b(x)]:
otherwise x would belong to E_eta. This is precisely the strictness
required by the relative theorem. No projection data outside the
equality strata have been assumed.

## 6. Compact extension and vanishing at infinity

If X is compact, apply the strict-relative embedding theorem with
boundary K_eta. The resulting z satisfies z*z=c and zz* in Her(b),
so c<=_Cu b. The empty-core case uses the theorem with empty boundary.

For noncompact X, choose a compact neighborhood L of
{x:||a(x)||>=eta/2}, with that set contained in int(L). Such L exists
by local compactness and a finite cover of this compact set. Its
dimension is at most dim(X). The two closed subsets K_eta and the
boundary of L are disjoint. Prescribe z_K on the first and zero on
the second; this is continuous boundary data, with initial positive
c on both. Apply the compact strict-relative theorem on L.

Extend the resulting vector by zero off L. It is norm continuous
because its restriction to the boundary is zero, and has compact
support. Outside L the source cutoff c is zero. Thus globally
z*z=c and z(x) lies in the hereditary module of b(x).
Functional-calculus approximate units for b converge uniformly on
z over the compact support by Dini's theorem. Hence z belongs to
closure(b C0(X,B)), and zz* belongs to Her(b) globally. We have
(a-eta)_+<=_Cu b in C0(X,B).

Taking all eta proves a<=_Cu b. Applying this in both directions
gives the stated criterion for equality of actual Cu classes.

## 7. What remains for realization

This theorem separates the order problem from the range problem.
For first-factor surjectivity, one still has to construct a source
positive with the target fiber classes and with the required compact
restriction bundles. The theorem then identifies its image with the
target. It does not construct such a positive or assert that an
arbitrary system of bundles on overlapping strata is compatible.

In particular, it does not remove the strict-collar issue identified
after the closed-compact-stratum result: a neighborhood projection can
keep the entire compact target class just outside a cutoff core and
therefore fail to embed into the target's soft predecessor.

## Sources

- A. Tikuisis, *The Cuntz semigroup of continuous functions into certain
  simple C*-algebras*, Theorem 4.1, Propositions 2.7 and 3.3:
  [primary manuscript](https://arxiv.org/pdf/1007.2927).
- L. G. Brown and A. Ciuperca, *Isomorphism of Hilbert modules over
  stably finite C*-algebras*, Theorem 3.5:
  [primary manuscript](https://arxiv.org/abs/0811.0958).
- V. Gutev, *Constructing selections stepwise over skeletons of nerves
  of covers*, Theorem 1.1:
  [primary paper](https://www.math.bas.bg/serdica/2018/2018-137-154.pdf).
- The exact-relative theorem and its coefficient inputs are proved
  in the linked internal artifact; they remain internally reviewed
  mathematics, not a formal proof-kernel certificate.
