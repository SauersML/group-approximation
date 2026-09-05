# Relative projection embeddings and compact-left comparison over all bases

Status: internally reviewed on 5 September 2026. This establishes compact-left comparison
against arbitrary positive targets. It does not claim full Cu regularity for
real-rank-zero coefficient fields.

Let D be separable, simple, stably finite, pure, and real rank zero; put
B = D tensor K. The first-factor map is denoted by phi. The already proved
all-base compact theorem gives a canonical isomorphism

```text
V(C(X,D)) -> V(C(X,D tensor Z))
```

for every compact metrizable X. The new conclusion is stronger:

**Theorem.** For every compact metrizable X, every projection
p in C(X,B), and every positive b in C(X,B),

```text
phi(p) <=_Cu phi(b)  implies  p <=_Cu b.
```

Thus the actual first-factor map reflects every order relation whose left
side is compact, even when the right side is noncompact and has mixed
compact and soft restrictions. There is no bound on dim X in this theorem.

The proof first proves an exact relative embedding statement in finite
dimension, then uses continuity to remove the dimension bound from the
compact-left conclusion.

## 1. The precise topological input

Michael's finite-dimensional selection theorem says: if X is paracompact
with dim X <= n+1, Y is completely metrizable, and F is an equi-LC^n family
of nonempty closed C^n subsets of Y, then every lower semicontinuous map
X -> F has a continuous selection. Here C^n means that every sphere map
of dimension at most n extends over its ball. Equi-LC^n means that the
local extension neighborhoods can be chosen uniformly over members of F.

The original source is E. Michael, *Continuous selections II*, Annals of
Mathematics 64 (1956), 562--580, Theorem 1.2. An accessible primary source
giving a self-contained proof is V. Gutev, *Constructing selections
stepwise over skeletons of nerves of covers*, Serdica Math. J. 44 (2018),
137--154, Theorem 1.1:

<https://www.math.bas.bg/serdica/2018/2018-137-154.pdf>.

We verify all the selection hypotheses below. In particular, fiberwise
weak contractibility is not used as a substitute for equi-local
connectivity or lower semicontinuity.

## 2. Proper coefficient Stiefel spaces

For projections 0<r<q in B, the norm-topological space

```text
Emb(r,q) = {v in qBr : v*v=r}
```

is weakly contractible. Indeed, U(qBq) acts transitively, because stable
rank one gives cancellation of the complementary projections. Its
stabilizer at r is U((q-r)B(q-r)), embedded by u -> r+u.

This quotient is a locally trivial principal bundle. A local section
near r can be obtained by first conjugating the nearby range projection
to r by the polar-decomposition unitary for close projections, and then
correcting the resulting unitary in rBr. The same construction works
near any embedding after translation by a unitary.

Both corner unitary groups are K-stable by Zhang's Theorem II for
non-elementary simple real-rank-zero stable-rank-one algebras. The map
on their stabilized homotopy groups is induced by the full-corner
inclusion, hence is an isomorphism. Their stabilization squares and the
homotopy exact sequence of the principal bundle prove the assertion,
including path connectedness. Stable rank one here follows from Lin's
theorem for simple finite pure algebras, and also passes to the corners.

Zhang's source and its exact use are audited in
`stw99-lxxvi-all-base-compact-k-stability-audit-2026-09-05.md`:

<https://jot.theta.ro/jot/archive/1991-026-002/1991-026-002-004.pdf>.

The strict inequality r<q is essential. When r=q, the space is U(qBq),
which retains coefficient K-theory.

## 3. Embedding spaces into arbitrary hereditary modules

For c in B_+ and a projection e in B, define

```text
E(e,c) = {v in closure(cB) : v*v=e}.
```

The right ideal closure(cB), not the hereditary algebra Her(c), is the
correct ambient module: the initial projection e need not belong to
Her(c). The space E(e,c) is norm closed in the Banach space B. Its
members have norm one when e is nonzero. The condition v in closure(cB)
implies vv* in Her(c).

If [e]<[c] in Cu(D), then E(e,c) is nonempty and weakly contractible.
The case e=0 is the singleton {0}. For nonzero e, projection comparison
gives nonemptiness. Choose an increasing projection approximate unit
(q_j) of Her(c), using real rank zero. Then [c]=sup_j [q_j]. Since [e]
is compact and [e]<[c], eventually [e]<[q_j].
Indeed, once [e]<=[q_j], if all subsequent classes were equal to [e],
their supremum would be [e], contradicting [e]<[c].

Given a continuous sphere map v:S^k -> E(e,c), compactness of its image
gives uniform convergence q_j v -> v. For large j the expression

```text
v_j = q_j v (v* q_j v)^(-1/2)
```

is defined, with the inverse square root taken in the unital corner eBe.
It is uniformly close to v and lies in E(e,q_j). Normalizing the straight
line between v and v_j gives a homotopy inside E(e,c). Choose j also so
that [q_j]>[e]. Fixing one embedding of e into q_j identifies E(e,q_j)
with a proper Stiefel space from Section 2. Hence v_j, and therefore v,
is null-homotopic. This works also for k=0.

## 4. A uniform local contraction independent of the hereditary algebra

Suppose v,w belong to one E(e,c) and are sufficiently close. For
0<=t<=1 put z_t=(1-t)v+tw and define

```text
H_t(v,w) = z_t (z_t* z_t)^(-1/2).
```

This remains in closure(cB), has initial projection e, and continuously
joins v to w. If ||v-w||<=delta, then

```text
||z_t* z_t-e|| <= 2 delta+delta^2.
```

Functional calculus consequently gives a bound
||H_t(v,w)-v|| <= C delta for small delta, with a universal C independent
of e, c, and B. For example, C=10 is sufficient for delta<1/8.

Given a sphere map contained in a delta-ball of an ambient point, choose
one image point as the center for this contraction. All its image points
are within 2 delta of that center. The formula extends the sphere over
its cone inside a universally controlled larger ball. It follows that
the family of all nonempty E(e,c), allowing e and c to vary, is equi-LC^n
for every finite n. Adjoining arbitrary singleton sets preserves this
property. This is the uniformity required by Michael's theorem.

## 5. Lower semicontinuity for moving positive sections

Let p:X -> B be a norm-continuous projection and b:X -> B_+ a
norm-continuous positive section. Assume [p(x)]<=[b(x)] for all x. Then

```text
x |-> E(p(x),b(x))
```

is a lower semicontinuous closed-valued map into B.

To check this, fix x_0 and v_0 in E(p(x_0),b(x_0)). Approximate v_0
arbitrarily closely by b(x_0) d p(x_0), for one fixed d in B. On a
neighborhood of x_0, set w(x)=b(x)d p(x). When the approximation and
neighborhood are sufficiently small, w(x)*w(x) is invertible in
p(x)Bp(x). Polar normalization

```text
w(x) (w(x)*w(x))^(-1/2)
```

then gives a local continuous selection as close to v_0 as desired.
The inverse varies continuously with the projection corner: equivalently
use w*w+1-p in the unitization. If p(x_0)=0, p vanishes on a neighborhood
and the zero selection works. This proves lower semicontinuity in the
fixed complete ambient space B.

## 6. Exact relative projection-into-positive embedding

**Relative lemma.** Let X be finite-dimensional compact metrizable, let
Y be closed in X, and let p,b be as in Section 5. Suppose

```text
[p(x)] < [b(x)] for every x outside Y with p(x) nonzero,
```

and suppose a norm-continuous v_Y:Y -> B is given with

```text
v_Y(x)*v_Y(x)=p(x),   v_Y(x) in closure(b(x)B).
```

Then v_Y extends to a norm-continuous v:X -> B with the same two
properties at every point. In particular, p <=_Cu b.

Proof: replace the embedding-space fiber over Y by {v_Y(x)}. This
modified multifunction is still lower semicontinuous. At a point of Y,
combine the lower semicontinuity from Section 5 with continuity of v_Y
along Y. Outside Y use that Y is closed. All values are closed and
nonempty. They are C^n for every n by Section 3, or are singletons, and
the whole family is equi-LC^n by Section 4. Michael's theorem gives the
required selection.

Finally vv* belongs to Her(b) globally, not just pointwise. Indeed,
pointwise membership vv*(x) in Her(b(x)) gives pointwise convergence
f_m(b(x))vv*(x) -> vv*(x), where (f_m(b)) is a usual increasing
functional-calculus approximate unit. The nonnegative continuous
functions ||(1-f_m(b(x)))v(x)|| decrease to zero, and hence converge
uniformly on compact X by Dini's theorem. Thus v belongs to
closure(b C(X,B)), and vv* belongs to Her(b). This verifies the claimed
global Cuntz comparison.

## 7. The compact equality locus is closed and has a spectral gap

Assume [p(x)]<=[b(x)] for all x and restrict to the clopen set where p
is nonzero. Set

```text
Y = {x : [p(x)]=[b(x)]}.
```

The complement of Y is open. At a point x_0 with strict inequality,
real rank zero and compactness of [p(x_0)] give a projection q in
Her(b(x_0)) with

```text
[p(x_0)] < [q] <= [b(x_0)].
```

For some epsilon>0, q <=_Cu (b(x_0)-epsilon)_+. Norm continuity of b
makes q <=_Cu b(x) near x_0. The class of p(x) is locally constant, so
[p(x)]<[b(x)] there.

For each y in Y, the actual positive operator b(y) has a spectral gap
at zero. Here the precise input is Brown--Ciuperca, *Isomorphism of
Hilbert modules over stably finite C*-algebras*, Theorem 3.5:
in a stable finite C*-algebra, compactness of the Cu class of a positive
element implies that its spectrum is contained in
`{0} union [epsilon,infinity)` for some epsilon>0. This applies to
B=D tensor K, which is stable and finite. The source is
<https://arxiv.org/abs/0811.0958>.

These pointwise gaps are locally uniform on Y. Fix y_0, and choose a
small positive threshold lying below the positive spectrum of b(y_0).
For nearby y the high spectral projection q(y) is continuous and has
the same class as the support projection of b(y_0), hence as p(y).
To choose q(y), take a smaller interval inside the spectral gap at y_0;
norm persistence of that interval gap defines one continuous spectral
cut on a neighborhood of y_0.
For y in Y, its inclusion in the support r(y) of b(y), together with
[q(y)]=[p(y)]=[r(y)], forces q(y)=r(y): r(y) is finite. Thus there is no
additional spectrum below the threshold at those y. A finite cover of
compact Y gives one uniform spectral gap for b|Y. Consequently b|Y has
a continuous support projection r in C(Y,B), and [b|Y]=[r] is compact.

This argument explicitly uses actual operator spectral gaps in finite
fibers; it does not infer a spectral gap from compact Cu classes in an
arbitrary C*-algebra.

## 8. Compact-left comparison reflection in finite dimension

Suppose phi(p)<=_Cu phi(b). The coefficient-level Cu isomorphism gives
[p(x)]<=[b(x)] at every point. Let Y and r be as in Section 7. On Y,
phi(p|Y)<=_Cu phi(r), so phi(p|Y) is Murray--von Neumann equivalent to
a subprojection of phi(r). At every fiber these projections already
have the same finite projection class. The complementary projection
therefore has zero value at every point and is zero. Thus

```text
phi(p|Y) ~ phi(r).
```

The all-base compact theorem, applied to the compact space Y, implies
p|Y ~ r. Choose the corresponding actual continuous partial isometry
v_Y, with initial projection p|Y and range r. Section 6 extends it
across X, since the coefficient comparison is strict off Y. This proves
p<=_Cu b. On the clopen region where p=0 the conclusion is automatic.

## 9. Removing the dimension bound from compact-left comparison

Write any compact metrizable X as an inverse limit of finite polyhedra
X_i. Then C(X,D) and C(X,D tensor Z) are the corresponding inductive
limits, and the first-factor maps commute with their connecting maps.

We use the following elementary consequence of Cu continuity. In a
commuting sequence of Cu morphisms f_i:S_i -> T_i, suppose every f_i
reflects comparisons c<=s with c compact. Suppose additionally that
every compact element of the source limit lifts to a compact element
at some stage. Then the induced limit map has the same compact-left
reflection property.

Indeed, lift the compact c to a compact c_i. Express an arbitrary s in
the source limit as a supremum of the usual stage representatives from
Cu continuity. Since f(c) is compact, f(c)<=f(s) implies f(c)<=f(s_j)
for one such representative. The comparison-lifting clause of Cu
continuity, applied to f_i(c_i)<<f_i(c_i), realizes this comparison at
a common later stage. Reflect it there, then pass to the limit.

In the present C*-algebra systems, compact classes are projection
classes because the algebras are stably finite. Projections lift to a
finite stage up to equivalence by stability of the projection relations.
Thus the extra lifting hypothesis holds. Section 8 applies at every
finite-polyhedron stage. This proves the stated theorem for arbitrary
compact metrizable X.

## Scope and the remaining full-Cu task

This proof resolves the uniform moving-target problem when the source
is a projection. It controls the actual map on compact classes and
every compact-left order comparison, in every compact base dimension.
The pre-existing full-soft theorem controls all functionally soft
classes and their mutual comparison.

An arbitrary positive source need not be a supremum of global
projections: C([0,1],D) need not have real rank zero. Consequently the
new compact-left result does not automatically prove reflection for
arbitrary mixed source classes or realization of arbitrary mixed target
classes. Those are still required for full LXXVI in this coefficient
class. No such conclusion is asserted here.

## Independent internal review and graph validation

The root reviewer checked the full argument, including the precise
statements of Gutev's Theorem 1.1 and Brown--Ciuperca's Theorem 3.5 in
the primary papers linked above. The review checked varying initial
projections in the fixed Banach-space selection problem, the singleton
replacement on the closed boundary, uniform local connectivity, the
locally uniform spectral gap on the equality locus, and compact-left
comparison lifting through the Cu inductive limit. No unresolved gap
was found. This is an internal mathematical review, not external peer
review or formal proof-kernel verification.

The actual Cairn CLI commands `check --changed` and `preview` passed on
MSI for the relevant dependency closure, including the new claim and
route and the updated LXI documentation: 22 claims and 21 routes.
The compact-left claim derives `ESTABLISHED`; the LXXVI and LXI roots
remain open. These checks validate graph structure, not mathematics.
Logs are `relative-check.log` and `relative-preview.log` in
`/projects/standard/hsiehph/sauer354/stw79-cairn-check-20260904/cu-all-base-scope-20260905`.
