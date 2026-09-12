# Hereditary sandwiches and full target realization for real-rank-zero fields

Status: internally reviewed on 5 September 2026; no unresolved gap found.
External verification and publication priority are not asserted.
The proof uses the previously reviewed
strict-relative embedding theorem and the new compact-equality-strata
comparison theorem. Every global comparison below explicitly invokes
the latter with its projection-bundle condition verified.

## 1. Statement

Let D be separable, simple, stably finite, pure, and real rank zero.
Put B=D tensor K, T=(D tensor Z) tensor K, and let phi:B->T denote
first-factor inclusion. For every second-countable locally compact
Hausdorff space X, the theorem is

```text
Cu(C_0(X,D)) --Cu(id tensor 1_Z)--> Cu(C_0(X,D tensor Z))
is an isomorphism.                                      (1.1)
```

The main construction has a finite-dimensional compact base. For every
positive contraction b in C(X,T) and every epsilon>0, it produces a
positive a in C(X,B) with the actual global inequalities

```text
[(b-epsilon)_+] <= phi[a] <= [b].                        (1.2)
```

This is the hereditary sandwich needed for surjectivity. Unlike the
closed-compact-stratum theorem, it imposes no condition on how compact
fiber classes accumulate. The construction does not add independent
projection patches orthogonally; it arranges their ranges inside a
largest active hereditary module.

The general STW LXXVI problem for arbitrary pure algebras is not the
statement of (1.1).

## 2. Inputs and coefficient facts

The internal inputs are:

1. `stw99-lxxvi-rr0-cutoff-relative-selection-audit-2026-09-05.md`:
   exact relative positive-source embeddings when fiberwise comparison
   is strict off the prescribed closed boundary.
2. `stw99-lxxvi-compact-equality-strata-comparison-2026-09-05.md`:
   for finite-dimensional compact X, global comparison is equivalent
   to fiberwise comparison and equivalence of the support bundles on
   every compact subset of every equal nonzero compact-value stratum.
3. `stw99-lxxvi-all-base-compact-k-stability-audit-2026-09-05.md`:
   actual first-factor V isomorphism over every compact metric base.
4. `stw99-lxxvi-rr0-full-order-reflection-audit-2026-09-05.md`:
   the actual first-factor Cu map is an order embedding.

The coefficient first-factor Cu map is an isomorphism. Also T has real
rank zero, as proved using algebraic Cu and the stable-rank-one criterion
in `stw99-lxxvi-rr0-finite-projection-patch-realization-2026-09-05.md`.
Thus the strict embedding and comparison inputs apply to both B and T.
We identify the two coefficient Cu semigroups through their specified
isomorphism and call the common semigroup S.

Here are the hypotheses behind the primary coefficient results. The
zero coefficient gives a trivial theorem, so assume D is nonzero.
It is nonelementary: an elementary simple coefficient is Morita
equivalent to the scalars, whose Cu semigroup is not almost divisible
(the compact class 1 cannot satisfy 2x<=1<=3x). Stable rank one of
the simple finite pure coefficient, and hence of its stabilization,
gives weak cancellation in S. Simplicity, stable finiteness, (O5),
and (O6) also hold for this coefficient Cu semigroup. Thus the
maximum-of-proper-subclasses conclusion of APT Proposition 5.4.4
applies; it is not inferred merely from equality of functional ranks.

The following coefficient facts will be used. They concern the simple
coefficients, not the section algebras.

- Stable rank one implies Riesz interpolation in S, by Theorem 3.5
  of Antoine--Perera--Robert--Thiel,
  [*C*-algebras of stable rank one and their Cuntz semigroups*](https://arxiv.org/pdf/1809.03984).
  Repeated interpolation handles any finite lists of lower and upper
  bounds.
- Real rank zero makes S algebraic: every element is an increasing
  supremum of projection classes. Consequently finitely many elements
  way below s have a common compact upper bound at most s.
- Every element of S is compact or soft. A nonzero compact class is
  not soft. For a nonzero compact t, its soft predecessor sigma(t)
  is the largest class strictly below t. The operation sigma fixes
  soft elements and is order preserving. Also if r<<s and s is soft,
  there is soft v with r<=v<<s. These are the simple finite case of
  Proposition 5.3.16, Proposition 5.4.4, Proposition 7.3.16, Remark
  7.3.17, and Proposition 7.3.18 of Antoine--Perera--Thiel,
  [*Tensor products and regularity properties of Cuntz semigroups*](https://arxiv.org/pdf/1410.0483).

All labels used below are bounded above by a projection class. Such
a label is strictly below the class omega of the infinite standard
module B. Indeed, omega dominating two copies of a bounding projection
rules out equality by stable finiteness. This strict upper bound will
allow a final extension of each frame through the standard module.

## 3. Neighborhood bundles respecting both ends of a spectral sandwich

Fix 0<delta<epsilon and put

```text
l=(b-epsilon)_+,       d=(b-delta)_+,
f(x)=[d(x)] in S.
```

For every nonzero compact p in S, set

```text
O_p={x:p<=f(x)},       Y_p={x:f(x)=p}.
```

O_p is open. The set {x:p<f(x)} is also open: at a strict point,
real rank zero in Her(d(x)) supplies a compact q with p<q<=f(x),
and q<=f(y) persists nearby. Hence Y_p is closed in O_p.

On Y_p the support Q_p=supp(d|Y_p) is continuous. To see this locally,
choose a spectral gap at one point. Its upper spectral projection
continues nearby and has class p; it lies under the full support,
which also has the finite class p on Y_p. Finiteness makes the two
projections equal.

Extend Q_p to a continuous projection, still denoted P_p, on an open
neighborhood U_p of Y_p inside O_p. This uses a bounded selfadjoint
Banach-valued extension from the closed subset Y_p of O_p, followed
by spectral cutoff near {0,1}. Shrink U_p so the projection class is
p everywhere.

We can shrink U_p further so that

```text
[l(x)] <= [P_p(x)] <= [d(x)]                    on U_p,   (3.1)
```

and, on either of the indicated endpoint strata,

```text
||supp(l(x))-P_p(x)|| < 1/2     if [l(x)]=p,
||supp(b(x))-P_p(x)|| < 1/2     if [b(x)]=p.               (3.2)
```

Here is the simultaneous verification. At y in Y_p, d(y) has a gap
at zero, so choose t_y strictly between delta and epsilon such that
spec(b(y)) avoids (delta,t_y]. Spectral values at or below delta
are allowed. Then

```text
R_y(x)=1_(t_y,infinity)(b(x))
```

is a continuous projection near y, with R_y(y)=Q_p(y). Shrink that
neighborhood until ||R_y(x)-P_p(x)||<1/2. Functional calculus gives

```text
supp(l(x)) <= R_y(x) <= supp(d(x)) <= supp(b(x)).
```

The first and last supports may initially be bidual projections;
these containments suffice for (3.1). If [l(x)]=p, its support is an
actual finite projection, contained in R_y(x), with the same class
p, so it equals R_y(x). The same argument, with containment reversed,
gives supp(b(x))=R_y(x) if [b(x)]=p. This proves (3.2). Take the union
of these shrunken neighborhoods. The norm estimate is uniform on that
union even though different neighborhoods may use different t_y.

In particular (3.2) gives global polar partial isometries on compact
subsets of either endpoint stratum. We have retained the bundle, not
only its fiber class. No single threshold t_y over all of Y_p is
required. For p=0 use the zero projection on {x:||b(x)||<epsilon};
this covers every zero fiber of d and satisfies (3.1).

## 4. A finite cover by compact bundle labels and bounded soft labels

The neighborhoods U_p cover all points where f(x) is compact.
If f(y) is noncompact, it is soft. Choose gamma with
delta<gamma<epsilon. Soft approximation in S gives a soft s with

```text
[(b(y)-gamma)_+] <= s << f(y).
```

Choose s bounded by a projection, using algebraicity and s<<f(y).
After shrinking a neighborhood V of y, we have

```text
[l(x)] <= s << f(x)                         for x in V.  (4.1)
```

Indeed the right inequality is open by lower semicontinuity with
respect to <<. The left follows from norm perturbation and the fixed
gap epsilon-gamma. This works also when the lower cutoff at y is
zero; the zero label alone can be used on an open zero-cutoff region.

Compactness of X gives a finite subcover by such sets. Consolidate
repeated labels: repeated compact p sets are all subsets of the
single neighborhood U_p with its single bundle P_p; repeated soft
labels have a fixed coefficient representative. Denote the resulting
distinct labels by the finite set L, and their open sets by V_r,
r in L. Each label is bounded by a projection, and

```text
[l(x)] <= r << f(x)                 whenever x in V_r.   (4.2)
```

For compact r, the second relation follows from r<=f(x). Take a
partition of unity (g_r) subordinate to this finite cover, with
supp(g_r) compactly contained in V_r.

## 5. Monotone soft interpolants for finite antichains

This section produces values for all faces of a barycentric
subdivision. It explicitly handles incomparable coefficient classes.
For an antichain A contained in L and another antichain C, write

```text
A preceq C  iff  every r in A is <= some s in C.
```

This is a partial order on antichains. For a nonempty subset J of L,
write max(J) for its maximal elements and

```text
K_J = intersection_(r in J) supp(g_r).
R_A = union_{nonempty J subset L: A preceq max(J)} K_J.
```

All these sets are compact. Also A preceq C implies R_C subset R_A.
We construct labels s_A with

```text
s_{empty}=0,       s_{ {r} }=r,
s_A <= s_C                         if A preceq C,
s_A << f(x)                        for x in R_A,         (5.1)
s_A soft                           if |A|>=2.
```

They are all bounded above by a projection class. For singletons,
the assertion on R_{ {r} } follows from (4.2) and r<=some active
label at every point of that set.

Process antichains with at least two elements in a linear extension
of preceq. In addition maintain s_A<=r for every original r in L
such that A preceq {r}. At the step for A, take as lower bounds all
previous s_C with C preceq A and C unequal to A, together with all
original singleton labels whose singleton is preceq A. These include every
member of A. Each lower bound is way below f(x) for x in R_A.

At each such x choose, by algebraicity, a compact q_x which dominates
all these finitely many lower bounds and satisfies q_x<=f(x).
The open sets {y:q_x<=f(y)} cover R_A; choose finitely many q_x from
this cover. As further upper bounds include every original r with
A preceq {r}. Every lower bound is below every upper bound: for the
original upper bounds this is the additional induction invariant.

Finite Riesz interpolation supplies t between these lower and upper
bounds. If R_A is empty, replace the absent list of q_x by one
projection class dominating all lower bounds. Such a projection
exists since every earlier label is projection-bounded. In both
cases t is projection-bounded; in the nonempty case it satisfies
t<<f(x) on R_A.

If t is soft, set s_A=t. If t is compact, set s_A=sigma(t). This
replacement retains every lower bound. Soft lower bounds are fixed
by sigma. A compact lower bound must be an original label r with
{r} preceq A, and it is strictly below t: if r=t, every a in A
satisfies a<=r, while r<=a_0 for some a_0 in A, forcing a_0 to
dominate the whole antichain A, contrary to |A|>=2. Thus the
predecessor property gives r<=sigma(t). All upper bounds and the
way-below bounds on R_A remain valid after replacement.

This proves (5.1), including the comparisons with original singleton
upper bounds that may appear later in the partial order. No ordering
of incomparable labels has been treated as a Cu comparison.

For any nonempty subset J set h_J=s_max(J). Then

```text
J subset J'  implies  h_J<=h_J',
[l(x)] <= h_J << f(x)                     for x in K_J.  (5.2)
```

The only nonzero compact values h_J are original compact labels p.
If h_J=p is compact, max(J)={p}, hence p belongs to J and K_J lies
in V_p. This is the property that preserves the original bundle data.

## 6. Closed patch supports with comparable active labels

Regard g=(g_r) as a continuous map X into the finite simplex on L.
Use its barycentric subdivision. Its vertices are indexed by nonempty
subsets J of L; let lambda_J be the continuous barycentric coordinate
of the vertex J, pulled back to X. These coordinates satisfy

```text
sum_J lambda_J=1,
lambda_J(x)>0 implies x in K_J,
{J:lambda_J(x)>0} is a chain under inclusion.             (6.1)
```

The second assertion follows also from the original simplex
coordinates: g_r(x)>=lambda_J(x)/|J| for every r in J.

Let N be the number of vertices and fix 0<eta<1/N. Define

```text
psi_J=(lambda_J-eta)_+,
F_J={x:lambda_J(x)>=eta}.
```

The F_J are compact, and their interiors where psi_J>0 cover X.
If F_J and F_J' intersect, both coordinates there are positive, so
J and J' are comparable. Thus h_J and h_J' are comparable.

Group equal values: for each distinct value v among the h_J put

```text
F_v=union_{h_J=v} F_J,
psi_v=sum_{h_J=v} psi_J.
```

If F_v meets F_w, the two values are comparable. Order the distinct
values by a linear extension of their partial order. On any overlap
of distinct labels v_i,v_j with i<j we then have v_i<v_j.

If v=p is nonzero compact, F_p is a compact subset of U_p. Lift the
actual target projection P_p|F_p to a source projection A_p in
C(F_p,B), with phi(A_p) Murray--von Neumann equivalent to P_p|F_p.
This is precisely the all-base compact first-factor theorem. For a
soft v choose a fixed positive contraction A_v in B with [A_v]=v;
on F_v it is a constant section. For the zero value use A_0=0.

## 7. Exact hereditary gluing on the finite closed cover

We prove the closed-cover gluing needed here directly. Write F_i,
A_i,v_i for the data in the preceding ordering. We construct
continuous vectors z_i on F_i such that

```text
z_i*z_i=A_i,
z_i z_i* in Her(z_j z_j*) on F_i intersect F_j if i<j.   (7.1)
```

The zero-label vector is zero. Proceed downwards through the other
indices. Suppose the vectors at indices larger than i are already
defined. Construct z_i first on F_i intersect F_(i+1), then extend
successively to include F_i intersect F_(i+2), and so forth. At the
step for j the new compact base is F_i intersect F_j. Its prescribed
closed boundary is its intersection with the union of the already
handled F_k, i<k<j.

On that boundary, the earlier z_i has range in Her(z_k z_k*) for
some k<j. By the induction hypothesis that hereditary algebra lies
inside Her(z_j z_j*) there. Hence the existing vector is valid exact
boundary data for target z_j z_j*. The coefficient inequality is
strict, v_i<v_j, throughout the new base. Exact strict-relative
positive embedding supplies the extension. This verifies compatibility
on all multiple overlaps, including their closed boundaries.

After handling every higher index, extend z_i to the rest of F_i
with constant target a strictly positive element of B. Its hereditary
module is B, and v_i<omega by projection boundedness. Apply the same
relative theorem with the already constructed closed union as boundary.
The result retains all the previously imposed constraints. This
finishes (7.1).

Now define, with zero extension off the appropriate closed sets,

```text
a=sum_i psi_(v_i) z_i z_i*  in C(X,B)_+.                 (7.2)
```

The weights vanish outside their respective F_i, so zero extension
is continuous. The sum is a contraction since all A_i are contractions
and the weights sum to at most one. At x choose the largest active
label v_i, meaning psi_(v_i)(x)>0. Every other active range is in
Her(z_i z_i*) by (7.1). The positive coefficient of z_i z_i* is
nonzero, and consequently

```text
[a(x)]=v_i.                                            (7.3)
```

If this value is a nonzero compact p, then on its entire level set
the support of a is z_p z_p*. On a compact subset K of that level
set the positive weight psi_p has a positive minimum, so this is an
actual continuous support projection, equivalent to A_p|K by z_p.
Its image under phi is equivalent to P_p|K. This identifies the
compact restriction invariant of the constructed positive.

## 8. Both global sandwich comparisons

Every active label at x lies between [l(x)] and f(x), by (5.2).
Equations (7.2)--(7.3) therefore give the fiberwise inequalities

```text
[l(x)] <= [phi(a(x))] <= [d(x)] <= [b(x)].               (8.1)
```

Let p be a nonzero compact value and let K be any compact subset
of the equality stratum [l(x)]=p=[phi(a(x))]. The compact-output
property in Section 5 puts K inside U_p. Section 7 identifies the
support bundle of phi(a)|K with P_p|K; (3.2) identifies the latter
with supp(l)|K by the uniform polar partial isometry. Thus the
compact-bundle condition for l<=_Cu phi(a) is verified.

Likewise, on any compact K in the equality stratum
[phi(a(x))]=p=[b(x)], Section 7 and the second estimate of (3.2)
identify the two support bundles. The comparison criterion therefore
applies in both directions of (8.1), and gives the global statements

```text
[(b-epsilon)_+] = [l] <= phi[a] <= [b].                  (8.2)
```

This proves (1.2). Equal compact labels have not been replaced by
mere fiber-rank equalities, and equal soft labels need no compact
bundle condition in the criterion. The largest-label hereditary
argument preserves overlaps instead of replacing their sum by an
orthogonal sum.

## 9. The sandwich gives actual surjectivity

Fix b and choose beta_1>0. Apply (1.2) to the positive
(b-beta_1)_+ with cutoff beta_1 to obtain x_1 in source Cu with

```text
[(b-2 beta_1)_+] <= phi(x_1) <= [(b-beta_1)_+] << [b].
```

Inductively choose 0<beta_(n+1)<beta_n/2 sufficiently small that

```text
phi(x_n) <= [(b-2 beta_(n+1))_+].
```

This is possible because phi(x_n)<<[b]. Apply the same sandwich to
(b-beta_(n+1))_+. It supplies x_(n+1) with

```text
phi(x_n) <= [(b-2 beta_(n+1))_+]
          <= phi(x_(n+1)) <= [(b-beta_(n+1))_+] << [b].
```

First-factor order reflection gives x_n<=x_(n+1) in the source.
Since beta_n tends to zero, Cu continuity of increasing suprema gives

```text
phi(sup_n x_n)=sup_n phi(x_n)=[b].
```

This proves surjectivity for finite-dimensional compact X. Combined
with order reflection, the actual first-factor map is a Cu isomorphism
for every such X.

## 10. Arbitrary compact and locally compact bases

For a compact metric X, choose countably many continuous functions
separating its points and let X_n be the image under the first n.
These are finite-dimensional compact metric spaces with surjective
coordinate bonding maps and inverse limit X. Stone--Weierstrass gives

```text
C(X,D)=lim_n C(X_n,D),
C(X,D tensor Z)=lim_n C(X_n,D tensor Z).
```

The specified first-factor maps form a commuting diagram of these
systems. Each finite-stage Cu map is an isomorphism by Section 9.
Continuity of Cu therefore gives the same conclusion for X. There
is no attempt to approximate a prescribed compact stratum at a finite
stage: full finite-dimensional regularity has already been proved.

For second-countable locally compact Hausdorff X, apply the compact
result to its one-point compactification. The ideal C_0(X,D) is
identified by evaluation at infinity, and naturality plus the
coefficient Cu isomorphism identifies its Cu ideal with the target
Cu ideal. Equivalently use the established ideal permanence of actual
first-factor Cu regularity. This proves (1.1).

Seth--Vilalta's Theorem A shows these section algebras are pure; the
locally compact case follows by passage to ideals. The conclusion is
therefore a full positive coefficient-field corridor for LXXVI,
including nonnuclear coefficients and infinite-dimensional compact
bases.

## 11. Prior art and internal review record

The range-theorem strategy of finite interpolation and hereditary
weighted gluing appears in Tikuisis,
[*The Cuntz semigroup of continuous functions into certain simple
C*-algebras*](https://arxiv.org/pdf/1007.2927), Section 5, for simple
unital Z-stable ASH coefficients. That coefficient theorem is not
invoked for D. Here the closed patch refinement and the exact strict
relative input replace the numerical rank buffers from an ASH
presentation. The proof above separately verifies the two endpoint
compact-bundle invariants required for a hereditary sandwich.

Independent internal review covered the following separate portions.
The root reviewer checked Sections 3--4 and 8--10, including both
endpoint bundle identifications, the below-delta spectral tail, both
global comparisons, and the increasing-supremum and base-limit steps.
A second reviewer checked Sections 5--7, including all original
singleton upper bounds in interpolation, comparability on truncated
closed barycentric supports, and compatibility on multiple overlaps.
The author separately stress-tested the spectral neighborhood lemma.
No gap was found in these checks.

The root reviewer also checked the primary statements of APRT
Theorem 3.5 and APT Proposition 5.4.4 and Sections 7.3.16--18 against
the coefficient hypotheses above. In particular weak cancellation
supplies the actual maximum of all classes properly below a compact
class, and nonelementarity is supplied by purity. The relative
embedding foundation and compact-equality-strata comparison input
were independently checked before this promotion.

No equality of fiber ranks alone proves any global comparison in
this manuscript. The internal review does not replace external
mathematical verification.
