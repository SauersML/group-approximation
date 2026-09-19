# Exact relative positive embeddings through strictly larger hereditary modules

Status: internally reviewed on 5 September 2026; no unresolved gap found.
Mixed target realization is a separate problem and is not claimed here.

Let D be separable, simple, stably finite, pure, and real rank zero, and
put B=D tensor K. The argument uses real rank zero, stable rank one, and
K-stability of every nonzero projection corner. The latter two properties
follow respectively from Lin's theorem and Zhang's Theorem II under the
stated coefficient hypotheses.

## The exact strict extension theorem

Let X be finite-dimensional compact metrizable and Y closed in X.
Let c,d in C(X,B)_+ be contractions, with [c(x)]<=[d(x)] everywhere
and [c(x)]<[d(x)] off Y whenever c(x) is nonzero. Every norm-continuous
z_Y:Y -> B with z_Y*z_Y=c|Y and z_Y(y) in closure(d(y)B) extends to a
norm-continuous z:X -> B with z*z=c and zz* in Her(d).

Section 6 proves this theorem. The cutoff result below is its immediate
corollary, with a specified compatible boundary map.

## The cutoff corollary

Let X be finite-dimensional compact metrizable and Y closed in X.
Let a,b in C(X,B)_+ be contractions such that [a(x)]<=[b(x)] for all x,
and [a(x)]<[b(x)] whenever x is outside Y and a(x) is nonzero.
Fix epsilon>0. Suppose a norm-continuous s_Y:Y -> B satisfies

```text
s_Y* s_Y = (a|Y-epsilon/2)_+,
s_Y(y) in closure(b(y)B).
```

Then there is a norm-continuous v:X -> B with

```text
v*v = (a-epsilon)_+,
v(x) in closure(b(x)B),
v|Y = s_Y h_epsilon(a|Y),
```

where h_epsilon(t)=sqrt((t-epsilon)_+/(t-epsilon/2)_+) for t>epsilon/2
and h_epsilon(t)=0 otherwise. In particular, vv* belongs to Her(b)
globally and (a-epsilon)_+ <=_Cu b.

The proof below establishes a relative extension theorem for the
**strict** embedding fibers, with the boundary fibers replaced by the
prescribed singleton. It does not assert equi-local connectivity for
the unrestricted family of exact embedding spaces. The disappearing
loop counterexample in the preceding working notes remains valid.

## 1. Module notation and cancellation of the finite part

For c in B_+, write H_c=closure(cB)=closure(c^(1/2)B), a right Hilbert
B-module. Its compact operators are Her(c). Define

```text
E(c,d) = {z in H_d : z*z=c}.
```

This is a norm-closed subset of B. Its points are in bijection with
isometric B-module embeddings T:H_c -> H_d, by z=T(c^(1/2)). Conversely,
z determines T(c^(1/2)e)=ze, initially on a dense submodule. Norm
convergence of z is equivalent to point-norm convergence of T: all the
embeddings have operator norm at most one, and c^(1/2)B is dense.
Adjointability of T is not assumed.

A projection p in Her(c) does give an orthogonal decomposition

```text
H_c = pB direct_sum (1-p)H_c.
```

Its complement is again a countably generated Hilbert module. Its
compact-operator algebra is (1-p)Her(c)(1-p), a hereditary subalgebra
of B, and therefore has real rank zero. It can be represented as H_c'
for a strictly positive element c' of that hereditary algebra.

We use exact cancellation of a projection summand:

```text
x+[p] <= y+[p]  implies  x<=y.
```

The primary source is Rordam--Winter, *The Jiang--Su algebra revisited*,
Proposition 4.2, <https://arxiv.org/pdf/0801.2259>. Apply that proposition
to the stable-rank-one algebra B itself, so arbitrary representatives
in B are already elements of M_infinity(B). In particular, if
x+[p]<y+[p], then x<y: cancellation gives the weak inequality, and
equality would contradict the original strict inequality.

All uses of module decompositions below are actual orthogonal
decompositions. We do not replace equality of Cu classes by a chosen
module isomorphism.

## 2. The already established projection-source input

For a projection p and d in B_+ with [p]<[d], the space E(p,d) is
nonempty and weakly contractible. This was proved in
`stw99-lxxvi-rr0-relative-projection-selection-audit-2026-09-05.md`:
projection approximate units in Her(d) reduce compact families of
embeddings to proper projection Stiefel spaces; Zhang's K-stability
theorem and full-corner K-theory make those spaces weakly contractible.

We also use the following explicit local transport. If V,W in E(p,d)
are close, there is a unitary U(V,W) in the unitization of Her(d),
depending continuously on V,W, such that

```text
U(V,W)V=W,   U(V,V)=1,
||U(V,W)-1|| <= C ||V-W||
```

for a universal C and sufficiently small ||V-W||. The unitary has a
continuous path from 1 with a similar bound.

For completeness, set r=VV*, s=WW*. The polar unitary of
sr+(1-s)(1-r) sends r to s and is uniformly close to 1. Call it h.
Then k=W(hV)*+(1-s) is a unitary, and U=kh sends V to W. All products
V W* lie in Her(d). The formulas give the uniform bound after restricting
to a fixed small norm neighborhood. The path is obtained from the
principal logarithm of U. This also proves local triviality of the
restriction bundles used next.

## 3. From finite projection frames to full module embeddings

First suppose [c]<=[d]. Real rank zero supplies an increasing projection
approximate unit p_n for Her(c), with p_0=0. Compatible embeddings
V_n:p_nB -> H_d can be constructed inductively.

Indeed, if V_n is fixed and r_n=V_n V_n*, decompose

```text
H_d = r_n B direct_sum (1-r_n)H_d.
```

The inequality [p_(n+1)]<=[d], after cancellation of [p_n], says that
p_(n+1)-p_n embeds into (1-r_n)H_d. This is ordinary comparison of a
projection with a positive element, so it gives an actual embedding
of the projection. Add it to V_n to get V_(n+1).

The resulting compatible maps extend by continuity to an isometric
embedding H_c -> H_d. In terms of vectors, the limit is

```text
z = lim_n V_n p_n c^(1/2),
```

because the norm of the difference between stages n and m is bounded
by ||(p_m-p_n)c^(1/2)||. Thus E(c,d) is nonempty. This construction
does not require a separate assertion that Cu comparison is already
implemented by an adjointable module map.

Now suppose [c]<[d]. We prove that E(c,d) is weakly contractible.
For every n, [p_n]<[d]. The finite-frame spaces E(p_n,d) are therefore
weakly contractible by Section 2. The restriction map

```text
rho_n:E(p_(n+1),d) -> E(p_n,d),   V |-> V p_n,
```

is onto. Over a frame V_n its fiber is the space of embeddings of
p_(n+1)-p_n into (1-r_n)H_d. Cancellation and the strict inequality
[p_(n+1)]<[d] show that this is a strict projection-source embedding
space, or the singleton when the difference projection is zero.
Every such fiber is weakly contractible.

The local transport U(V,W) from Section 2 identifies nearby fibers
continuously, so rho_n is a locally trivial fiber bundle. In particular
it is a Serre fibration. This is a bundle of actual embeddings, not a
map between their Cu equivalence classes.

Given a sphere map into E(c,d), restrict it to every p_n. Extend the
first finite-frame sphere over its ball using weak contractibility.
Inductively extend the next finite frame compatibly with the already
extended preceding frame and the prescribed sphere boundary. This
relative lifting is valid for rho_n: its fiber is nonempty and weakly
contractible, so the obstruction groups for a finite CW pair vanish.
Equivalently, an onto Serre fibration with weakly contractible fibers
has the relative lifting property for CW pairs. Only disks and their
sphere boundaries are used here.

The compatible disk embeddings V_n give the uniform limit
V_n p_n c^(1/2), since ||(1-p_n)c^(1/2)|| -> 0 independently of the disk
parameter. This produces a continuous extension in E(c,d), with the
original sphere boundary. Consequently E(c,d) is C^k for every k.

## 4. Quantitative local connectivity of the strict family

Consider the family consisting of all E(c,d) with 0<=c<=1 and
[c]<[d], together with arbitrary singleton subsets of B. This family
is equi-LC^k for every finite k. The strict inequality is essential.

Fix a desired ambient radius R>0; replacing it by min(R,1) causes no
loss. Choose eta>0 so small that 4 sqrt(eta)<R/4. For each c, choose a
projection

```text
p in Her((c-eta)_+)
```

with ||(1-p)(c-eta)_+^(1/2)||<sqrt(eta). Then

```text
||(1-p)c^(1/2)|| < 2 sqrt(eta).                 (1)
```

Such a projection exists by real rank zero. It need not depend
continuously on c: in the equi-local connectivity test c is fixed
within each individual sphere map, while all resulting estimates are
uniform in c. The projection p=0 is allowed.

Choose a continuous bounded scalar function g on [0,1] which equals
t^(-1/2) for t>=eta and has norm at most eta^(-1/2). Because p is in
Her((c-eta)_+),

```text
c^(1/2) g(c) p=p.
```

Let z:S^k -> E(c,d) have image in a delta-ball about an arbitrary
ambient point z_*. Write T_s for its module embeddings and fix one
point s_0. The p-frames satisfy

```text
T_s(p)=z(s)g(c)p,
||T_s(p)-T_(s_0)(p)|| <= 2 delta/sqrt(eta).     (2)
```

For small enough delta, Section 2 gives a continuous family of target
unitaries U_s, connected to 1 through uniformly small paths, such that
U_s T_s(p)=T_(s_0)(p). Multiplying the embeddings by these paths makes
a homotopy, in E(c,d), from z(s) to z'(s)=U_s z(s). It moves vectors
by at most C_1 delta/sqrt(eta), for one universal C_1. The p-part of
the new embeddings is exactly fixed.

Let r=T_(s_0)(p)T_(s_0)(p)*. The remaining embeddings map

```text
(1-p)H_c -> (1-r)H_d.
```

Their source and target Cu classes are strictly ordered: add [p] to
both and use [c]<[d] and cancellation from Section 1. The space of
these complementary module embeddings is weakly contractible by
Section 3, using strictly positive representatives of the two
complementary hereditary algebras. The sphere of tail embeddings
therefore extends over a disk while leaving the p-part fixed.

Point-norm continuity of this tail sphere follows from that of T_s;
the fixed-module vector model in Section 1 identifies its topology
with the norm topology used in Section 3. When reconstructing the
original vector, every extension of the tail is evaluated only on
(1-p)c^(1/2). Thus (1) bounds its distance from the tail at s_0 by
4 sqrt(eta). The entire inner disk lies within

```text
delta+4 sqrt(eta)
```

of z_*. The preceding small-unitary homotopy forms an outer collar,
whose vectors lie within delta+C_1 delta/sqrt(eta) of z_*.

Choose delta, depending only on R, so that (2) lies in the fixed
transport neighborhood and both displayed distance bounds are <R.
The collar and inner disk together extend the original sphere into
E(c,d) intersected with the R-ball. The construction works for every
k, with the same delta. If p=0, use weak contractibility of the whole
embedding space and the small bound on ||c^(1/2)|| instead. Singleton
members have the required extension property trivially.

This proves the precise equi-LC assertion. It does not concern fibers
E(c,c) with c nonzero, whose disappearing compact summands gave the
previous counterexample. Here strict comparison supplies the
contractible complementary embedding space at the crucial step.

## 5. Lower semicontinuity for varying positive initial elements

Suppose c,d:X -> B_+ are norm continuous and [c(x)]<=[d(x)] for all x.
Then x -> E(c(x),d(x)) is lower semicontinuous in the fixed Banach
space B. No strictness is needed for this assertion.

Fix x_0 and z_0=T_0(c(x_0)^(1/2)). Choose a projection
p_0 in Her((c(x_0)-eta)_+) with
||(1-p_0)c(x_0)^(1/2)|| small, as in Section 4. Put
e_0=g(c(x_0))p_0, so c(x_0)^(1/2)e_0=p_0. Near x_0, polar normalization
of c(x)^(1/2)e_0 gives continuous partial isometries t_x with

```text
t_x*t_x=p_0,   p_x=t_x t_x* in Her(c(x)),
t_(x_0)=p_0.
```

Independently, approximate T_0(p_0) arbitrarily closely by d(x_0)e_1 p_0
for a fixed e_1 in B. Polar normalization of d(x)e_1 p_0 gives a local
continuous target frame w_x in E(p_0,d(x)), as close to T_0(p_0) as
desired. Exact agreement with T_0(p_0) at x_0 is unnecessary for lower
semicontinuity; arbitrarily close agreement suffices.

The map w_x t_x* embeds p_xB into H_(d(x)). If r_x=w_x w_x*, the
inequality [c(x)]<=[d(x)], after cancelling the compact summand [p_0],
gives

```text
[(1-p_x)H_(c(x))] <= [(1-r_x)H_(d(x))].
```

Section 3 supplies an isometric embedding S_x of these complementary
modules at each x. We do not assert or need a continuous choice of S_x
in this lower-semicontinuity test. Define

```text
z_x = w_x t_x* c(x)^(1/2)
      + S_x((1-p_x)c(x)^(1/2)).
```

The two summands have orthogonal target ranges, so z_x belongs to
E(c(x),d(x)). Its first summand is uniformly close near x_0 to
T_0(p_0)c(x_0)^(1/2). Its second summand has norm exactly
||(1-p_x)c(x)^(1/2)||, which is small near x_0. The discarded tail of
z_0 has the same small bound. Hence z_x lies in any prescribed
neighborhood of z_0 once eta, the frame approximation, and the base
neighborhood are sufficiently small. This proves lower semicontinuity.

If p_0=0 the entire norm is small and no frame transport is necessary.
If c(x_0)=0, the statement follows immediately from
||z_x||=||c(x)||^(1/2) and nonemptiness from Section 3.

## 6. Relative selection on the strict locus

Let c,d be positive sections over finite-dimensional compact metrizable
X, with c a contraction and [c(x)]<=[d(x)] everywhere. Let Y be closed,
and assume [c(x)]<[d(x)] off Y whenever c(x) is nonzero. Suppose a
continuous z_Y is prescribed on Y with z_Y*z_Y=c|Y and z_Y(y) in H_(d(y)).

Use the multifunction

```text
Phi(x) = E(c(x),d(x))  for x outside Y,
Phi(y) = {z_Y(y)}      for y in Y.
```

It is lower semicontinuous by Section 5, continuity of z_Y, and
closedness of Y. Its values are nonempty closed subsets of the complete
metric space B. Every value is C^k for every k by Section 3 or is a
singleton. Section 4 proves that the entire family is equi-LC^k.

Michael's finite-dimensional selection theorem now gives a continuous
selection z:X -> B. The exact primary statement and a self-contained
proof are in Gutev, *Constructing selections stepwise over skeletons
of nerves of covers*, Theorem 1.1:
<https://www.math.bas.bg/serdica/2018/2018-137-154.pdf>.

Thus z extends z_Y and z*z=c. Pointwise z(x) in H_(d(x)) implies global
z in closure(d C(X,B)): increasing functional-calculus approximate
units f_n(d(x)) converge on z(x), and Dini's theorem makes the
convergence uniform on compact X. In particular zz* belongs to Her(d).

## 7. Applying the spectral slack

Set c=(a-epsilon)_+ and prescribe z_Y=s_Y h_epsilon(a|Y). Functional
calculus gives z_Y*z_Y=c|Y, and right-module closure gives z_Y(y) in
H_(b(y)). Whenever x is outside Y and c(x) is nonzero,

```text
[c(x)] <= [a(x)] < [b(x)].
```

Thus Section 6 applies and proves the stated cutoff lemma, with the
exact specified boundary restriction.

The epsilon/2 buffer supplies the continuous boundary cutoff map and
discards all summands below epsilon. The proof controls larger source
spectral pieces through (1)--(2) and permits arbitrary motion of their
small weighted tails in strictly larger complementary modules. It never
uses uniform local connectivity of unrestricted equal-class fibers.

## Prior art and remaining scope

Tikuisis, *The Cuntz semigroup of continuous functions into certain
simple C*-algebras*, Lemma 4.2, already gives a relative positive-element
embedding theorem for recursive subhomogeneous coefficients with a
numerical matrix-rank gap:
<https://arxiv.org/pdf/1007.2927>.
The present coefficient argument replaces the matrix-rank-gap input
by proper-corner K-stability, projection approximation, and compact
cancellation. The relative embedding method itself is not claimed new.

The theorem above is a comparison/extension result. This artifact does
not construct an arbitrary mixed target Cu class in the source, does
not prove hereditary inner cofinality, and does not conclude full LXXVI.

## Internal review

The root reviewer checked the complete argument, including the actual
projection-frame restriction bundles, relative disk lifting, uniform
convergence of their compatible embeddings, and the source-tail bounds
in Section 4. The review also checked varying-source lower semicontinuity
without assuming a continuous choice of tail embeddings, the singleton
boundary replacement, and the global hereditary membership conclusion.
Rordam--Winter Proposition 4.2 was checked in the primary manuscript:
it cancels a projection summand from comparison in a stable-rank-one
algebra, with no unitality assumption. The strict-only selection family
is essential throughout. This is internal mathematical review, not
external peer review or formal verification.
