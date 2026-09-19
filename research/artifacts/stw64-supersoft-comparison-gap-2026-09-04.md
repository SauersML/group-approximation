# STW LXIII--LXIV: the supersoft comparison gap

Date checked: 2026-09-04. These are derived mathematical statements with
published inputs, not a claim of priority or a solution of a named open
problem. No Lean formalization is asserted.

## Source and status

The source problem is Schafhauser--Tikuisis--White,
[Nuclear C*-algebras: 99 problems](https://arxiv.org/html/2506.10902v2),
Problems LXIII--LXIV. Gardella--Perera,
[The modern theory of Cuntz semigroups](https://arxiv.org/html/2212.02290v2),
Problem 16.3, explicitly requires the two maps to preserve unit classes.
Targeted primary-source searches on 2026-09-04 did not find a general
resolution. This is not an exhaustive certification of the literature.

The imported calculus is Antoine--Perera--Robert--Thiel,
[C*-algebras of stable rank one and their Cuntz semigroups](https://arxiv.org/html/1809.03984v3),
Section 2.5, Proposition 7.4, the full-function realization results in
Section 7, Proposition 8.2, Theorem 8.4, and Section 8.6.

Repository searches for supersoft and scalar comparison gaps found no
previous node. The literature search found the APRT calculus and adjacent
work on radius of comparison; no novelty claim is inferred from a search
not finding this exact formulation.

## Hypotheses and notation

Throughout, A is separable, simple, unital, infinite-dimensional, and has
stable rank one and a nonempty normalized 2-quasitrace space. Write
S=Cu(A), u=[1_A], and x-hat(lambda)=lambda(x). Let

    s_t = alpha(t*u-hat),                 0<t<infinity.

The imported theorems give s_t-hat=t*u-hat, monotonicity of alpha, and

    x+s_t = alpha(x-hat+t*u-hat)           (x in S, t>0).       (1)

They also give

    x+z<=y+z', z'<<z  =>  x<=y.                              (2)

The comparison radius is the infimum over R>0 for which
x-hat+R*u-hat<=y-hat implies x<=y. Rank inequalities are on the full
functional cone. In this simple unital setting they reduce to normalized
quasitraces for the nonzero full classes appearing in the proof.

## The gap formula

We prove

    rc(A) = inf { b-a : 0<a<b<infinity, s_a<<s_b }.             (3)

An empty infimum is infinity.

First suppose s_a<<s_b. For arbitrary x,y with
x-hat+(b-a)*u-hat<=y-hat, equation (1) gives

    x+s_b
      = alpha(x-hat+b*u-hat)
      <= alpha(y-hat+a*u-hat)
      = y+s_a.

Apply (2) to get x<=y. Thus b-a is an admissible comparison constant.

Conversely, suppose b-a>rc(A). Choose an admissible R with
0<R<b-a. Choose z_n<<z_(n+1) with sup_n z_n=s_b. For every normalized
quasitrace lambda, lambda(z_n) increases to b. The sets

    U_n = { lambda : lambda(z_n)>a+R }

are open and increasing and cover the compact normalized quasitrace space.
A finite subcover, and then the largest of its indices, gives U_n equal
to the whole space for one n. The comparison inequality with constant R
therefore gives s_a<=z_n<<s_b. Taking infima proves (3).

No conclusion at the boundary b-a=rc(A)>0 is required or asserted.
In particular, this proof does not assume alpha preserves <<. In a
positive-radius target, small gaps are exactly where that assumption fails.

## Obstruction to the canonical second Jiang--Su map

Let f:Cu(Z)->S preserve the unit, and denote the soft real classes by t.
For a normalized functional lambda, the integer lower and upper bounds on
n*t show lambda(f(t))=t on letting n tend to infinity. Thus

    f(t)-hat = t*u-hat.                                      (4)

The image is soft. Indeed, for v<<f(t), preservation of increasing
suprema gives r<t with v<=f(r). Choose k with (k+1)r<=kt. Then
(k+1)v<=k*f(t), which is the softness criterion.
The supersoft majorant theorem gives f(t)<=s_t.

Suppose now f(t_0)=s_(t_0) for one finite t_0>0. For every r>0,
additivity, (1), and (4) give

    f(t_0+r)=s_(t_0)+f(r)=s_(t_0+r).

For every delta>0 the source has t_0+1 << t_0+1+delta, so f gives
s_(t_0+1)<<s_(t_0+1+delta). By (3), rc(A)<=delta. Hence rc(A)=0.

Therefore, if rc(A)>0, every unital Cu(Z) map lies strictly below s_t
at every finite positive soft real t. The canonical scalar family differs
from every actual map, but it is not itself another Cu-morphism.

## What remains open

Two distinct morphisms require two genuine coherent soft scales, with
additivity, increasing-supremum preservation, compact-containment
preservation, and the mixed unit comparisons. Neither rank realization
nor the canonical supersoft scale provides this pair.

The former LXIV attempt incorrectly treated rank realization as
classification of the soft part. The argument above pinpoints a missing
relation and removes that shortcut. It does not settle LXIII or LXIV.
