# Consecutive chart feedback: explicit candidate and unresolved equations

Date: 2026-09-08. This is a construction attempt, not a claim of an
injective or nonsurjective automaton. No computational check was run.
The prediction is unresolved: isolated finite charts are reversible,
and the remaining collision equations involve both charts.

Use the binary Leavitt atlas generators a_1,b_1,a_2,b_2 and finite
chart groups K_1,K_2 from
`research/artifacts/gottschalk-four-track-finite-chart-collision-2026-09-08.md`.
On binary configurations define alternating bilinear operations

    C(U,V)(g)=U(g a_1)V(g b_1)+U(g b_1)V(g a_1),
    D(U,V)(g)=U(g a_2)V(g b_2)+U(g b_2)V(g a_2).

The proposed four-track rule uses consecutive chart blocks:

    F_1=x_1+C(x_2,x_3),       F_2=x_2+C(x_3,x_4),
    F_3=x_3+D(x_4,x_1),       F_4=x_4+D(x_1,x_2).

All coefficients are specified. Alternation fixes every configuration
whose four tracks are scalar multiples of a common binary mask. The
common-operation four-cycle theorem in
`experiments/gottschalk-feedback-design-2026-09-08.md` does not apply:
here C and D are different operations.

## Why the chart blocks are consecutive

There is a small exact eigenmask inside the first chart. Put

    H=<a_1>,       U=1_H,       Z=1_(H b_1).

Then C(Z,U)=U. The summand Z(g b_1)U(g a_1) equals U(g).
The other summand vanishes: its nonvanishing would force
b_1^-1 a_1 b_1^-1 into H. This cannot occur, since that matrix takes
the last standard basis vector to (1,1,1,1)^T, whereas every power
of a_1 fixes the last basis vector. Also b_1 is outside H, so U and
Z have disjoint support. Both supports have three elements.

The second-chart operation D vanishes on any two inputs supported
in K_1. Indeed simultaneous membership of g a_2 and g b_2 in K_1
would force a_2^-1 b_2 into K_1, excluded in the collision artifact.

Therefore assigning C to opposite outputs 1 and 3 would immediately
give the collision (U,Z,U,Z) and (0,Z,0,Z), regardless of D in the
other two outputs. Consecutive assignment avoids this exact test.

## Each isolated chart gives an explicit bijection

For inputs supported in K_1, D vanishes everywhere and C stays
supported in K_1. The rule becomes triangular. Given its output y,
recover

    x_4=y_4,       x_3=y_3,
    x_2=y_2+C(y_3,y_4),
    x_1=y_1+C(x_2,y_3).

The reverse chart separation holds by the same exact calculation:
(a_1^-1 b_1)s_000=s_1+s_000+s_001, so applying t_1 gives 1;
for h in K_2, t_1 h s_000 is either 0 or s_0. Thus C vanishes on
inputs supported in K_2. The inverse there is

    x_1=y_1,       x_2=y_2,
    x_4=y_4+D(y_1,y_2),
    x_3=y_3+D(x_4,y_1).

These are exact restrictions to finite-support subspaces, not global
inverse formulas. They show that a failure has to use mixed chart
interaction. They do not authenticate any mixed relation needed in
a putative global decoder.

## Exact reduction to two tracks with repeated dependence

For target first outputs p,q and old third and fourth inputs z,w,
put

    t=C(z,w),       x_2=q+t,       x_1=p+C(q+t,z).

This is a reversible input change, with local inverse. In these
coordinates F preserves p,q, and its other outputs are exactly

    H_(p,q)(z,w) =
      (z+D(w,p+C(q+t,z)),
       w+D(p+C(q+t,z),q+t)).

Consequently, if F is injective, the established nonlinear
certificate-fiber theorem makes strictness equivalent to strictness
of the p=q=0 fiber. That fiber is

    t=C(z,w),       s=C(t,z),
    H(z,w)=(z+D(w,s), w+D(s,t)).

The first correction has bidegree (2,2) in (z,w); the second has
bidegree (3,2). For a=a_1,b=b_1, the intermediate cubic is explicitly

    s(g) = z(g a^2)w(g ab)z(g b)
         + z(g ab)w(g a^2)z(g b)
         + z(g ba)w(g b^2)z(g a)
         + z(g b^2)w(g ba)z(g a).

Thus the candidate is also a completely specified two-track rule
with eight quartic terms in its first correction and sixteen
quintic terms in its second. The two right cosets a_2 K_1 and
b_2 K_1 are disjoint, so the outer D operation does not collapse
their variables. The earlier conditional-linearity exclusion does
not apply to this residual map.

## A concrete remaining collision equation

Any nonzero U and any W satisfying

    C(U,W)=D(U,W)=U

give an actual collision:

    F(U,W+U,U,W+U)=F(0,W,0,W)=(0,W,0,W).

With W=1, this asks for a common nonzero kernel vector of

    I+R_(a_1)+R_(b_1),       I+R_(a_2)+R_(b_2)

on the full binary shift. Individual singularity is known exactly.
For either chart, the operator I+exterior^2(a)+exterior^2(b) on
exterior^2(F_2^4) kills

    k=e_01+e_02+e_12+e_23.

Indeed exterior^2(a)k=e_02+e_03+e_13+e_23 and
exterior^2(b)k=e_01+e_03+e_12+e_13. This proves that 1+a+b is
not a unit in the finite chart group algebra, but it does NOT
provide a common kernel for the two charts.

The common-kernel question is equivalently whether the span of
the translates of the two local relations is a proper subspace
of the finitely supported group algebra. With the convention
R_a U(g)=U(ga), it is the left ideal

    F_2[Q](1+a_1+b_1)+F_2[Q](1+a_2+b_2).

If this ideal is proper, any nonzero linear functional on its
quotient gives a common-kernel configuration. If it is the whole
ring, a finite Bezout identity excludes this particular constant-W
collision; other nonlinear collisions still have to be excluded.

The simplest shared-tail exterior-square attempt does not solve
this. On the boundary module with tail 0^infinity, let
u=0^infinity, v=010^infinity, r=10^infinity,
d=0010^infinity, e=0110^infinity. The two chart kernel wedges are

    k_1=v wedge r+v wedge u+r wedge u+u wedge d,
    k_2=u wedge r+u wedge v+r wedge v+v wedge e.

They differ by u wedge d+v wedge e, which is nonzero. A common
vector requires a further argument; infinitely many separate
chart kernels do not establish one.

## What would finish this construction

A counterexample requires an actual finite-memory decoder J with
J composed with H equal to the identity on every binary input and
H composed with J different from the identity on a finite pattern.
Both are literal Boolean polynomial identities, with X^2=X and
addresses multiplied in Q. For a fixed finite decoder memory and
degree, its unknown coefficients enter J composed with H linearly,
so these are definite finite equations. No solution is asserted.

At present neither injectivity nor a missing output pattern is
proved. A common eigenmask above would instead disprove injectivity
and finish this attempt negatively. The finite-chart controls and
the displayed normalization are the established parts of the design.
