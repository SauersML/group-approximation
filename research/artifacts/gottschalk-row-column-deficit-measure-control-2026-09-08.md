# Row and column entropy deficits have no local measure ordering

Date: 2026-09-08. This is an exact reversible control for the Gottschalk
information-transport route. It refutes a sign comparison of the row
and column deficit measures on the pin-density square, including a
comparison of their singular parts alone. It does not
refute or prove the integrated lower bound needed for surjunctivity.
No computation or enumeration was used.

The posterior formulas and finite-reveal inequalities used here are
proved in
`research/artifacts/gottschalk-information-transport-pinning-control-2026-09-08.md`.

## The total sign is exactly the missing lower bound

Use independent iid source and output pins, with densities t,u, and
the notation

    F(t,u)=E H(X_1 | X_(S_t minus {1}), Y_(T_u)),
    J(t,u)=E H(Y_1 | X_(S_t), Y_(T_u minus {1})),
    a(t,u)=sum_k E I(X_1;Y_k |
                    X_(S_t minus {1}),Y_(T_u minus {k})).

All mask variables are included in the conditioning. The source X is
uniform iid with entropy h per site, and Y has a bounded local decoder
back to X. Group mass transport equates a with the corresponding
column sum. Finite-coordinate reveal accounting implies that

    a(t,u) du <= -d_u F(t,u),
    a(t,u) dt <= -d_t J(t,u)

as measures. Define the nonnegative remainder measures on the square
by

    R(dt,du)=dt [-d_u F(t,u)-a(t,u)du],
    C(dt,du)=[-d_t J(t,u)-a(t,u)dt] du.

Here the Stieltjes decrease measures include endpoint masses if a
value at 0 or 1 differs from its one-sided interior limit. Thus their
total masses equal the displayed endpoint decreases without an
unstated continuity assumption at the ends of the pin interval.

These are the missing reveal contributions. Their definition does not
assert that all their mass is singular with respect to planar Lebesgue
measure: it includes any missing absolutely continuous contribution
as well. Every entropy jump contributes its full atom to the relevant
one-parameter remainder because the reveal term is a density. Write
R^s,C^s for their singular parts with respect to planar Lebesgue
measure.

Writing M=integral integral a(t,u) dt du and

    P(Y)=integral_0^1 E H(Y_1 | Y_(T_u minus {1})) du,

the total endpoint bookkeeping is

    R_total=h-M,
    C_total=P(Y)-M,
    C_total-R_total=P(Y)-h.                         (1)

Thus the useful integrated comparison C_total>=R_total is exactly
the percolative-entropy lower bound P(Y)>=h. Renaming the missing
contributions does not prove that bound. The preceding alphabet-
expanding local encoding gives strict C_total>R_total; the reversible
control below has equal totals but opposite local inequalities.

## Reversible iid control

Set d=65536 and let G=F_(d-1) x C2. At each site use two uniform
independent binary coordinates (x,z), so h=2. If a_1,...,a_(d-1)
freely generate the first factor, define

    (Lx)(g)=x(g)+sum_(j=1)^(d-1) x(ga_j),
    tau(x,z)(g,i)=(x(g,i),z(g,i)+(Lx)(g,1-i)).

This is a local linear involution. It preserves Haar measure on the
binary full shift, so both X and Y=tau(X) are uniform iid processes.
The joint law of (X,Y) is invariant under interchanging its entries.

For iid source and output masks, let r be the greatest fixed point

    r=(1-t)(1-u)[1-tu(1-r)^(d-1)]^(d-1).             (2)

The exact row entropy is

    F(t,u)=1+(1-u)[1-tu(1-r)^(d-1)]^d-u(1-r)^d.     (3)

The tree posterior proof in the preceding artifact applies to every
d: surviving variables can be flipped in an exact infinite-support
kernel configuration, so (2)-(3) describe actual conditional entropy,
not only a necessary peeling statistic.

## A uniform row jump near the top edge

Fix any t in [2/5,3/5] and put u_0=63/64. At r_0=1/320, the right
side f of (2) obeys

    (1-t)(1-u_0)>=1/160,
    (1-r_0)^(d-1)<2^-200.

For the second inequality, (319/320)^320<1/2 and d-1>=200*320.
Bernoulli's inequality now gives

    [1-tu_0(1-r_0)^(d-1)]^(d-1)
      >=1-(d-1)tu_0(1-r_0)^(d-1)
      >1-2^-184>1/2.

Hence f(r_0)>1/320=r_0, while f(1)<1. There is a fixed point larger
than r_0, so the greatest fixed point at u_0 is larger than r_0.

For every u>=u_0 there is no fixed point in

    [1/(4d),1/d].

Indeed, for r<=1/d,

    (1-r)^(d-1)>1/3,
    tu>1/3,
    f(r)<(8/9)^(d-1)<2^-19<1/(4d).

The first bound follows from
(1+1/(d-1))^(d-1)<sum_(k>=0)1/k!<3. For the last bound it suffices
that (8/9)^8<1/2 and d-1>=8*19. All inequalities are strict for
the displayed constants.

At u_1=1-1/(4d), every fixed point is at most

    (1-t)(1-u_1)<=3/(20d)<1/(4d).

The greatest fixed point is decreasing in u. It starts above r_0
at u_0, ends below 1/(4d) at u_1, and cannot take a value in the
forbidden interval. Therefore it has a downward jump somewhere in
(u_0,u_1), from at least 1/d to at most 1/(4d).

Formula (3) is increasing in r. The final term alone shows that the
corresponding entropy jump is greater than

    u_0 [(1-1/(4d))^d-(1-1/d)^d]
      > (63/64)(3/4-1/2)=63/256.                    (4)

Here the first power is at least 3/4 by Bernoulli's inequality,
and the second is less than 1/2 because
(1+1/(d-1))^d>2.

## Opposite signs on transposed rectangles

Consider the rectangle

    Q=[2/5,3/5] x [63/64,1]

in source-density/output-density coordinates. Every t in its first
interval has the row jump (4) inside its second interval. Its full
mass belongs to the row remainder. These selected atoms lie on a
measurable graph: choose

    u_*(t)=sup{u:r(t,u)>=1/d}.

Since r is decreasing in t as well as u, u_* is monotone and hence
measurable. Its graph has planar Lebesgue measure zero. Thus the
selected row-jump mass belongs to R^s, and

    R(Q)>=R^s(Q)> (1/5)(63/256)=63/1280.            (5)

At any fixed u, the entire column remainder is bounded by the total
decrease of J as source pins are added, and this decrease is at most
the two-bit root entropy. Therefore, without needing any column
posterior formula,

    C^s(Q)<=C(Q)<=2(1-63/64)=1/32=40/1280.         (6)

Equations (5)-(6) give the strict quantitative inequality

    R(Q)-C(Q)>23/1280,
    R^s(Q)-C^s(Q)>23/1280.

The source/output symmetry of the involution gives F(t,u)=J(u,t)
and, using mass transport, a(t,u)=a(u,t). Consequently the transpose
Q^T has the reversed inequality:

    C(Q^T)-R(Q^T)>23/1280,
    C^s(Q^T)-R^s(Q^T)>23/1280.

Thus neither R<=C nor C<=R holds as a measure comparison on the
pin-density square, and neither ordering holds for their singular
parts alone. The control has fully iid masks, a bounded
local inverse, and a uniform iid output process. Its total masses
nevertheless agree, since P(Y)=h=2 in (1).

This rules out a proof that assigns a universal favorable sign
locally to these missing contributions. It leaves open the weaker
integrated comparison in (1), whose proof would need cancellation
or transport between distinct parameter regions. No such global
comparison is established here.
