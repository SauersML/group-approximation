# Information transport for Gottschalk: reversible counterexample to exact row accounting

Date: 2026-09-08. This is an independent pure-mathematical attack memo.
It proves neither surjunctivity nor a counterexample to surjunctivity. It
does refute the proposed exact information-row identity below, even for a
reversible local involution with independent source and output pins at
every site. No computation is used.

## The proposed invariant

Let X be the uniform iid process on A^G, put h=log|A|, and let Y=tau(X).
Assume tau has a bounded local decoder sigma, so sigma tau=id. Let S_t
and T_u be independent Bernoulli subsets of G of densities t and u.
All conditional entropies below also condition on these random subsets.
Define

    F(t,u)=E H(X_1 | X_(S_t minus {1}), Y_(T_u)),
    J(t,u)=E H(Y_1 | X_(S_t), Y_(T_u minus {1})).

The finite-coordinate information transport is

    m_tu(g,k)=E I(X_g;Y_k |
                    X_(S_t minus {g}), Y_(T_u minus {k})).

It is nonnegative and equivariant. Tonelli and the group mass-transport
identity equate its expected row and column sums. The candidate completion
would prove, for almost every t,

    integral_0^1 sum_k m_tu(1,k) du = h.                 (R)

This is an exact row-mass conjecture, not merely a claim that a posterior
has no tail. Finite systems satisfy it by the entropy chain rule. Here
F(t,0)=h by independence, and F(t,1)=0 by the bounded local decoder.
The issue is whether the entire decrease is accounted for by individual
output-coordinate reveals. An infinite conditional-information transition
can invalidate that step.

On the column side, finite-coordinate reveal accounting gives at most the
total entropy decrease when source coordinates are revealed. Thus the
candidate row identity would force

    h <= integral_0^1 E H(Y_1 | Y_(T_u minus {1})) du.   (P)

The right side is random-past, or percolative, entropy. For a proper
same-alphabet image it is strictly below h. Indeed every integrand is at
most h; equality in the integral would force Y_1 to be uniform and
independent of every finite collection of other output coordinates.
Translation invariance would then make Y the uniform full-shift process,
contrary to a missing finite pattern. Therefore (R), if established in the
stated iid setting, would settle Gottschalk positively.

The construction below refutes (R), for a positive-measure interval of
source-pin densities, using a reversible involution. Absolute continuity
alone should not be substituted for (R) without also authenticating the
infinite-coordinate reveal formula.

## Why general Rokhlin entropy does not supply the lower bound

Seward's [Krieger II, author PDF](https://mathweb.ucsd.edu/~bseward/Files/krieger2.pdf)
derives Bernoulli Rokhlin entropy equal to base entropy, and then
surjunctivity, under an additional positive-Rokhlin-entropy hypothesis for
countable groups. This is an open input, not an unconditional lower bound
available here.

Alpeev's [random-order Gibbs paper](https://arxiv.org/pdf/1705.08559)
obtains its lower bound through sofic models. The local-conjugate Bernoulli
class above is narrower than arbitrary measurable generators, but no
argument here removes the missing lower bound even in that class.

## A reversible local rule with a discontinuous pinning posterior

The broad assertion that positive source pinning and a bounded local
decoder eliminate conditional-information transitions is false. The
following example uses structured layer pinning; it does not refute (R),
whose source and output subsets are iid on the entire site group.

Let H be the free group on a,b, let G=H x C_2, and use alphabet F_2^2,
with coordinates (x,z). Define

    (Lx)(g)=x(g)+x(ga)+x(gb),
    F(x,z)(g,i)=(x(g,i), z(g,i)+(Lx)(g,1-i)).          (1)

This is a G-equivariant finite-memory cellular automaton and F^2=id.
It is therefore a control with an explicit local inverse and no strict
embedding. Start with uniform iid source (x,z).

Reveal the source and output on the layer H x {0}. These observations
reveal x_0,z_0 and Lx_1. Now independently reveal additional source sites
on layer 1 with density t and output sites there with density u. Since
x_0 is already known, the observed second output coordinate on layer 1
only determines the independent z_1 coordinate. The remaining uncertainty
in x_1 is exactly that of x conditioned on its full L-syndrome and on
independent coordinate pins of combined erasure probability

    epsilon=(1-t)(1-u).                                (2)

The bipartite graph with variable vertices H, check vertices H, and a check
g joined to variables g,ga,gb is the 3-regular bipartite tree. It is the
universal cover of the graph having two vertices and three parallel edges.

For any fixed pin set, differences between two posterior configurations
are precisely the solutions v of Lv=0 vanishing at pinned variables.
The posterior is uniform Haar measure on an affine translate of this
closed binary linear space.

Apply the following peeling rule: whenever a check has only one remaining
unpinned variable, delete that variable. Every deleted variable must be
zero in every such difference. Conversely, a variable in the surviving
core can be nonzero in a difference. To construct one, set it to one and,
at each of its incident checks, choose one further surviving variable to
be one. Continue away from the root. The tree prevents collisions, and
every encountered check has exactly two chosen incident variables. All
other variables are zero. This gives Lv=0 and respects every pin.

Consequently the root posterior bit has entropy one precisely when it
survives this peeling process, and zero otherwise. Infinite support is
essential: there is no nonzero finitely supported solution of Lv=0,
because the finite support's neighboring tree has a check of degree one.

Let r be the probability that a variable-to-check branch survives. The
greatest fixed point, obtained by peeling from all unpinned variables,
satisfies

    r=epsilon (1-(1-r)^2)^2
     =epsilon (2r-r^2)^2.                              (3)

The two incident check branches excluding the parent must each have at
least one other surviving variable. The independence of the branches
justifies (3). The root survival probability is

    theta=epsilon (2r-r^2)^3.                          (4)

For r>0, equation (3) is equivalent to

    1=epsilon r(2-r)^2.

The maximum of r(2-r)^2 on [0,1] is 32/27, attained at r=2/3.
Therefore the greatest fixed point jumps at

    epsilon_c=27/32,

from zero below epsilon_c to r=2/3 at epsilon_c. Equation (4) then gives

    theta(epsilon_c)=16/27.                            (5)

Thus the expected posterior entropy has a jump of 16/27 bits. For every
fixed additional source-pin density 0<t<5/32, increasing u through

    u_c=1-27/(32(1-t))

crosses this discontinuity. Positive independent source pinning on the
remaining layer does not remove it.

One may choose the initially revealed C_2 layer uniformly to make the
structured pinning law G-invariant. It remains non-iid across G; that
distinction is part of the control, not a technicality to suppress.

## Independent source and output pins: the posterior reduction

Generalize (1) by taking H free on a_1,...,a_(d-1), and set

    (Lx)(g)=x(g)+sum_(j=1)^(d-1) x(ga_j).

The Tanner graph is now the d-regular bipartite tree. The same two-track
rule (1) is a reversible G-equivariant involution. Independently pin the
entire source symbol at each site with probability t and the entire output
symbol with probability s. All masks are independent across sites and
between source and output.

At a physical site, its x coordinate is known if either mask is present.
Its opposite-layer L-syndrome is revealed if both masks are present.
An output-only observation does not constrain the opposite x layer:
its second coordinate is masked by that site's otherwise unobserved,
independent uniform z bit. A source-only observation supplies no check.
Integrating these private z bits out is exact and contributes a constant
likelihood independent of the x configuration.

Consequently, conditional on the masks, the posterior on the two x layers
is the product of two affine binary linear systems. In either Tanner copy,
each variable is unpinned with probability

    epsilon=(1-t)(1-s),

and each check is active with probability

    c=ts.

Variable masks in a Tanner copy lie on one physical layer and its check
masks on the other. Hence all its variable and check masks are mutually
independent. The two Tanner copies' masks are correlated with one another,
but this does not affect either marginal calculation.

The peeling characterization remains exact with inactive checks omitted.
An active check requires another surviving variable; an inactive check
places no condition. Thus, writing

    a(r)=1-c(1-r)^(d-1),

the variable-to-check survival probability is the greatest fixed point

    r=epsilon a(r)^(d-1).                              (6)

The greatest fixed point is obtained by decreasing iteration from r=1.
Finite peeling depths give the iterations by branch independence, and
their limit gives survival through every finite peeling depth. A surviving
variable can be flipped by the tree construction already given: at every
active incident check choose one other surviving variable and continue
outward. Thus survival is equivalent to one bit of posterior uncertainty,
not merely a necessary graph condition.

For d=3 this posterior has no jump. Indeed the derivative of the right
side of (6) is

    4 epsilon c (1-r)[1-c(1-r)^2] <= 4 epsilon c <= 1/4,

because epsilon c=t(1-t)s(1-s)<=1/16. This is a uniform contraction for
all achievable source and output densities. The structured degree-3
transition above therefore does not survive replacement by iid masks.

## Degree 64 produces a transition with iid masks

Take d=64 and any t in [2/5,3/5]. Put

    f_(t,s)(r)=(1-t)(1-s)[1-ts(1-r)^63]^63.

This is increasing in r and decreasing in s. Its greatest fixed point
r(t,s) is therefore decreasing in s.

At s=1/2 there is a fixed point greater than 1/10. To check this without
numerical computation, observe

    (9/10)^10 < 7/20,
    (9/10)^63 < (7/20)^4 < 1/50.

Since epsilon>=1/5 and c<=3/10 at s=1/2, Bernoulli's inequality gives

    f_(t,1/2)(1/10)
      > (1/5)[1-63(3/10)(1/50)]
      = 311/2500 > 1/10.

Also f_(t,1/2)(1)<1, so the intermediate value theorem gives the claimed
fixed point above 1/10.

For every s>=1/2 there is no fixed point in [1/512,1/128]. Indeed, for
r<=1/128, Bernoulli's inequality gives

    (1-r)^63 >= 65/128 > 1/2.

Here c>=1/5 and epsilon<=3/10. Consequently

    f_(t,s)(r) < (3/10)(9/10)^63
               < (3/10)(7/20)^5 < 1/512.              (7)

Finally, for s>=511/512 every fixed point is at most
epsilon<1/512. Monotonicity, the initial high fixed point, and the forbidden
interval in (7) force r(t,s) to jump from at least 1/128 to at most 1/512
at some s_*(t) strictly between 1/2 and 511/512. Strictness of the bounds
and continuity of f give room at both endpoints. One can define s_* as
the supremum of s for which r(t,s)>=1/128; the left and right limits give
the asserted jump. Thus the transition occurs for every t in an interval
of positive Lebesgue measure.

## The jump occurs in the actual row conditional entropy

The proposed row quantity excludes the root source pin. This changes the
root calculation but does not remove the transition. Use base-two entropy,
so h=2 for the alphabet F_2^2. Away from the root the masks are unchanged
and have cavity survival probability r=r(t,s). At the root:

* If its output is absent, its z bit remains independent uniform, and its
  unpinned x bit is free exactly when all d incident checks allow it. This
  gives conditional expected entropy 1+a(r)^d.
* If its output is present, x is known. The z bit equals the observed
  second output bit plus the opposite-layer root-check syndrome. That
  check is inactive because the root source pin was excluded. Removing
  it splits the Tanner tree into d independent branches, and its syndrome
  is free exactly when at least one branch is free. This gives conditional
  expected entropy 1-(1-r)^d.

The independence in the second item holds both for the mask law and for
the posterior on the separated branches; the original source law is
product and every retained constraint lies within one branch. Therefore
the exact row entropy is

    F(t,s)=1+(1-s)a(r)^d-s(1-r)^d.                     (8)

For 0<t,s<1 this expression is strictly increasing in r. Hence the cavity
jump gives an actual downward jump in F(t,s), rather than merely a jump
in an auxiliary graph statistic. Uniformly over t in [2/5,3/5], the jump
size is at least the positive constant

    eta=(1/2)[(511/512)^64-(127/128)^64] > 0.          (9)

The term -s(1-r)^64 alone gives this bound, since s_*>=1/2; the other
r-dependent term increases with r as well. Direct substitution into (8)
also gives F(t,0)=2 and F(t,1)=0, as required by the iid source and the
local decoder.

## Finite exhaustion authenticates the missing information mass

Here is the needed reveal inequality, with no smoothness assumption on an
infinite posterior. Let V have finite entropy, let C denote all side
information independent of the output-pin mask, and enumerate output
coordinates by increasing finite sets K_N. Define

    F_N(s)=E H(V | C,Y_(T_s intersect K_N)).

Finite-coordinate differentiation gives

    -F_N'(s)=sum_(k in K_N)
      E I(V;Y_k | C,Y_(T_s intersect (K_N minus {k}))).

Conditional-entropy martingale convergence gives F_N(s) down to F(s),
and convergence of each fixed k summand to its full infinite-coordinate
counterpart. All summands are nonnegative. Fatou's lemma, with a summand
set to zero before its coordinate enters K_N, therefore gives

    integral_a^b sum_k E I(V;Y_k | C,Y_(T_s minus {k})) ds
      <= F(a)-F(b).                                  (10)

In measure terms, the reveal density is dominated by the Stieltjes
decrease measure of F. Its integral cannot include an atomic jump of F.
For completeness, apply (10) on the two sides of a shrinking interval
around a jump. The reveal density is integrable by (10) on [0,1], so its
integral over that shrinking interval tends to zero. Passing to the
one-sided entropy limits leaves the jump size subtracted from the total
entropy decrease.

Apply this with V=X_1 and C=(source mask, X_(S_t minus {1})). Equations
(8)-(9) imply, for every t in [2/5,3/5],

    integral_0^1 sum_k m_ts(1,k) ds <= 2-eta < h.      (11)

This refutes (R), including its almost-every-t formulation, with fully iid
source and output masks and a bounded reversible decoder.

## A locally invertible recoding can strictly increase percolative entropy

Equality of percolative entropy under arbitrary local conjugacies is also
too strong. On the same degree-64 group G, now start with just one iid
uniform bit x per site and define

    Y(g,i)=(x(g,i),(Lx)(g,1-i)).                       (12)

This changes the alphabet from two symbols to four. The inverse on the
image is projection onto the first coordinate, so both directions are
local. In the Tanner posterior under iid output pins of density u,
epsilon=1-u and c=u. The variable and check masks again occupy opposite
physical layers and are independent within each Tanner copy. If r is the
greatest fixed point of (6) and a=1-u(1-r)^63, the exact root entropy is

    J(u)=E H(Y_1 | Y_(T_u minus {1}))
        =a^64+1-(1-r)^64.                            (13)

The first term is the unpinned root variable's entropy. The second is
the omitted opposite-layer check's syndrome entropy. Their posterior
entropies add because the two x-layer systems are independent conditional
on the masks and observations.

For every u<=3/5, the right side f_u of the cavity equation satisfies

    f_u(1/5)
      >= (2/5)[1-(3/5)(4/5)^63]^63
      > (2/5)[1-189/2560] > 1/5.

Here (4/5)^10<1/8 implies (4/5)^63<1/512, and Bernoulli's inequality
gives the middle bound. Hence the greatest fixed point r is at least
1/5 throughout that u interval. Another application of Bernoulli gives

    J(u) > 2-[64(3/5)+1]/512 = 4923/2560.

The remaining integrands are nonnegative, so

    integral_0^1 J(u) du
      > (3/5)(4923/2560)
      = 14769/12800 > 1.                             (14)

The source process has percolative entropy exactly one bit. Thus (12)
strictly increases this entropy despite its immediate local inverse.
This refutes an equality-based salvage, while remaining consistent with
the weaker conjectural lower bound needed for surjunctivity. Ordinary
coordinate-overlap recodings do not supply this countercontrol: their
information is merely replicated, and mass transport gives equality.

## What the controls permit and rule out

Bounded locality, a bounded inverse, finite dependence of the unconditioned
output, and positive additional source pinning do not individually or
together prohibit posterior phase transitions. The example even has a
reversible involution and preserves the uniform output process.

A viable information-transport proof of surjunctivity must compare missing
row and column contributions, or replace this invariant. Proving that all
such singular contributions vanish is false even for the reversible iid
control above. Since this involution exchanges the joint laws of source
and output, its integrated row and column deficits agree. That symmetry
explains why a failed row identity is compatible with surjunctivity here;
it does not establish the needed deficit comparison for an arbitrary
injective cellular automaton.

These are explicit adversarial controls for the proposed invariant; no
novelty claim is made for erasure-peeling phase transitions themselves.
For literature context, Austin and Podder's
[percolative-entropy paper](https://arxiv.org/abs/1705.03589) obtains its
entropy comparison from finite models, and obtains equality under strong
spatial mixing. Neither input is an unconditional lower-bound argument
for an arbitrary group here.

The [local deficit-measure control](gottschalk-row-column-deficit-measure-control-2026-09-08.md)
also rules out universal domination of the row and column singular
deficit measures on the pin-density square. Opposite signs occur on
transposed rectangles even for a reversible iid control. Their total
comparison remains exactly the unproved percolative-entropy lower
bound; the local counterexample does not decide that integrated sign.
