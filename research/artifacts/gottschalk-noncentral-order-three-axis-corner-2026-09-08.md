# Order-three quadratic feedback: an exact corner criterion

Date: 2026-09-08. Let t have order three in an arbitrary group G.
For scalar Boolean rules F(x)=x+A(xR_t x), this note proves an exact
direct-finiteness criterion when A preserves the subspace of
configurations constant on the right-t orbits g<t>. Neither centrality
of t nor preservation of the complementary subspace is needed.
When <t> is normal, the result covers every scalar linear A and the
criterion is direct finiteness of F_2[G/<t>].

For a nonnormal <t> and unrestricted A, the argument has a specific
gap: injectivity on the linear axis does not imply injectivity of
its compression back to that axis. An explicit finite-group example
below disproves that inference, even over a stably directly finite
group algebra. The example is itself noninjective and is not a
counterexample to Gottschalk's conjecture. No computation was used.

The later [norm-feedback rigidity theorem](gottschalk-noncentral-norm-feedback-rigidity-and-corner-equivalence-2026-09-08.md)
handles all feedback of the form A=aE without assuming it preserves
W. In that subclass, injectivity forces the corner compression to
be injective; when it is bijective, a finite-path argument forces
the off-axis part to vanish. Thus the whole norm subclass reduces
exactly to the corner, including when <t> is nonnormal. The gap for
arbitrary A with A(1-E) nonzero remains.

## Coordinates without centrality

Put R=F_2[G], write R_a x(g)=x(ga), and identify each group-ring
element with its scalar linear cellular automaton. Set

    T=R_t,       e=1+t+t^2,       E=I+T+T^2,
    W=im E,      V=ker E,         Q(x)=xTx.

Here e^2=e. The space W consists of configurations constant on each
right-t orbit g<t>, while V consists of configurations of even
parity on each such triple. Both are compact G-invariant subspaces,
and every configuration has unique coordinates x=d+c with d in V
and c in W. They are coset-constrained subshifts; we do not identify
either one with an unconstrained full G shift.

For d in V put N(d)=E Q(d), a repeated bit on each triple. The four
even-parity triples give, with T acting by forward cyclic shift,

| d | Q(d) | N(d) | T^2 d |
| --- | --- | --- | --- |
| 000 | 000 | 0 | 000 |
| 110 | 100 | 1 | 011 |
| 101 | 001 | 1 | 110 |
| 011 | 010 | 1 | 101 |

Consequently Q(d)=N(d)+T^2d and N(d)T^2d=T^2d. Define the local
G-equivariant involution

    Psi(d,m)=d+m+N(d),       d in V, m in W.

This is the map Psi(x)=(I-E)x+E Q(x) on the original configuration
space. It fixes the V coordinate and adds N(d) to the W coordinate,
so Psi^2=I. Expanding Q(d+c), with c=m+N(d), yields the exact identity

    Q Psi(d,m)=m+mT^2d.                               (1)

The product mT^2d belongs to V because m is constant on each triple.
All these facts use only t^3=1, not centrality or normality.

Let A have group-ring coefficient a. The map P=F_A Psi, where
F_A(x)=x+A Q(x), therefore has the following exact output coordinates:

    d' = d+(I-E)A m+(I-E)A(mT^2d),
    c' = N(d)+(E+EAE)m+EA(mT^2d).                    (2)

In particular the zero-d axis maps by the full linear inclusion
m -> (I+A)m. Its W compression is E(I+A)E; these are different maps
unless the V component (I-E)AE vanishes.

## Exact theorem for feedback preserving W

For fixed G and t of order three, the following are equivalent:

1. The unital corner ring eRe, with identity e, is directly finite.
2. Every injective F_A=x+A Q with

       (1-e)ae=0                                     (3)

   is surjective.

Condition (3) says exactly A(W) is contained in W. It does not require
A(V) to be contained in V and does not require A to commute with T.

We first record the relevant linear duality. Under the pairing
<f,x>=sum_g f_g x(g), a scalar operator with coefficient b is dual
to right multiplication f -> fb. The continuous F_2-linear dual of W
is the left ideal Re: indeed W is the image of the dual of f -> fe, and
R/R(1-e) identifies with Re. Hence for b in eRe the operator B_b on
W is dual to

    rho_b: Re -> Re,       f -> fb.

B_b is injective exactly when rho_b is surjective. In that case
choose c in Re with cb=e and replace c by ec. Then c belongs to
eRe and still cb=e. If eRe is directly finite, bc=e as well, so
rho_b and B_b are bijective. Conversely a one-sided inverse pair
in eRe gives a one-sided inverse pair of the operators on W. This
action is faithful: if b acts as zero on W, then right multiplication
by b on Re is zero, and evaluating at e gives b=0.

Assume now eRe directly finite and F_A injective under (3). Formula
(2) becomes

    P(d,m)=(L_m d, V_2(d,m)),
    L_m d=d+(I-E)A(mT^2d),
    V_2(d,m)=N(d)+B_0m+EA(mT^2d),
    B_0=e+eae acting on W.                           (4)

For each fixed m, L_m is homogeneous F_2-linear in d, and L_0=I.
The restriction P(0,m)=(0,B_0m) is injective. The preceding corner
duality therefore makes B_0 bijective.

We give the two-block elimination proof on these constrained coset
spaces explicitly. If L_m d=0, choose m' with
B_0m'=V_2(d,m). Then P(d,m)=P(0,m'), so injectivity forces d=0.
Every L_m is consequently injective, and

    J(d,m)=(L_m d,m)

is a local injective map from V x W to itself. When m has finite
support, L_m differs from identity at only finitely many output
sites, independently of d. Enlarge that set to a finite union S of
whole right-t triples. For any fixed exterior configuration in V,
L_m injectively maps its finite set of fillings on S to itself.
Each triple has four possible even-parity fillings, so this map is
bijective. It follows that L_m is onto for every finitely supported m.

Finitely supported points are dense in W: retain a configuration on
finitely many whole triples and set it to zero elsewhere. Thus the
compact image of J contains a dense subset of V x W, making J
bijective. Its inverse is continuous and G-equivariant. Compactness
provides a finite determining set for each output coordinate at the
identity; equivariance translates it everywhere. Hence J^-1 is
uniformly local on V x W, despite the coset constraints.

Define D=P J^-1. This local injective map preserves its first
coordinate d. On the zero-d fiber it is B_0, since L_m^-1(0)=0.
For a fixed finitely supported d, locality shows that the fiber map
D_d:W -> W differs from B_0 at only finitely many output sites,
with a set independent of m. Therefore D_d B_0^-1 is an injective
finite-output perturbation of identity on W. Enlarging its affected
set to finitely many whole triples, each with two possible W
fillings, proves it bijective by the same finite-set argument.

The image of D now contains every point with finitely supported d
and arbitrary m. Such d are dense in V by the same whole-triple
truncation. Compactness makes D onto, and consequently P and F_A
are onto. No step changes only part of a constrained triple.

For the converse, let b,c in eRe satisfy cb=e and choose a=b-e.
This a satisfies (3), kills V, and maps into W. Formula (1) gives
the exact conjugacy

    Psi F_A Psi=(I-E)+B_b.                           (5)

Indeed a annihilates mT^2d in (1); the W output before the last
Psi is N(d)+bm, and the last Psi cancels N(d). The right side of
(5) is identity on V and B_b on W. It has left inverse
(I-E)+B_c, so F_A is injective. Assertion 2 makes it surjective.
A surjective map with a left inverse has that same right inverse;
hence B_b B_c=I on W, and faithfulness gives bc=e. This proves the
equivalence.

## Consequences for the ambient ring and for normal subgroups

If R is directly finite, so is eRe. To see this, a pair cb=e in
eRe gives

    (c+1-e)(b+1-e)=1

in R. Reversing this product by direct finiteness gives bc=e.
Thus direct finiteness of F_2[G] suffices for every feedback satisfying
(3); stable direct finiteness is not needed for this conclusion.

If H=<t> is normal in G, the sum e of its elements is central.
Every a then satisfies (3), and

    eF_2[G]e is isomorphic to F_2[G/H].               (6)

Explicitly, the quotient basis element gH maps to ge. This is
well-defined because he=e for h in H; distinct cosets have disjoint
supports, and centrality of e makes multiplication agree. These ge
span the corner. Consequently, for any normal subgroup H of order
three,

    every injective scalar F=x+A(xR_t x) on G is onto
       iff F_2[G/H] is directly finite.              (7)

Here t need not be central. For example, the statement applies to
C_3 semidirect Gamma even when some elements of Gamma invert t.
For central direct products it recovers the full C_3 equivalence in
[the central-cycle artifact](gottschalk-central-odd-norm-conjugacy-direct-finiteness-2026-09-08.md).

## A finite obstruction to the unrestricted compression step

For a nonnormal H, injectivity of the full axis map (I+A)|W does
not imply injectivity of E(I+A)|W. This remains false when every
matrix ring over F_2[G] is directly finite.

Take the group of order 18

    G=(<a> x <b>) semidirect <sigma>,
    a^3=b^3=sigma^2=1,       ab=ba,
    sigma a sigma=b,

and put t=a, H=<a>, A=R_sigma-I. Then (I+A)|W is the restriction
of the invertible shift R_sigma, so it is injective. Write
E_a=I+R_a+R_a^2 and E_b=I+R_b+R_b^2. With q=1_H, set

    m=1_H+1_(Hb)=q+R_(b^-1)q.

This m is nonzero and E_a m=m. Every b-orbit in <a,b> meets its
support in two points, and every other b-orbit meets it in zero
points, so E_bm=0. Since a sigma=sigma b,

    E_a R_sigma=R_sigma E_b,
    E_a(I+A)E_a m=R_sigma E_bm=0.

Thus the compressed map has a nonzero kernel. The group algebra
and all its matrix rings are finite-dimensional over F_2, so all
are directly finite: left inverses of finite-dimensional linear
operators are right inverses. Stable direct finiteness therefore
does not repair this particular compression inference.

The associated nonlinear F is itself noninjective. Indeed Q(q)=q
and F(q)=R_sigma q. The supports of R_sigma q and T R_sigma q are
disjoint, since sigma^-1 a sigma=b does not belong to H. Therefore
Q(R_sigma q)=0 and

    F(q)=R_sigma q=F(R_sigma q),       q != R_sigma q.

This is a control for the failed intermediate inference, not a
counterexample under the full hypothesis that F is injective.

## What remains open in this argument

For arbitrary A with (1-e)ae nonzero, the first line of (2) contains
the additive axis term (I-E)Am. Its removal requires information
about the full linear inclusion (I+A)|W, rather than its W
compression alone. The proof above neither supplies such a
straightening nor rules out a different one using full nonlinear
injectivity. In particular it does not decide whether direct
finiteness, or stable direct finiteness, of F_2[G] suffices for the
unrestricted family when <t> is nonnormal.
