# Unrestricted order-three feedback: odd-parity collisions

Date: 2026-09-08. Let t have order three in an arbitrary group G,
and consider every scalar Boolean rule

    F(x)=x+A Q_t(x),       Q_t(x)=xR_t x,

with A an arbitrary scalar linear cellular automaton. This note
proves the following restrictions, including for A(1-E) nonzero:

- An exact criterion detects every collision whose two inputs have
  odd parity on every right-t orbit.
- If EAE=0, injectivity forces AE=0. Consequently every injective
  rule in this subfamily is surjective, on any G and without a
  direct-finiteness assumption.
- On G=A_4 with t a three-cycle, injectivity always forces
  (I-E)AE=0. An explicit collision excludes every other feedback.

Here E=I+R_t+R_t^2. The A_4 result is a structural restriction on
possible reversible controls; finiteness already makes any injective
map on that group surjective. The unrestricted problem on other
groups remains open in this argument. No computation is used in
any proof below.

## Coordinates and block support

Put T=R_t, W=im E and V=ker E. The blocks are the right-t orbits
g<t>, each containing three sites. W consists of one repeated bit
per block; V consists of the four even-parity triples per block.
For d in V put N(d)=E Q_t(d). On a block, N is zero at 000 and
one at every other even-parity state. Directly,

    Q_t(1+d)=1+N(d),       d in V,                   (1)
    v+Tv=T^2v,            v in V.

In particular N(Tv)=N(T^2v). For a nonzero V block v, the norm
derivative N(d+v)+N(d) is one at d=0,v and zero at the other
two states. For v=0 it is always zero.

Define K=(I-E)AE:W -> V. In this note, the support of a W or V
configuration at the block level means the blocks on which it is
nonzero. It is not the support of individual sites: an active W
block is 111, while a nonzero V block has only two ones.

## Exact collision criterion on the odd-parity subshift

The restriction of F to {x:Ex=1} is noninjective if and only if
there is a nonzero q in W such that

    EAq=0,
    q_i=1 implies (Kq)_i != 0 on every block i.       (2)

This criterion does not require any augmentation assumption on A.
Under (2), put

    v=Kq=Aq,
    d=(1+q)Tv,
    x=1+d.                                          (3)

These give an explicit collision between x and x+v. On an active
q block, d=0 and v is nonzero, so the norm derivative is one.
On an inactive block, d=Tv and d+v=T^2v, whose norms agree.
Therefore

    N(d+v)+N(d)=q.

Both inputs have odd parity, and (1) gives

    Q_t(x+v)+Q_t(x)=q,
    F(x+v)+F(x)=v+Aq=0.

They are distinct because q is nonzero and v is nonzero on its
active blocks.

Conversely, write two distinct odd-parity inputs as 1+d and 1+d'
and set v=d+d' in V and q=N(d)+N(d') in W. Equality of their
outputs implies v=Aq. Thus EAq=0 and v=Kq. If q were zero,
then v would be zero, contrary to distinctness. On any block
where q_i=1, the inputs' norms differ, so v_i is nonzero. This
proves (2) is also necessary for a collision on this subshift.

Separately, global injectivity of F forces the augmentation of its
coefficient a in F_2[G] to be zero: F(0)=0, while
F(1)=(1+aug(a))1. This observation will be used for A_4 below.

## Zero compression forces zero action on W

Suppose EAE=0 and F is injective. We prove AE=0 for arbitrary G.
Since A1 is constant and E fixes constant configurations,
EAE=0 implies A1=0. In this case K=AE maps W into V, and (1)
shows that F preserves the odd-parity subshift and acts there as

    F(1+d)=1+R_K(d),
    R_K(d)=d+K N(d),       d in V.                   (4)

Hence R_K:V -> V is injective, continuous and G-equivariant.

Construct a directed graph on the t-blocks by placing an edge
j -> i when the coefficient K_ij:F_2 -> V_i is nonzero. This
graph has finite propagation and is G-invariant, and G acts
transitively on its vertices.

A shortest directed cycle gives an exact collision. Indeed, there
are no additional edges between its vertices: a chord would
produce a shorter directed cycle, and a loop would itself have
length one. If q is the indicator of that cycle, then each active
row (Kq)_i has exactly its one nonzero predecessor contribution.
Thus (2) holds; EAq=0 is automatic here. This contradicts
injectivity. Consequently the graph is acyclic.

If it nevertheless had an edge, transitivity would give each
vertex an incoming edge. A fixed terminal block i_0 would have
infinitely many distinct ancestors, obtained by repeatedly choosing
a predecessor; repetition would make a directed cycle.

The inverse of R_K on its compact image is continuous. Let S be
a finite set of output sites determining the entire input triple
at i_0 under this inverse. Since K is local, only finitely many
input W blocks can influence its output at sites in S. Choose an
ancestor block i_* outside this finite collection and distinct
from i_0, and choose a shortest directed path from i_* to i_0.
No finite-generation or metric assumption on G is needed.

The induced graph on this path consists only of its consecutive
forward edges: a forward chord would shorten it and a backward
chord would create a cycle. Let q be its vertex indicator and
v=Kq. At every active block except i_*, the vector v_i is nonzero;
at i_* it is zero. With d=(1+q)Tv, the block derivative facts give

    N(d+v)+N(d)=q+1_(i_*).

It follows from (4) that

    R_K(d+v)+R_K(d)=K 1_(i_*).                       (5)

By the choice of i_*, the right side vanishes on S. The input
difference v is nonzero on the terminal block i_0, however. This
contradicts the determining property of S. Thus the graph has no
edges, K=0, and AE=0 as claimed.

This also proves a positive statement about the whole subfamily:

    EAE=0 and F injective imply F surjective.         (6)

Indeed AE=0 makes the zero-d map in the Psi coordinates the
identity on W. The first output is homogeneous linear in d at
fixed m, with the identity at m=0. The compact two-block
elimination proof in
[the corner theorem](gottschalk-noncentral-order-three-axis-corner-2026-09-08.md)
then applies with B=I. That proof requires a bijective B for the
individual rule; here no ring hypothesis is needed to obtain it.

## Every injective A_4 feedback preserves W

Now let G=A_4, let t be a three-cycle, put H=<t>, and write
e=1+t+t^2 in F_2[G]. Let a be the coefficient of A. We prove

    F injective implies (1-e)ae=0                    (7)

for every a, including those with a(1-e) nonzero.

The action of A_4 on the four cosets gH is its usual action on
four points. It is 2-transitive: a point stabilizer H cyclically
permutes the other three points. There are two H double cosets,
namely H and G minus H. Put D=sum_(g outside H) g. For g in H,
ege=e. For g outside H, the subgroups H and gHg^-1 are distinct
order-three subgroups with trivial intersection. All nine terms
in ege are consequently distinct and fill G minus H, so ege=D.
Thus

    eae=alpha e+beta D.

If F is injective, aug(a)=0. Since both e and D have augmentation
one, alpha=beta, giving

    eae=lambda Omega,
    Omega=sum_(g in G) g.                            (8)

Consider K=(I-E)AE:W -> V on the four t-blocks. Its diagonal
coefficient K_ii is zero. To see this, the stabilizer of block i
fixes its W input bit but cyclically rotates its V output triple.
There is no nonzero fixed vector in an even-parity triple: a fixed
triple is constant, and 111 has odd parity. Equivariance therefore
forces K_ii=0.

If K is nonzero, some off-diagonal coefficient is nonzero.
2-transitivity and equivariance then make every off-diagonal
coefficient nonzero. Choose q to be the W indicator of any two
blocks. The total number of ones in q is six, so Omega q=0.
Equation (8) gives EAq=0. On each of its two active blocks,
(Kq)_i is exactly the nonzero contribution from the other active
block; the diagonal contribution vanishes. Thus (2) holds and
(3) constructs a collision, contradicting injectivity. This proves
(7).

In particular A_4 cannot provide a finite reversible control with
(I-E)AE nonzero. This conclusion uses the two-double-coset and
2-transitivity properties just proved; neither is assumed for a
general nonnormal order-three subgroup.

## A further constraint using the non-norm feedback

For any fixed parity configuration c in W, define the full linear
map from V into F_2^G

    L_c(v)=v+A((1+c)T^2v).

If F is injective, every L_c is injective. Indeed, take a nonzero
v in its kernel and put d=Tv. Then N(d+v)=N(d), since d+v=T^2v.
The identity

    Q_t(c+d)=c+N(d)+(1+c)T^2d

shows that c+d and c+d+v have the same F output. This contradicts
injectivity. The map L_c is an inclusion into the whole output
space; this argument does not justify compressing it to V or to W.
It supplies a constraint on A(1-E), while leaving the unrestricted
noncentral case beyond the proved subfamilies unresolved.

## What straightening a bijective B actually gives

For general A, suppose the compression B=(E+EAE)|W is bijective.
Use the reversible coordinates Psi(d,m)=d+m+N(d), and set

    K=(I-E)AE:W -> V,
    C=(I-E)A|V:V -> V,
    D=EA|V:V -> W,
    M=KB^-1:W -> V.

Since mT^2d belongs to V, the exact map P=F Psi is

    P(d,m)=(d+Km+C(mT^2d),
            N(d)+Bm+D(mT^2d)).                       (8)

The inverse of B is uniformly local on W by compactness and
equivariance. The local linear output shear

    S(u,c)=(u+Mc,c)

is an involution. Applying it to (8) cancels Km, but yields

    SP(d,m)=(R(d)+(C+MD)(mT^2d),
             N(d)+Bm+D(mT^2d)),
    R(d)=d+M N(d).                                   (9)

Thus the straightened first output has a nonlinear base term R(d).
If F is injective, one rigorous consequence is

    R^-1(0)={0}.                                    (10)

Indeed, if R(d)=0, then

    SP(d,0)=(0,N(d))=SP(0,B^-1N(d)),

so injectivity forces d=0. This does not establish injectivity of
R on all pairs. In fact the restriction SP(d,0)=(R(d),N(d)) is
automatically injective for every M: its two coordinates recover
d=R(d)+MN(d). Therefore injectivity of that restriction alone
cannot supply the missing injectivity statement for R. The
norm-feedback graph argument requires that stronger statement
and cannot be applied to the first coordinate of (9) on this basis.

## A two-track control shows why scalarity matters

The implication from bijective B and injective F to K=0 is false
for general matrix feedback, even on finite groups. Take two
independent Boolean tracks, apply Q_t separately to them, and use

    A_tilde = [[0, R_h], [0, 0]].

Then

    F_tilde(x,y)=(x+R_h Q_t(y),y)

is an involution. With E_tilde=diag(E,E), its W-coordinate
compression is the involutive unit

    B_tilde = [[I_W, ER_h|W], [0, I_W]],

while its off-axis component has the single potentially nonzero
entry

    (K_tilde)_12=(I-E)R_h|W.

This entry is nonzero when h does not normalize H=<t>. For a
fully explicit finite example, take

    G=(<a> x <b>) semidirect <sigma>,
    a^3=b^3=sigma^2=1,       ab=ba,
    sigma a sigma=b,
    t=a,       h=sigma.

In the group algebra, with e=1+a+a^2,

    (1-e)sigma e=(a+a^2)(1+b+b^2)sigma != 0.

The six terms are distinct, so K_tilde is indeed nonzero.

This control preserves locality and G-equivariance, but the
collection of scalar t-blocks has two separate track orbits, with
feedback directed only from the second track into the first.
It is not a scalar counterexample. In particular, a matrix-corner
argument that forgets this distinction cannot establish scalar
axis rigidity from the remaining hypotheses alone. A linear
group-algebra matrix-block isomorphism also does not by itself
identify the pointwise products used to define Q_t, so it does
not automatically turn this two-track control into a scalar one.
