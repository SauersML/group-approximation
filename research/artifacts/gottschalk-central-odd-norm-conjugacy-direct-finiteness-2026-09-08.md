# Central C3 quadratic feedback and characteristic-two direct finiteness

Date: 2026-09-08. For each fixed group Gamma, the following assertions
are equivalent: F_2[Gamma] is directly finite; every injective scalar
Boolean cellular automaton F=x+A(xR_t x) on Gamma x C_3, with arbitrary
scalar linear feedback A and t generating the central C_3, is onto.
The full three-cycle proof uses an explicit local involution and
two-block elimination. A norm subclass works for every odd cycle and
is reversibly conjugate to arbitrary scalar linear dynamics together
with unchanged coordinates.

These are equivalences and reductions, not a proof of direct finiteness.
The unrestricted-feedback sufficiency theorem is proved here for C_3;
the general odd-cycle argument concerns the norm subclass. No claim
about direct finiteness over all characteristics is made. No computation
was used.

## The central norm family

Let Gamma be any group, let n>=3 be odd, and put

    G=Gamma x C_n,       C_n=<t>.

Write R_a x(g)=x(ga), T=R_t, and Q_t(x)=xTx on F_2^G. Define

    E=I+T+...+T^(n-1).

Since n is odd, E^2=E. Its image consists exactly of configurations
constant on the C_n coordinate, canonically identified with F_2^Gamma.
Every configuration has a unique decomposition

    x=d+c,       c=Ex,       d=(I-E)x,       Ed=0.

Here c records the parity of each cyclic block and repeats it on that
block. All additions and subtractions below are in characteristic two.

Let B be any scalar F_2-linear cellular automaton on F_2^Gamma. Use
the same notation for its lift to F_2^G acting independently on each
C_n coordinate. This lift commutes with T and E. Set

    A_B=(B-I)E,
    F_B(x)=x+A_B Q_t(x).                               (1)

Thus F_B belongs to the unrestricted linear-feedback family
x+A Q_t(x). It need not belong to the earlier two-term subfamily
with A=(I+R_u)R_s.

## An explicit local involution

For t-invariant c, expansion of the quadratic product gives

    Q_t(c+d)=c+c(d+Td)+dTd.

Applying E cancels the cross term, because E(d+Td)=0, and E(c)=c.
Consequently, if h(d)=E Q_t(d),

    E Q_t(c+d)=c+h(d).                                 (2)

Define the local cellular automaton

    Psi(x)=(I-E)x+E Q_t(x).                            (3)

In the decomposition x=d+c it has the simple form

    Psi(d,c)=(d,c+h(d)).

The first coordinate is unchanged, and adding h(d) twice cancels.
Therefore Psi^2=I: this is an explicit reversible local change of
coordinates, independent of B. Its locality follows directly from
the finite orbit defining E and the two-site rule Q_t.

## Exact conjugacy

Formula (2) gives

    F_B(d,c)=(d,Bc+(B-I)h(d)).

Conjugating by Psi cancels the offset:

    Psi F_B Psi(d,c)=(d,Bc).

Equivalently, as cellular automata on F_2^G,

    Psi F_B Psi=(I-E)+BE.                              (4)

The right side acts as identity on ker E and as B on im E. Hence

    F_B is injective  iff  B is injective;
    F_B is surjective iff  B is surjective.            (5)

For example, a missing value of B gives a missing target in (4)
with d=0; the unchanged d coordinate cannot supply another preimage.
Conversely, when B is onto, choose its preimage independently for
the c coordinate while retaining the desired d.

Thus the finite cyclic nonlinearity supplies no automatic positive
resolution of the unrestricted family: within this norm subclass,
the injectivity-versus-surjectivity question is exactly the arbitrary
scalar linear question on Gamma.

## Composition and explicit decoder identities

Write L_B=(I-E)+BE. Since the lifted linear maps commute with E,

    L_B L_C=(I-E)+(BC)E=L_(BC).

The conjugacy uses the same Psi for every B, so

    F_B F_C=F_(BC),       F_I=I.                       (6)

In particular, if CB=I, then F_C F_B=I. If BC=I as well, F_C is
the two-sided inverse of F_B. More generally, a one-sided linear
decoder gives the corresponding explicit quadratic decoder through
formula (1).

This construction is faithful to B: on t-invariant configurations,
Q_t(c)=c and E(c)=c, so F_B(c)=Bc. Therefore F_D=I holds exactly
when D=I. A failed reverse product of linear maps remains a failed
reverse product of the quadratic maps in (6).

## The explicit three-cycle control

For n=3, write a cyclic block as (x_0,x_1,x_2). Its norm of Q_t is
the repeated bit

    m(x)=x_0x_1+x_1x_2+x_2x_0.

Over Boolean inputs this is the majority bit. The involution Psi
fixes 000 and 111, and swaps each weight-one triple with its
complementary weight-two triple:

    100 <-> 011,       010 <-> 101,       001 <-> 110.

Thus a nonlinear reversible block map changes the parity coordinate
into the majority coordinate while retaining the other coordinates
in ker E. In these terms,

    F_B(x)(g,i)=x(g,i)+(B-I)m(x)(g).

As a positive control, take B=R_h for any h in Gamma. Then

    F_B(x)(g,i)=x(g,i)+m(x)(gh)+m(x)(g),

and its explicit inverse is F_(R_(h^-1)). This shows why a universal
noninjectivity claim for the quadratic norm family would be false.
It does not require any assumption about surjunctivity of Gamma.

## The full central three-cycle equivalence

For a fixed group Gamma, let G=Gamma x C_3 and allow A to be any
scalar F_2-linear cellular automaton on F_2^G. Then

    every injective F_A(x)=x+A Q_t(x) is surjective
       iff F_2[Gamma] is directly finite.              (7)

Necessity follows from the norm subclass (1), (5), and the scalar
linear duality proved below. We now prove sufficiency for all A,
not merely those of the form (B-I)E.

Retain E=I+T+T^2. On the even-parity block d, put N(d)=E Q_t(d),
viewed as one repeated bit. With T(d_0,d_1,d_2)=(d_1,d_2,d_0),
the four possible blocks give

| d | Q_t(d) | N(d) | (I-E)Q_t(d)=T^2d |
| --- | --- | --- | --- |
| 000 | 000 | 0 | 000 |
| 110 | 100 | 1 | 011 |
| 101 | 001 | 1 | 110 |
| 011 | 010 | 1 | 101 |

In particular N(d)d=d. Since Ed=0 also gives d+Td=T^2d, the
involution Psi from (3), written as Psi(d,m)=(d,m+N(d)), satisfies

    Q_t Psi(d,m)=m+mT^2d.                              (8)

For example, expand Q_t(d+c)=Q_t(d)+c(d+Td)+c with c=m+N(d).
Using Q_t(d)=N(d)+T^2d and N(d)T^2d=T^2d leaves precisely (8).
The invariant bit m is distinct from the input's original parity
coordinate after Psi has been applied.

Because t is central, A commutes with T and E. Its restrictions are
a scalar Gamma-linear CA A_0 on im E and a linear Gamma-CA A_1 on
the two-dimensional even-parity block. Multiplication by the repeated
bit m preserves that even block. Consequently P=F_A Psi has coordinates

    P(d,m)=(L_m d, N(d)+B_0m),
    L_m d=d+A_1(mT^2d),       B_0=I+A_0.               (9)

For each fixed m, L_m is homogeneous F_2-linear in d, and L_0=I.
If F_A is injective, so is P, and its restriction at d=0 shows that
the scalar linear map B_0 is injective. Assume F_2[Gamma] directly
finite. Scalar linear duality then makes B_0 bijective.

Here is a self-contained two-block elimination argument, allowing
the unrestricted second output in (9). If L_m d=0, choose m' with
B_0m'=N(d)+B_0m. Then P(d,m)=P(0,m'), so injectivity forces d=0.
Thus every L_m is injective, and the local map

    J(d,m)=(L_m d,m)

is injective. For finitely supported m, the map L_m differs from
identity at only finitely many Gamma output sites, independently of
d. An injective map with this property is bijective: for each fixed
exterior configuration, it permutes the finite set of possible
fillings of those sites. The image of J therefore contains every
point with finitely supported m and arbitrary d. Density and compactness
make J bijective on the whole product shift.

Its inverse is uniformly local as a Gamma map. Indeed, a continuous
equivariant inverse on a compact finite-alphabet shift has a finite
determining set at the identity, and equivariance translates that
set to all output sites. Define D=P J^-1. This local injective map
preserves d, and its zero-d fiber is B_0, because L_m is injective.
For fixed finitely supported d, the map D_d on the m fiber differs
from B_0 at only finitely many output sites, with the affected set
independent of m. Hence D_d B_0^-1 is an injective finite-output
perturbation of identity, and the same finite-filling argument makes
it bijective. Thus D attains every target with finitely supported d
and arbitrary m. Density and compactness prove that D, then P and
F_A, are surjective.

This completes the sufficiency direction of (7). The argument does
not assume that the second output N(d)+B_0m is homogeneous in m;
it uses only its bijective zero-d restriction, locality, and the
homogeneous first block with L_0=I.

## Scalar linear duality and direct finiteness

Let R=F_2[Gamma], the vector space of finitely supported functions
on Gamma with group-ring multiplication. For b=sum_h b_h h in R,
the associated scalar linear cellular automaton is

    B_b x(g)=sum_h b_h x(gh).

Identify all configurations with the full algebraic dual of R using
the pairing <f,x>=sum_g f_g x(g). Direct expansion shows

    <f,B_b x>=<fb,x>.

Thus B_b is the dual of right multiplication

    rho_b:R -> R,       rho_b(f)=fb.

For linear maps, the dual is injective exactly when the original
map is surjective, by the existence of a nonzero functional on a
nonzero quotient. The dual is surjective exactly when the original
map is injective, by extending linear functionals from its image.
It follows that

    B_b injective  iff  rho_b surjective
                    iff some a in R satisfies ab=1;
    B_b surjective iff  rho_b injective.              (10)

Direct finiteness of R means precisely that ab=1 implies ba=1.
If R is directly finite and B_b is injective, choose a with ab=1.
Then ba=1, and fb=0 implies f=fba=0. Thus rho_b is injective,
and B_b is surjective.

Conversely, suppose every injective scalar linear CA on Gamma is
surjective. Given ab=1, equation (10) makes B_b injective and then
surjective, so rho_b is injective. But

    (ba-1)b=bab-b=0.

Therefore ba=1. This proves the exact equivalence, for each Gamma,

    F_2[Gamma] directly finite
       iff every injective scalar linear CA on Gamma is onto
       iff every injective F_B in (1) is onto.        (11)

For a hypothetical one-sided inverse ab=1 with ba!=1, (6) would give

    F_(B_a) F_(B_b)=I,
    F_(B_b) F_(B_a)=F_(B_(ba))!=I,

and F_(B_b) would be injective but nonsurjective. This is a conditional
translation of such a pair, not a construction or existence assertion.

A positive theorem for x+A Q_t(x), arbitrary linear A, even with
t a central element of order three, would therefore settle direct
finiteness of every F_2 group algebra. The implication is expressly
in characteristic two; no all-characteristic conclusion follows
from this argument alone.

## Encoding arbitrary matrix linear rules in a scalar block

The same scalar quadratic norm family also contains arbitrary
finite-track linear surjunctivity problems, after a finite group
factor is added. The following elementary block construction gives
the exact encoding, including its multiplicity.

Present S_3 as <a,b | a^3=b^2=1, bab=a^2>, and put e=a+a^2 in
F_2[S_3]. Then e^2=e, and e is central: conjugation by b exchanges
a and a^2. The ideal eF_2[S_3] has dimension four. Indeed,
eF_2[<a>] has dimension two, and its translate by b has disjoint
group-basis support and contributes another two dimensions.

On F_4, choose omega with omega^2+omega+1=0 and represent

    a(z)=omega z,       b(z)=z^2.

These F_2-linear maps satisfy the S_3 relations, and e acts as
identity. The operators z -> lambda z+mu z^2, for lambda,mu in F_4,
are linearly distinct: vanishing at z=1 gives lambda=mu, and then
vanishing at z=omega gives lambda=0. They span the four-dimensional
endomorphism algebra of the two-dimensional F_2-space F_4. Thus

    eF_2[S_3] is isomorphic to M_2(F_2).

Take K=S_3^k, m=2^k, and epsilon=e tensor ... tensor e. Tensoring
the preceding isomorphism gives a central block

    epsilon F_2[K] is isomorphic to M_m(F_2).          (12)

Now let B be a d-track F_2-linear CA on Gamma. Choose k with m>=d
and pad B to the m-track rule B'=diag(B,I_(m-d)). Embed each matrix
coefficient of B' through (12), and add identity on the complementary
central ideal (1-epsilon)F_2[K]. This defines a scalar linear CA
C_B on Gamma x K.

Here is the explicit module interpretation. Identify the K-track
space F_2^K with F_2[K] by sending the coordinate vector at h to
h^-1. Then a right shift R_k becomes left multiplication by k:
substituting y=hk in the defining sum gives this identity directly.
On the epsilon block, left multiplication by an m-by-m matrix acts
independently on each of the m columns of M_m(F_2). The complementary
ideal carries identity. Therefore, as a Gamma cellular automaton,

    C_B is linearly conjugate to m independent copies of B
    together with 6^k-md identity binary tracks.       (13)

The identity-track count includes m(m-d) padding coordinates and
the 6^k-m^2-dimensional complementary ideal. Equation (13) proves
that C_B is injective exactly when B is injective, and surjective
exactly when B is surjective; no transpose or opposite-ring change
is hidden in the construction.

Apply the central three-cycle norm construction to C_B over
(Gamma x K) x C_3. By (5), the resulting scalar Boolean quadratic
rule has exactly the same injectivity and surjectivity status as
the original matrix rule B. The construction is multiplicative
for fixed d and padding size: the central block multiplies padded
matrices and the complement remains identity, so (6) also transports
matrix decoder pairs.

For completeness, the corresponding matrix dual acts on finitely
supported row vectors by v -> vB over F_2[Gamma]. Its surjectivity
is equivalent to a matrix C with CB=I; its injectivity then forces
BC=I by applying it to BC-I. Thus the matrix version is the stable
direct-finiteness question for F_2[Gamma]. This extension remains
entirely in characteristic two and does not assert that a one-sided
inverse pair without a reverse inverse exists.
