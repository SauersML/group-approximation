# A two-term linear code extension and its explicit complement collision

Date: 2026-09-08. Adjoining one controlled symmetry to the group
of the infinite scalar-code construction makes its reversible
code map extend to a scalar rule of the exact form x+B Q_s,
with B the sum of two right translations. An explicit pair of
complementary configurations proves that this extension is not
injective on the full shift.

This establishes linear-span membership after the stated group
enlargement. It does not establish membership for the original
group, uniqueness of the extension, or an injective full-shift
extension. Other coefficients, including linear operators that
vanish on Q_s of the code, remain possible correction directions.
No computation or resolution of Gottschalk's conjecture is claimed.

The source, observable, original group Lambda, and invariant code
are defined in
[the infinite-code construction](gottschalk-balanced-triangular-invariant-scalar-code-construction-2026-09-08.md).
We restate the ingredients needed for the exact calculation.

## A controlled source symmetry isolates the desired linear term

Let G_0=A_4, t=(123), h=(12)(34), and A=I+R_h. The source
X=D^N has finite component alphabet D=(F_2^{G_0})^2. Write
z_i=(x_i,y_i), u=(1,1), and c_i=1_{z_i=u}. The operations Q
and F_A act componentwise, with

    Q(x,y)=(Q_t(x),Q_t(y)),
    F_A(x,y)=(x+A Q_t(y),y).

Both preserve all masks c_i. The original observable is

    phi(z)=x_0(1)  if z_1=u;
           y_1(1)  if z_1!=u and z_0=u;
           1       otherwise.

Let H=H_0 be the prefix homeomorphism

    UU->UU,       UZU->UZ,       UZZ->ZZ,       Z->ZU,

where U denotes u and Z a component other than u. Let P swap
components 0 and 1, and put a=P H. Both a and a^-1 belong to
the original symmetry group Lambda. If

    X_i=1+x_i(1),       Y_i=1+y_i(1),

then the translated observable psi=phi composed with a satisfies

    psi(z)=1+Y_0+c_0 c_2 X_1.                      (1)

Indeed the source prefixes UU, UZU, UZZ, and Z give respectively
the values 1, x_1(1), 1, and y_0(1). In particular, whenever
c_0=0, psi simply reads y_0(1).

Define K to apply diagonal left translation by h to every
component and track exactly on the predicate

    c_0=0 and c_1=1,

and to be the identity elsewhere. This predicate is clopen and
is preserved by Q, F_A, and diagonal G_0 translations. Thus K
is a continuous involution, and commutes separately with Q and
F_A. No commutation of Q with F_A is assumed.

On the active predicate, equation (1) reads y_0(1) before K
and y_0(h) after K. Elsewhere K is the identity. If c_0=1,
then y_0=1 and Ay_0=0; hence in all cases

    psi(Kz)+psi(z)=c_1(Ay_0)(1)=:d(z).             (2)

The original observable also gives directly

    phi(F_A z)+phi(z)=c_1(A Q_t(y_0))(1)=d(Qz),    (3)

because only its first case reads the updated x track and the
case masks are Q- and F_A-invariant.

## Exact scalar linear-feedback extension on the enlarged group

Set

    Lambda_tilde=<Lambda,K>.

This group is still countable and all its elements commute with
Q and F_A. Use the same observable to define

    L_tilde(z)(lambda)=phi(lambda^-1 z).

The original coordinates are retained, so L_tilde is still
injective; it is continuous with a closed invariant image C_tilde.
The same identity phi(Qz)=phi(z)phi(s^-1z), where s is diagonal
left translation by t, proves

    L_tilde Q=Q_s L_tilde,
    Q_s(w)(lambda)=w(lambda)w(lambda s).

Equation (2) is now a sum of two orbit coordinates:

    d(z)=L_tilde(z)(a^-1)+L_tilde(z)(K a^-1).

The translation order follows from
(K a^-1)^-1=a K, since K is an involution. Put r=a^-1 and k=K,
and define the scalar linear operator

    B=R_r+R_{kr}=(I+R_k)R_r.

Then the full-shift cellular automaton

    tau(x)=x+B Q_s(x)                               (4)

satisfies tau L_tilde=L_tilde F_A. At the identity coordinate
this is exactly (2)-(3), and equivariance gives every coordinate.
Thus tau is a linear-feedback extension of the reversible code
map. The following calculation shows why it is not an injective
extension.

## The relevant subgroup is an actual copy of A_4

The subgroup J=<s,k> is isomorphic to A_4, with s corresponding
to (123) and k to (12)(34). To see this without inferring a
presentation from coefficients, use A_4=V_4 semidirect <t> and
the retraction pi:A_4 -> <t>. For g in A_4, act diagonally by
g on the invariant predicate c_0=0,c_1=1, and by pi(g) on its
complement. This is a group action. It sends t to s and h to
k, and is faithful: a nonidentity diagonal permutation moves
a suitable coordinate-unit configuration in component 0, while
component 1 is u. Its image is therefore exactly J, an A_4.

Moreover, r commutes with s. The prefix homeomorphism H and
the component swap P both commute with diagonal G_0 translations,
so their product a and its inverse r do too. No finite-order
claim for the whole support group is needed below.

## A general tetrahedral complement-collision lemma

Let M be any group containing J=<s,k> isomorphic to A_4, with
s=(123) and k=(12)(34) under that isomorphism. Let r in M
commute with s. Then

    tau=I+(I+R_k)R_r Q_s

is not injective on F_2^M.

First define z_0 on J using the complete graph on vertices
1,2,3,4. Orient all edges incident to 4 towards 4, and orient
the remaining triangle as 1->2->3->1. Every vertex then has
even outdegree: 0 at vertex 4 and 2 at the other vertices.
For g in A_4, put z_0(g)=1 exactly when the orientation of the
edge between g(4) and g(3) is g(4)->g(3).

Right multiplication by k reverses that edge, since k exchanges
3 and 4. Therefore

    (I+R_k)z_0=1.

The right-s triple g,gs,gs^2 has the same vertex g(4), and
its other endpoints run over all three remaining vertices.
Even outdegree gives

    (I+R_s+R_s^2)z_0=0.

Extend z_0 independently to every left J-coset of M, using a
choice of coset representatives. The resulting configuration z
satisfies the same two equations on M. Set

    x=R_{r^-1}R_s z.

For Boolean inputs,

    Q_s(x+1)+Q_s(x)=(I+R_s)x+1.

Since (I+R_k)R_r sends 1 to 0 and r commutes with s, it follows
that

    tau(x+1)+tau(x)
      =1+(I+R_k)(I+R_s)R_r x
      =1+(I+R_k)(R_s+R_s^2)z
      =1+(I+R_k)z
      =0.

Here (R_s+R_s^2)z=z follows from the even-triple equation.
The configurations x and x+1 are distinct, proving the lemma.

## Scope of the extension result

Applying the lemma to (4) gives an explicit full-shift collision
for the two-term extension, although its restriction to C_tilde
is an involution. The collision therefore cannot have both inputs
inside that code.

The result proves a finite linear representation of the needed
observable after adjoining K. It makes no assertion that the same
representation already exists over the original Lambda. Nor does
the collision exclude other extensions over Lambda_tilde or
further groups: another linear operator can agree on Q_s C_tilde
and act differently elsewhere. Finding an injective or reversible
ambient extension, by such corrections or another construction,
remains unresolved.
