# Finite support gives a reversible nonlinear full-shift extension

Date: 2026-09-08. The infinite invariant scalar code constructed
for the balanced triangular control has a zero-preserving,
nonlinear reversible extension to the entire scalar full shift.
The extension acts independently on cosets of a subgroup of
order at most 192. Its finite block permutation agrees with the
code involution on all block patterns occurring in the code and
fixes every other block pattern.

This closes the general nonlinear reversible-extension step.
An injective extension constrained to x+B Q_s with B linear is
still unproved. The previously constructed two-term extension
is noninjective, and the nonzero four-term correction below
preserves all its complement collisions. That bounded correction
result does not exclude other linear corrections.

No cellular automaton whose memory generates a finite subgroup
can be a Gottschalk counterexample. Thus the present reversible
control is not such a counterexample; a headline counterexample
would require memory generating an infinite group. All arguments
below are analytic and require no computation.

The subsequent
[group audit](gottschalk-prefix-symmetry-group-elementary-amenability-2026-09-08.md)
proves the entire current prefix and controlled-diagonal symmetry
group elementary amenable. It therefore excludes a counterexample
even after adding addresses that generate an infinite subgroup
inside this group. The linear-feedback extension question remains
only a reversible-control question within this construction.

We use the code C in F_2^{Lambda_tilde}, source symmetry group,
and linear-feedback extension from
[the controlled-extension artifact](gottschalk-controlled-symmetry-linear-code-extension-and-complement-collision-2026-09-08.md).
Write k=K, r=(P H_0)^-1, and let s be diagonal left translation
by t=(123). The involution k applies diagonal h=(12)(34)
exactly on the source mask predicate p=ZU*. The map P swaps
the first two components, and U denotes the component u=(1,1).

## The memory subgroup is finite

Set a=P H_0. For non-u components v,w and an arbitrary suffix
eta, its exact prefix action is:

    UU eta is fixed;

    (v,U,eta) <-> (U,v,U,eta);

    (v,w,eta) -> (U,v,w,eta) -> (w,v,eta)
               -> (U,w,v,eta) -> (v,w,eta).

These cases exhaust the source space, and prove a^4=I. They
also show that r=a^-1 exchanges p=ZU* with q=UZU*.

Every diagonal A_4 action preserves u and commutes with the
prefix cases and component swap. Thus r commutes with all
global diagonal A_4 actions, not just s. It follows that

    k'=r k r^-1

is conditional diagonal h on q, while r^2 k r^-2=k.

Conjugating k by s generates conditional V_4 on p, since
the t-conjugates of h generate the normal Klein four subgroup
of A_4. Conjugation by r gives conditional V_4 on q. These
two groups commute because p and q are disjoint and each
conditional action preserves every component's U/Z class.
Their product N is isomorphic to V_4 x V_4: either factor acts
faithfully on its own nonempty predicate and trivially on the
other one.

The group N is normalized by s and r. The element s conjugates
both factors diagonally, while r swaps them, using its commutation
with every global diagonal A_4 action. Since s^3=r^4=1 and
rs=sr, the memory subgroup

    H=<s,k,r>=N<s,r>

has order at most 16 times 12, hence at most 192. No exact
order assertion is needed.

## A nonzero correction that preserves complement collisions

The elements k and k' are commuting involutions with disjoint
source predicates. For any function f on the source, at least
one of them fixes each input; the commuting four-term orbit
sum therefore vanishes pointwise:

    f(z)+f(kz)+f(k'z)+f(kk'z)=0.

Consequently the scalar linear operator

    D=(I+R_k)(I+R_{k'})R_r

annihilates C, and therefore also Q_s C. At target coordinate
lambda this is the displayed identity applied to the observable
f=phi composed with r^-1 and input lambda^-1 z. Its four
group-ring terms are distinct because <k,k'> is C_2 x C_2;
thus D is a nonzero operator on the full shift. Its support
lies in H.

For B=(I+R_k)R_r, commutation of k and k' gives

    B+D=R_{k'}B.

Both B and B+D kill the constant configuration 1. The complement
collision equation for I+B Q_s is B(I+R_s)x=1. Since R_{k'}
is invertible and fixes 1,

    (B+D)(I+R_s)x=1  iff  B(I+R_s)x=1.

Thus this genuine correction, invisible on Q_s C, preserves
exactly the same complementary collision pairs. No conclusion
about all possible corrections follows from this example.

## Completing the code involution on each finite block

The known extension

    tau=I+B Q_s

has all memory addresses in H. Let tau_H:F_2^H -> F_2^H be
the same rule restricted to H, and let

    P_H={c restricted to H : c in C}.

The set P_H is invariant under the left H action. It is also
tau_H-invariant, and tau_H^2 is the identity on P_H. Indeed,
lift any p in P_H to a code point c. The restriction of tau(c)
to H depends only on p, and tau^2(c)=c because tau agrees on
C with its code involution. No injectivity of the projection
C -> P_H and no product structure for C are needed.

Define the finite block map

    theta_H(p)=tau_H(p)  if p in P_H;
               p        otherwise.

This is an H-equivariant involution of F_2^H. Its two invariant
pieces are P_H and its complement; on the first it is the code
involution and on the second it is the identity.

For x in F_2^{Lambda_tilde}, define

    Theta(x)(g)=theta_H(h |-> x(gh))(1).

H-equivariance makes this act as theta_H independently on every
left H-coset, regardless of coset representative. Hence Theta is
a scalar Lambda_tilde-equivariant cellular automaton with finite
memory H, and Theta^2=I on the entire full shift.

Every coset window of a point in C belongs to P_H by shift
invariance. Therefore Theta agrees with tau on C and realizes
the original balanced triangular dynamics under its code encoding.
It is zero-preserving: if the zero block lies in P_H, tau_H
fixes it; otherwise theta_H fixes it by definition.

This map is nonlinear. The restriction D_H is a nonzero linear
operator and P_H is contained in its proper kernel. Therefore
theta_H fixes every vector outside ker D_H. A linear map fixing
the complement of a proper linear subspace must be the identity:
any vector in the subspace is the sum of two vectors outside it.
But theta_H is not the identity, since its code restriction
realizes the nonidentity F_A. Thus theta_H and Theta are not
F_2-linear; because they preserve zero, they are not affine either.

The completion establishes a reversible nonlinear extension.
It does not assert that Theta has the special form x+B' Q_s
with B' linear. An injective extension in that restricted family
remains the separate open construction step.

## Why finite memory groups cannot produce a surjunctivity counterexample

More generally, let a cellular automaton on a finite-alphabet
full shift have all memory addresses in a finite subgroup H.
It acts independently by one finite map on each left H-coset.
If the full automaton is injective, the finite block map must
be injective: a block collision could be placed on a single
coset, with all other cosets unchanged. A finite injective map
is bijective, so independent block inversion makes the full
automaton surjective.

This applies to every rule supported in the H above, including
any corrected linear-feedback rule whose added addresses remain
in H. Such a rule could supply a reversible control for the
restricted feedback question, but cannot refute Gottschalk's
conjecture. A counterexample would need memory generating an
infinite subgroup, and the subsequent elementary-amenability
theorem excludes every subgroup of the current generated source
symmetry group. The proven code and reversible completion do not
settle the headline problem.
