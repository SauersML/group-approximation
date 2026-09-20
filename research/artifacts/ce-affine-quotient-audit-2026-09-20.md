# A matrix-only affine decoder cannot escape through a nonhyperlinear host

20 September 2026. This is a correction to the optimistic interpretation
of the CE-only decoder regime, not a solution of perfect-completeness
hardness. It strengthens the earlier canonical-trace argument by passing
to the image of one Connes-embeddable representation first.

## Statement

Use the setting of `ce-exact-affine-compilers-force-nonhyperlinear-corners`:
Gamma is countable, J is central of order n, omega is a faithful character
of <J>, and p_omega is its central-character projection. A finite BCS B
has a decoder from finite abelian contexts of p_omega C*(Gamma), with
affine answer maps, that is exact on **every** Connes-embeddable (CE)
tracial model of this corner.

If the corner has even one CE tracial model, then B has a perfect CE
model whose support in every source context is an affine subset of that
context's allowed answers. No hyperlinearity assumption on Gamma is
needed.

Consequently, for a source with no such affine-safe perfect CE model,
every CE-exact affine target corner has **no CE model at all**. Making its
ambient group nonhyperlinear cannot restore the positive quantum branch.
Non-affine and constant-loss decoders remain outside this statement.

## 1. Pass to the group image of one model

Let tau be a CE model of the corner and let M be its tracial GNS von
Neumann algebra, embedded trace preservingly into a tracial matrix
ultraproduct. The map

    rho(g) = image of g p_omega in U(M)

is a group homomorphism. It sends J to omega(J) times the identity.
Set N=ker rho and H=Gamma/N. The induced map of H into U(M) is injective.
In particular the image j of J still has exact order n. Gamma need not
be hyperlinear; the countable image H is.

For completeness, the usual trace-amplification argument verifies the
last assertion without assuming that rho initially has canonical trace.
For h in H let chi(h)=tau_M(rho(h)). Faithfulness of the trace on M
gives chi(h)!=1 whenever h!=1: a unitary of trace one has squared
2-distance zero from the identity. Direct-sum rho with the trivial
representation in equal proportions, then take m tensor copies. The
resulting character is

    chi_m(h) = ((1+chi(h))/2)^m.

For h!=1, the complex number inside parentheses has modulus strictly
less than one; for h=1 it is one. Thus chi_m converges to the canonical
character delta_1. Each finite direct sum and finite tensor power has
matrix microstates, inherited from those of M. A diagonal choice over
the countably many words and m gives microstates for delta_1 itself.
Equivalently L(H) with its canonical trace is CE. This is the standard
hyperlinear amplification argument, not a new analytic theorem.

## 2. A new CE corner model with canonical quotient support

The image j is central of order n. In L(H), let q_omega be its
omega-character projection. Its canonical trace is 1/n. The positive
corner q_omega L(H) q_omega, with normalized trace, is CE: cut matrix
microstates along the spectral projection of the finite-order central
unitary, whose normalized rank converges to 1/n. Approximate commutation
with each fixed word ensures the compressed microstates represent the
corner products. Equivalently use the standard permanence of CE under
positive-trace corners.

Pull this trace back along Gamma -> H and the induced map of character
corners. This gives another CE model sigma of the original corner.
The decoder must therefore work on sigma, not merely on the original tau.

Let A be one of the original finite abelian target contexts. Let
Abar be its image in H. In the normalized canonical j-character trace,
the spectral distribution on Abar is uniform on the characters that
agree with omega on Abar intersection <j>. Pulling back to A gives
the set

    X_A = {characters of A that factor through Abar and have
           the specified omega value whenever their image lies in <j>}.

It is nonempty, and is a coset of a subgroup of the character group of
A. One can also see this directly by Fourier expansion: the trace of
a is zero unless its image is j^k, when it is omega(j)^k. Orthogonality
of characters then gives equal positive mass on exactly X_A.

The original affine decoder D sends X_A to an affine set D(X_A). Its
image is exactly the support of the decoded answer distribution, since
every element of X_A has positive mass. Exactness on sigma puts that
support inside the allowed set. The shared-variable condition in the
decoder gives one global source model, and its algebra is a subalgebra
of the CE quotient corner, so it is CE. This proves the statement.

Notice the intersection in the formula is computed **after quotienting**.
Different target words may become equal in H. This changes the affine
coset, but does not destroy affinity. No preservation of the original
context subgroup as an injective subgroup is needed.

## 3. Consequence for the current constructive attack

The earlier node established the weaker conclusion that an affine-unsafe
source forces a nonhyperlinear ambient group. That conclusion remains
correct. Its proposed escape through a nonhyperlinear host is not enough
when the task also demands a positive CE model: that model supplies the
hyperlinear quotient used above.

This closes a precise tempting use of Liu's new examples. Attaching a
nonhyperlinear group to an affine-readout compiler does not, by itself,
permit exact affine decoding on all matrix models while retaining a
matrix model on a halting input whose source is affine-unsafe.
Liu's theorem is not used in the proof of this obstruction.

For example, a literal group clock of order three that is disjoint from
the marked central subgroup has all three characters in the quotient
canonical model unless quotient relations constrain that clock to the
marked center. One cannot use a matrix-only promise to universally erase
just its trivial character while preserving both nontrivial characters
in the same marked sector. Nonabelian matrix-algebra readouts and
source-specific non-affine decoding are genuine different possibilities.

## Sources and review scope

Repository searches covered the CE-only decoder map, the exact affine
corner theorem, its constant-gap refinement, and the finite-subgroup
invisible-type condition. None of those arguments passes to the group
image of an arbitrary positive CE corner model.

The standard analytic ingredients are hyperlinear trace amplification and
CE permanence for positive corners. The central-character formulation was
checked against Andreas Thom, *Examples of hyperlinear groups without
factorization property*, [arXiv:0810.2180](https://arxiv.org/html/0810.2180),
and the published version [DOI:10.4171/GGD/80](https://doi.org/10.4171/GGD/80).
The paper's central-extension criterion is background; the displayed
amplification and quotient argument give the specialized proof here.
No claim of literature novelty or formal verification is made.

The strong LCS target remains open. This proof closes a decoder regime,
not the whole target. An independent sibling review checked trace
amplification, the marked corner after taking the quotient, possible
noninjectivity of the finite context maps, and the affine support
calculation, and found no flaw. This is internal written review, not
formal verification.
