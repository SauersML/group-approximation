# Wreath-product source: coefficient projection is not a full-group map

Date: 2026-09-08. The Boone--Higman goal remains open.

The new source located in the previous turn is
[Almeida--Dantas--de Oliveira-Tosti, arXiv:2609.01868v1](https://arxiv.org/pdf/2609.01868v1).
This audit does not import Theorem D as an established Cairn premise.
It identifies an obstruction to a step in its finite-presentation proof,
without asserting that its theorem is false.

## The projection obstruction

On printed page 29, at the end of Section 5.2.1, the proof appeals to a
projection toward V_m(G) which kills a localized lamp generator.
Remark 5.14 repeats the exponent argument for several lamps. The same
passage occurs in the HTML version; it is not an HTML extraction issue.

There can be no such coefficient-forgetting homomorphism preserving the
prefix subgroup V_m. The new Cairn claim
`cantor-prefix-subgroup-detects-every-normal-kernel` proves this in greater
generality: in any faithful group of Cantor homeomorphisms containing
V_m, every nontrivial normal subgroup intersects V_m nontrivially.

Its certificate is the elementary identity

    [[a,f],b]=[a,b]!=1

where f is a nonidentity element of the proposed kernel, a and b are
noncommuting prefix permutations supported in a cylinder U, and U is
disjoint from f(U). This places a nontrivial prefix permutation in the
kernel. Any map fixing V_m would have to preserve that element instead.

An ordinary coefficient epimorphism H->G therefore does not automatically
induce V_m(H)->V_m(G). In the faithful full group, coefficient elements
and prefix elements already satisfy geometric relations which the
coefficient epimorphism may not respect.

This addresses a global full-group interpretation of the projection.
If instead the intended map is defined only on a localized copy of the
ordinary wreath product, the ordinary coefficient projection exists;
the exponent inference below still does not follow from it. These two
interpretations should not be conflated.

There is also a direct recursion check in the displayed construction.
The source's lamp recursion has the form

    gamma=(gamma,1,...,1,x)

with trivial first-level permutation and a nonidentity actor element x.
The corresponding localized splitting identity is

    L_v(gamma)=L_(v1)(gamma)*L_(vm)(x).

All localized copies of gamma are conjugate by prefix replacements.
A homomorphism fixing those prefix replacements and killing L_v(gamma)
would also kill L_(v1)(gamma). The displayed identity would then force it
to kill L_(vm)(x). It cannot at the same time preserve the prescribed
actor coefficients. Equivalently, forgetting gamma fails compatibility
with sections: a section of gamma is x, whereas the identity has only
identity sections.

## Two elementary checks on the proposed normalization

Even inside the ordinary wreath product, a projection which kills a lamp
contains no information about that lamp's exponent. For every integer t,
the image of gamma^t under the coefficient projection is the identity.
Thus the inference from a trivial projected element to t=0 needs a
different argument. Once the actor component has been shown trivial,
one may inspect the actual lamp coordinates; the projection itself does
not inspect them.

Commutativity also does not identify different lamp positions. In
Z wr Z, let a_0 and a_1 denote the unit lamps at positions 0 and 1.
They commute, but a_0*a_1^-1 has coordinates (1,-1), so it is nonidentity
despite having total exponent zero. A reduction to one scalar exponent
must justify how it preserves every occupied coset coordinate. The
source's finite-presentation conclusion is not established by the
projection argument as written.

## Scope and next usable condition

The extended nucleus is defined as N(G) union Q(gamma), a finite state
set. This audit does not claim that this definition is infinite. The
earlier question about powers was resolved by reading that definition.

To use this proposed finite-presentation mechanism, a replacement proof
must derive cancellation of the localized lamp coordinate vector from
the finite relator list. It cannot appeal to a homomorphism of faithful
full groups which kills that vector while fixing V_m. The existence of a
replacement proof has not been decided here.

This obstruction also explains why the canonical quotient in
`abstract-btb-simple-quotient-fp-gate` must retain its stated abstract,
possibly nonfaithful setting. It is not a license to forget nonidentity
homeomorphisms inside a faithful full group while fixing all prefix maps.
No change is made to that imported theorem.

An independent positive construction for constant-ray boundary orbits
is now recorded in `boundary-orbit-cyclic-wreath-germ-proof` and
`research/artifacts/boone-higman-boundary-wreath-germ-construction-2026-09-08.md`.
It uses relative isotropy germ quotients and the finite-germ theorem;
it does not use the audited projection or establish the full generality
of Theorem D. The projection obstruction above remains applicable.

The associated unreplicated boundary actor also has infinite
abelianization by `boundary-orbit-wreath-section-charge-proof`.
This must be distinguished from the repeated-state representation in
Section 5.2.2 of the source: repetition changes the section-sum
relations and removes that particular integer character. Thus the
new character does not refute the source's altered-representation
finite-abelianization conclusion.

There is no assertion here that the paper's target groups fail finite
presentation or fail Boone--Higman. No author or provider was contacted.
The new kernel lemma is a written proof; no GPU or local computation was
used to establish it.

## Remote structural validation

The mathematical audit and graph changes are commit `010203a9f`, pushed
through main integration `c44909373e882b6b022d51af7fb03858b173859d`.
[Research run 34288738250](https://github.com/SauersML/group-approximation/actions/runs/34288738250)
completed successfully. The downloaded evidence is retained in
`.cairn/bh-cantor-kernel-check-20260908/`.

The inspected Cairn `node_status` is ESTABLISHED for
`cantor-prefix-subgroup-detects-every-normal-kernel` and OPEN for
`boone-higman-conjecture`. The earlier universal automorphism premise is
still REFUTED and its route INVALIDATED. No theorem from the audited
paper was promoted to ESTABLISHED. These are dependency-graph checks,
not machine verification of the infinite-group proofs.
