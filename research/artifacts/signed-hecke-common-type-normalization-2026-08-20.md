# Common-type normalization for the signed-Hecke programme

**Date:** 2026-08-20  
**Status:** Two exact finite-algebra statements proved; the global algebraic
atlas remains open.  No non-hyperlinear group is claimed.

## Uniform local seed

For a finite BCS, take `D` to be twice the least common multiple of the
numbers of allowed assignments in its contexts.  Every context can be placed
in the same tautological irreducible type of the hyperoctahedral group

```text
K_D=(C_2)^D semidirect S_D.
```

Repeat each allowed assignment equally among the `D` coordinates.  The
corresponding diagonal sign elements have exactly the desired joint spectrum.
The primitive central idempotent `q_D` of the tautological type has positive
canonical trace, is killed by every scalar group character, and decomposes
into `D` explicit algebraic coordinate atoms `q_D e_(chi_i)`.

This proves
`all-bcs-contexts-share-one-hyperoctahedral-signed-type`.  The signed-Hecke
programme no longer needs to reconcile different local finite groups,
irreducible dimensions, or corner traces.

## Sharp finite-root obstruction

The common-type normalization does not solve overlap compatibility.  If all
piecewise transports return the context projections to the single finite
root algebra

```text
q_D C[K_D]q_D isomorphic to M_D(C),
```

then the compatible atlas is a finite-dimensional representation of the BCS
algebra.  Its normalized matrix trace is Connes embeddable, contradicting the
choice of the no-CE-trace BCS.  This is
`root-block-piecewise-transport-cannot-host-nonce-bcs`.

Consequently the remaining holonomy has an exact geometric requirement.  All
contexts may begin with isomorphic copies of the same finite block, but after
transport into `q_D C[Gamma]q_D` at least one copy must be a finite-dimensional
subalgebra not contained in the root `M_D(C)`.  Shared-variable marginals must
agree across those differently placed subalgebras.  Coordinate permutations
or arbitrary unitary rotations internal to the root block cannot suffice.

## Rational balancing and the remaining chord

A source trace gives nonnegative context-atom weights with matching signed
marginals.  The feasibility region is a nonempty rational polytope, so it has
a rational point.  Clearing denominators gives a common integer dimension
`D` and context multiplicities `n_(c,a)`.  The `+1` and `-1` eigenspace ranks
of every shared variable now agree exactly, so each incidence has an explicit
coordinate permutation intertwining that one sign.  This is
`tracial-bcs-has-rational-balanced-hyperoctahedral-atlas`.

Those edge permutations cannot admit a coherent family of context gauges.
If they did, the conjugated diagonal signs would define one tuple in `M_D`
satisfying every BCS context, and normalized matrix trace would be CE.  Thus
the residual obstruction is precisely cycle holonomy; this is
`coherent-balanced-context-permutations-would-give-a-ce-trace`.

The refined open cell is `signed-hecke-block-escaping-cycle-holonomy`.  It
asks for finite-support corner unitaries which preserve the shared binary
marginal on each chord while moving at least one whole context matrix algebra
outside the finite root block.  Proving that cell completes the original
signed-Hecke atlas by `signed-hecke-balanced-holonomy-route`.

## Exact one-marginal escape

One chord of the refined cell is now explicit.  In
`Gamma=K_D times F_D`, let `e_i` be the root coordinate atoms and set

```text
W=sum_i h_i e_i
```

for free generators `h_i`.  This is a finite-support corner unitary.  Rotate
two same-sign coordinates by a Hadamard matrix before conjugating by `W`.
The resulting atom projections contain nonzero coefficients at the reduced
words `h_r h_s^(-1)` and hence lie outside the root block, while their signed
sum is the original binary marginal.  This is
`one-binary-marginal-block-escape`.

This first statement concerns the coordinate refinement.  A coarse BCS
assignment projection escapes when the Hadamard pair belongs to two distinct
supported assignments with the same preserved sign.  If they are duplicate
coordinates of one assignment, the cross terms cancel in the coarse sum.
More generally, `free-phase-context-escape-criterion` proves that a family of
already-fixed marginals permits a context escape exactly when their joint
sign pattern does not separate the supported context assignments.

The remaining claim is
`simultaneous-block-escaping-context-holonomy`.  Independent one-edge cells
do not work because they give different PVMs for the same context.  The
needed composition must preserve all previously fixed marginals while still
mixing across at least one context atom.  This is now a finite simultaneous
incidence/linear-algebra problem rather than an unspecified groupification.

The exact audit `experiments/signed_hecke_one_marginal_escape.py` performs the
calculation in `M_4(Q[F_4])`.  It verifies unitarity, self-adjointness,
idempotence, orthogonality, the partition identity, and preservation of the
signed marginal.  Its checked JSON records the two non-root supports
`h1 h2^(-1)` and `h2 h1^(-1)`.

## Full overlaps and join trees

Evaluating every joint atom on a context intersection strengthens binary rank
balancing to `tracial-bcs-rationalizes-full-overlap-distributions`.  After
rationalization, the entire separator tuple between two contexts has matching
integer fibers.

This makes the free-phase construction inductive on a join tree.  Attach a
child context in a fresh direct-product free factor, using the transported
matrix units of its parent.  A unitary block diagonal over the full separator
fibers and the diagonal free-phase sum preserve every previously defined
shared variable.  The running-intersection property ensures that all earlier
overlaps of the child lie in that separator.  This proves
`join-tree-bcs-has-explicit-signed-hecke-atlas`.

Thus the first genuinely open operation is no longer generic simultaneous
composition.  It is `first-cycle-signed-hecke-chord`: close one non-tree
overlap while retaining the tree-separator marginals at both endpoints.  A
stable letter supplies conjugacy but not equality, and regauging one endpoint
usually destroys its parent attachment.

The finite double-orbit calculation is now exact.
`chord-regauging-is-relative-commutant-feasibility` identifies a common target
involution in the intersection of the two separator commutants.
`finite-relative-commutant-chord-is-bounded-integer-feasibility` decomposes
the algebra generated by both separator tuples into Wedderburn blocks and
turns existence into one bounded integer system.  When the separators
commute, `commuting-separator-chord-is-capacitated-transport` turns the same
system into bipartite max flow.  Equal unconditional ranks are not sufficient:
the two Pauli axes in `M_2(C)` generate the full matrix algebra and leave only
a scalar common commutant.

This does not finish the chord.  The join-tree ambient group is a finite
direct product of a finite group and free groups, hence residually finite.
`cycle-closure-cannot-remain-in-the-join-tree-group` shows that completing all
cycles inside its unchanged signed corner would pull back a CE canonical
trace, contradicting the no-CE BCS source.  Moreover finite-subgroup character
idempotents admit exact piecewise HNN transport, but
`finite-edge-hnn-closures-cannot-finish-the-nonce-atlas` proves that every
finite iteration of such finite-edge HNN steps remains residually finite.
The missing operation must therefore create the algebraic common commutant
through an infinite-edge or non-Bass--Serre mechanism.

The exact audit `experiments/signed_hecke_chord_feasibility.py` checks both
finite criteria over the rationals.  It computes the common commutant of the
transverse Pauli separators and finds only the identity direction, hence no
rank-one common chord sign.  It also exhausts two `2 by 2` capacitated
transport instances, recording both the two feasible permutation flows and a
cut-obstructed instance with no integral solution.

## Exact free-phase support and the infinite-edge audit

The free-phase cell uses less of its fresh free group than its original
presentation suggests.  If `h_1,...,h_D` are the fresh generators, put

```text
a_1=1,                    a_i=h_i h_1^(-1),
L_D=<a_2,...,a_D>.
```

Then `{h_1,a_2,...,a_D}` is a Nielsen basis, so `L_D` is a proper free factor
of rank `D-1`.  Every transported coefficient has the form

```text
E_(ij) h_i h_j^(-1)=E_(ij) a_i a_j^(-1),
```

and hence the entire escaped context block is supported on
`q C[K_D times L_D]q`.  This is
`free-phase-context-support-is-a-proper-free-factor`.  It supplies a canonical
proper infinite subgroup for the first-chord interface (nonamenable once
`D>=3`) and removes the otherwise unused common phase generator from the
problem.

The most immediate ways to use that subgroup have now been audited exactly:

1. Identifying two commuting copies of `L_D` symmetrically gives an HNN group
   whose height kernel is the graph product of copies of `L_D` over the
   bi-infinite path.  Finite intervals are right-angled Artin groups, so the
   kernel is a directed union of hyperlinear groups and the full group is
   hyperlinear-by-cyclic.  This is
   `symmetric-free-support-hnn-remains-hyperlinear`.
2. Sending one phase copy diagonally into two commuting copies does transport
   every matrix coefficient exactly and appends one free-phase layer.  After
   reversing the stable letter, however, this is the Formanek--Procesi group

   ```text
   H(L)=<L times L,s | s(g,g)s^(-1)=(g,1)>.
   ```

   It embeds in `Aut(L*Z)` and is residually finite for finitely generated
   residually finite `L`.  Thus the exact depth-advance cell is residually
   finite and hyperlinear.  These are
   `diagonal-hnn-exactly-advances-free-phase-depth` and
   `formanek-procesi-diagonal-hnn-is-residually-finite`.
3. Distorting the new phase by an arbitrary injective endomorphism
   `theta:L_D->L_D` does not escape this fence.  The graph HNN

   ```text
   <L_0 times L_1,t | t(g,1)t^(-1)=(g,theta(g))>
   ```

   embeds in the same Formanek--Procesi group by
   `(g,h)|->(theta(g),h)`.  Britton membership reflection proves injectivity.
   This is `graph-endomorphism-phase-hnn-embeds-formanek-procesi`.
4. The apparent residual case of nonextendable partial graph maps is also
   residually finite.  Let `A` be any finitely generated subgroup of a
   finite-rank free group `L`, let `P` be finitely generated and residually
   finite, and take arbitrary homomorphisms `Theta_0,Theta_1:A->P`.  Then

   ```text
   <L times P,t |
    t(a,Theta_0(a))t^(-1)=(a,Theta_1(a))>
   ```

   is residually finite.  A finite phase quotient preserves every pinch whose
   free coordinate lies in `A`.  Marshall Hall covers simultaneously make
   both partial maps descend and keep every other free-coordinate syllable
   outside the image of `A`.  The chosen word therefore survives in an HNN of
   a finite group and then in a finite quotient.  This is
   `partial-phase-graph-hnn-is-residually-finite`.
5. Moving the faithful support between two whole direct factors does not help.
   For arbitrary finitely generated residually finite `A,P` and auxiliary
   maps `Theta_0,Theta_1:A->P`, the HNN between

   ```text
   {(a,1,Theta_0(a))}  and  {(1,a,Theta_1(a))}
   ```

   inside `A times A times P` is residually finite.  One common finite quotient
   of `A` makes both phase maps descend and preserves every faithful-coordinate
   pinch test.  This is
   `phase-coordinate-switch-hnn-is-residually-finite`.
6. The same conclusion holds for the actual proper supports in `(FPS1)`.
   More generally, if one abstract finite-rank free group is embedded as a
   free factor in each of two ambient free groups, then the HNN between its two
   graph embeddings is residually finite, with arbitrary auxiliary phase maps.
   One common finite quotient of the support extends across each free
   complement and preserves the finitely many forbidden memberships of a
   chosen Britton word.  This is
   `free-factor-phase-graph-hnn-is-residually-finite`.
7. The first nonprimitive power-pair test has exact finite marked models.  For
   primes not dividing `mn`, the HNN sending each `x_i` to `x_i^m y_i^n` acts
   exactly on two copies of the finite Heisenberg group, and the free
   commutator remains nontrivial.  Thus proper, nonextendable power images do
   not alone create a finite-dimensional collapse.  This is
   `power-pair-phase-hnn-has-finite-heisenberg-mark-models`.
8. In fact every coprime power-pair HNN is residually finite.  For any prime
   away from the two exponents, cyclic-syllable normal form in the free
   pro-`p` product shows that the profinite graph intersects the discrete
   `F times F` in exactly the intended power-pair subgroup.  Characteristic
   finite `p`-group quotients then preserve every forbidden Britton pinch;
   see `coprime-power-pair-phase-hnn-is-residually-finite`.  Hence the first
   explicitly nonprimitive return is fully fenced.

Together with `amenable-edge-hnn-preserves-hyperlinearity`, this leaves a
much narrower live interface.  A decisive infinite-edge chord must use a
nonamenable proper support and couple multiple phase factors non-graphically:
it cannot be a symmetric factor identification, a graph of one injective
endomorphism into a commuting copy, a partial graph over one unchanged
faithful free coordinate, a switch between whole faithful direct factors, an
amenable edge, a switch between the natural free-factor supports, a coprime
power-pair switch, or an endomorphism of the whole base.  It must instead use
a nonprimitive faithful-coordinate embedding beyond coordinatewise coprime
powers (or leave finite-product free-phase geometry), fix both separator
algebras, and carry genuine cycle holonomy.  Its marked packet must
also be profinitely incompatible with the edge transport; mere
nonprimitivity is not enough.  This surviving requirement is recorded in
`infinite-edge-common-commutant-for-first-chord`.
