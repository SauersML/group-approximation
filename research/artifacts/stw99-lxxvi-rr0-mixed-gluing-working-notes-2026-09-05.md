# Working notes: the remaining mixed-class argument for real-rank-zero fibers

Status: exploration only. This is not a proof of full Cu regularity for
real-rank-zero simple pure coefficient fields and is not a route in the
proof graph. The soft, all-base compact, and residual-projectionless
theorems are in separate reviewed artifacts.

Update: the moving-target gap below has now been resolved when the
source is a projection. The reviewed proof is
`stw99-lxxvi-rr0-relative-projection-selection-audit-2026-09-05.md`.
Its polar formulas verify both lower semicontinuity and equi-local
connectivity, and Michael selection supplies the exact relative
embedding. The resulting compact-left comparison theorem holds over
all compact metrizable bases. The exploration below records the
earlier gap and the still unresolved arbitrary-source passage.

## Exact current target

Let D be simple, separable, stably finite, pure, and real rank zero.
Prove that `C(X,D) -> C(X,D tensor Z)` induces a full Cu-isomorphism,
initially for finite CW X. All compact classes and all functionally
soft classes are already controlled in every base dimension. What
remains is a globally noncompact class having a nonzero compact image
under some closed-subset restriction.

The target is not an unrestricted `Lsc(X,Cu(D))` formula: compact
restriction bundles contain real data, and the first-factor map must
preserve that data together with its attachment to the other strata.

## A rigorous local input: proper Stiefel spaces are weakly contractible

Let `0<p<q` be projections in `D tensor K`, with `q-p` nonzero, and set

```text
Emb(p,q) = {v in q(D tensor K)p : v*v=p}.
```

Then Emb(p,q) is weakly contractible in its norm topology.

To see this, put `C=q(D tensor K)q`, a unital simple real-rank-zero
stable-rank-one algebra. U(C) acts transitively on Emb(p,q). Indeed,
given two embeddings v1,v2, their range projections r1,r2 are
equivalent to p. Cancellation in C makes `q-r1` and `q-r2` equivalent.
Adding a partial isometry between those complements to `v2 v1*`
produces a unitary taking v1 to v2. The stabilizer of the canonical
embedding p is `U((q-p)(D tensor K)(q-p))`, embedded by `u |-> p+u`.

The quotient map has local continuous sections by the standard polar
decomposition construction for nearby projections and nearby
isometries. It is therefore a locally trivial principal bundle and
has the usual homotopy long exact sequence.

Both unitary groups in this bundle are K-stable by Zhang's Theorem II.
The inclusion of the complement corner in C is full, so induces the
Morita K-theory isomorphism. The stabilization squares therefore show
that the map between the two unitary groups induces isomorphisms on
all homotopy groups, including components. The long exact sequence
gives connectedness and vanishing of all homotopy groups of Emb(p,q).

This argument is not available when p=q: the embedding space is U(C),
whose homotopy groups contain the coefficient K-theory. Those are
exactly the compact clutching invariants already retained by the
all-base compact theorem.

For locally trivial projection bundles with a locally nonzero
complement, this eliminates ordinary finite-CW relative obstruction
groups. It is a real input toward the full theorem, but it concerns
fixed projection types and ordinary bundles.

## The earlier moving-target gap, now resolved for projection sources

For arbitrary positive sections a,b, a relative comparison argument
would have to retain a prescribed comparison on a closed set, extend
it across the region with strict fiberwise Cu gap, and control norm
errors uniformly as the source and target compact fiber types change.
The proper-Stiefel calculation does not itself establish such a
parameterized extension theorem.

One possible route is a selection theorem for approximate comparison
spaces

```text
{v : ||v* b(x) v-a(x)||<epsilon}.
```

To use this route for arbitrary sources, one needs an explicit uniform local-connectivity
statement compatible with epsilon cutdowns and the prescribed closed
boundary, as well as enough control to pass to a continuous global
choice. Knowing each fixed-fiber homotopy group is zero is insufficient
for a selection theorem with moving fibers. No such theorem in the
needed arbitrary-source coefficient generality has been verified here.
For a projection source, the separate reviewed Michael-selection proof
now supplies the exact missing uniformity and relative extension.

Alternatively one could approximate a positive section by finite local
projection data. Real rank zero supplies projection approximations in
each individual coefficient hereditary algebra. It does not supply
one compatible family over the base, nor an automatic extension of
chosen local embeddings over overlaps. Constructing those compatible
families is part of the missing proof, not a permitted inference from
fiber real rank zero.

Even comparison alone would not finish the task: realizing the target's
mixed compact/soft restriction data in a source section must be proved
separately. The all-soft rank realization theorem does not prescribe
compact quotient lifts.

## A concrete check against a tempting false shortcut

One must not assert that `C(X,D)` has real rank zero merely because D
does. For a unital D with a normalized trace, consider the selfadjoint
section `h(t)=t 1_D` on [0,1]. A selfadjoint section with finite *global*
spectrum has the form `sum lambda_i p_i(t)`. Each projection p_i(t)
has a constant trace along the interval, since its Murray--von Neumann
class is locally constant. Thus every such finite-spectrum section
has constant trace. Its uniform distance from h is at least 1/2.

Accordingly one cannot replace the field Cu semigroup by the completion
of its global projection semigroup. The problem already occurs on an
interval, despite the independently proved full interval regularity.

## Literature boundary

Tikuisis, arXiv:1007.2927, Theorem 4.1, proves exactly a comparison
criterion retaining compact-level restriction data for simple unital
Z-stable ASH coefficients. The proof uses Lemma 4.2: a relative
embedding extension for recursive subhomogeneous building blocks with
a numerical matrix-rank gap. Lemma 4.3 then transfers the gap from a
slow-dimension-growth presentation. Neither hypothesis is available
for an arbitrary nonnuclear simple pure real-rank-zero D. Importing
that theorem with only the words 'real rank zero' substituted for ASH
would leave a substantive gap.

The Stiefel argument has now replaced the relative rank-gap mechanism
for projection sources. Its extension to arbitrary positive sources
and to mixed target realization remains unproved. These are dependencies
in this attack, not claims that the dependencies are themselves
separately published open problems.

## A genuine failure of the direct arbitrary-source selection shortcut

The successful projection-source local contraction cannot simply be
asserted for the family

```text
E(a,b) = {v in closure(bB) : v*v=a},
```

with arbitrary positive a varying in norm. The family of these spaces
need not be equi-LC^1, even for an infinite-dimensional UHF coefficient.

Choose nonzero orthogonal projections p,q in B and let epsilon_n>0
decrease to zero. Set a_n=b_n=p+epsilon_n q. Since p+q is finite,
E(a_n,a_n) is homeomorphic to U((p+q)B(p+q)) by

```text
u |-> u (p+sqrt(epsilon_n) q).
```

The loop

```text
v_n(t)=p+sqrt(epsilon_n) exp(2 pi i t) q,  0<=t<=1,
```

lies within sqrt(epsilon_n) of the ambient point p, which belongs to
E(p,p). Under the displayed homeomorphism this is the loop
p+exp(2 pi i t)q. Its stabilized pi_1 class is [q] in K_0 of the corner,
which is nonzero as detected by a faithful trace. Thus it is not
null-homotopic even in the entire E(a_n,a_n). Arbitrarily small balls
around p therefore contain sphere maps in members of this family that
do not extend in those members at all. Equi-LC^1 fails.

This is not a counterexample to Cu regularity: the UHF algebra is
already Z-stable. It is a precise obstruction to applying the same
one-shot Michael theorem to unrestricted moving positive sources.
Any successful arbitrary-source proof must control the disappearing
compact summands, for instance by fixing their embeddings on suitable
spectral equality sets before treating the remaining soft portion.

The compact-left theorem handles a single fixed projection source and
does not encounter this degeneration. Its initial-projection equation
is fixed within each contraction, and projection initial conditions
cannot acquire a new small spectral summand in the norm topology.

## Frozen end-of-round target: a cutoff relative selection lemma

The disappearing-loop example obstructs exact unrestricted selection.
It does not obstruct Cuntz comparison, which permits discarding source
spectrum below an arbitrarily small positive cutoff. The next bounded
target is the following explicit statement, currently **unproved**.

Let X be finite-dimensional compact metrizable and Y closed in X.
Let a,b in C(X,B)_+ be contractions with [a(x)]<=[b(x)] for all x,
and [a(x)]<[b(x)] whenever x lies outside Y and a(x) is nonzero.
Fix epsilon>0. Suppose a continuous s_Y:Y -> B satisfies

```text
s_Y* s_Y = (a|Y-epsilon/2)_+,
s_Y(y) in closure(b(y)B).
```

The required conclusion is a continuous v:X -> B such that

```text
v*v = (a-epsilon)_+,
v(x) in closure(b(x)B),
v|Y = s_Y h_epsilon(a|Y),
```

where h_epsilon is the continuous scalar function

```text
h_epsilon(t) = sqrt((t-epsilon)_+/(t-epsilon/2)_+)
```

on t>epsilon/2, extended by zero below that threshold. The boundary
formula ensures exactly the desired initial positive element after
the second cutoff. The lemma asks for compatible selection only after
this cutoff; it does not ask the family of unrestricted E(a,b) to be
equi-LC. Uniform control of embeddings of the large source spectral
pieces, with smaller pieces discarded, is the proposed mechanism.

Such a lemma would supply the missing comparison step in the method
of Tikuisis, Theorem 4.1 and Lemma 4.3(i), with the coefficient system
constant. For a given source cutoff, the compact equality set is
closed; the now-proved compact-left reflection supplies comparison
there. A slightly further cutoff extends that comparison to a closed
neighborhood. Off its interior the earlier source cutoff has strict
fiberwise comparison. The displayed lemma would then extend the
comparison over the whole finite-dimensional base. This paragraph is
a proposed use of an unproved lemma, not a completed reflection proof.

## The separate realization target

Even full order reflection would leave the following inner cofinality
statement to establish. For every pair y'<<y in the target Cu semigroup,
find a source class x with

```text
y' <= Cu(phi)(x) <= y.
```

This is a hereditary sandwich condition, much stronger than the already
known existence of an image class above y. The all-soft theorem proves
it within the soft part, and the compact theorem realizes compact y;
neither automatically handles arbitrary mixed y.

For clarity, the sandwich condition plus full order reflection would
finish surjectivity: take a rapidly increasing sequence y_n with
supremum y and choose x_n satisfying
y_n<=Cu(phi)(x_n)<=y_(n+1). Order reflection makes (x_n) increasing,
and its supremum maps to y. Thus the current full-Cu attack has exactly
two unproved tasks: cutoff comparison for mixed sources and the
mixed hereditary sandwich. No full real-rank-zero field theorem is
promoted until both are proved.
