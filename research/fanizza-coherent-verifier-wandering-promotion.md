---
rg: 2
id: fanizza-coherent-verifier-wandering-promotion
kind: claim
title: Promote the coherent Fanizza verifier reflection to one wandering Hecke word
distinct_from:
  balanced-router-pauli-holonomy-interface: that promotes two D8 packet reflections and asks a mixed return to trivialize their holonomy; this promotes one coherent-verifier reflection while retaining an infinite wandering normal form.
  compressed-reflection-kills-even-cesaro-mark: that requires a reducing corner reflection; the native uniform zero-flag corner here is nonreducing and therefore does not satisfy that theorem's hypotheses.
---

OPEN.  Let `V_m` and the finite clock/flag carrier `Q` be the explicit
reflection and projection from
`uniform-clock-reflection-block-encodes-game-hamiltonian`.  Construct a
finitely presented group extension and an ordinary word `w` such that:

1. after fixed finite-packet exactification in every matrix microstate, the
   selected carrier `Q_U` has fixed positive mass and

   ```text
   ||Q_U(w(U)-V_m(U))Q_U||_2 <= omega(def);            (FCW1)
   ```

2. the native signal carrier lies in `Q_U`, with only a fixed computable
   packet loss;
3. the group normal form keeps `w^k` and `X_D^R w^k` pairwise distinct; and
4. a countably amplified perfect HALT representation extends, even though
   `w` agrees on its first selected compression with the full finite-order
   reflection `V_m`.

## Dependency correction: the native corner is nonreducing

`uniform-clock-corner-is-not-a-reflection` corrects the former terminal
reading of `(FCW1)`.  Although `V_m^2=1` on the full clock/flag space,

```text
Q_U V_m(U)Q_U=(1-H_m(U))Q_U,
Q_U V_m(U)(1-Q_U)V_m(U)Q_U
 =H_m(U)(2-H_m(U))Q_U.                                (FCW1a)
```

Thus the selected compression is generally a strict contraction, not a
corner reflection.  Neither `compressed-reflection-kills-even-cesaro-mark`
nor `compressed-finite-order-wandering-is-terminal` applies to `(FCW1)`.
The routes `fanizza-wandering-dirichlet-return-route` and
`fanizza-compression-implies-localized-square-return` are invalidated.

Consequently the construction requested here, even if achieved, is only a
one-step wordization.  To recover a nonhyperlinear route one must additionally
construct a reducing returned carrier or prove a weighted-state estimate
controlling all complementary excursions of the powers of `w`.  The direct
finite-lamp construction in `uniform-clock-corner-is-not-a-reflection`
wordizes `V_m` exactly, but its word has order two.  Making the normal form
wandering while retaining robust excursion control is the actual missing
input.

There is now a further strict weakening which removes the named packet
carrier itself.  `unnamed-positive-density-fixed-space-is-terminal` proves
that an arbitrary model-dependent contraction `X_U` with fixed
`||X_U||_2^2` mass and `||(u(U)-1)X_U||_2=o(1)` already contradicts finitely
many canonical moments of one infinite-order word `u`.  No projection,
polar correction, spectral threshold, or cross-model carrier coherence is
needed.  The resulting minimal interface is
`fanizza-heterogeneous-compressed-row`: across an HNN edge it asks only for

```text
||a t p-t p b||_2=o(1).
```

The identity in `hnn-compressed-row-is-unnamed-fixed-carrier` turns this
into the soft fixed carrier for the Britton word `a t b^(-1)t^(-1)`.
Thus `(FCW1)` is not the weakest live endpoint and is no longer terminal; it
remains useful only as the first step of a stronger excursion-control
construction.

The exact tension is now explicit: `w` must be infinite and wandering in the
group regular normal form but have the same first corner as the fixed
reflection `V_m`, while its powers control the nonzero excursion in
`(FCW1a)`. A finite-edge graph-of-groups cell
cannot suffice, because its regular finite models reproduce the Hecke
compression.  The promotion must use a genuinely infinite-edge,
non-Bass--Serre, or finite-multiplicity return mechanism.

An infinite-edge self-similar return is not sufficient by itself either.
`self-similar-cylinder-return-regular-energy-floor` computes the exact
canonical obstruction: if the selected cylinder has density `alpha`, the
regular squared return defect is at least
`2 alpha-(2/pi)sin(pi alpha)`, even though the boundary/groupoid return can
be exact.  Hence a Nekrashevych, Toeplitz, or Leavitt normal form supplies a
noncanonical boundary carrier, not clause 1.  The surviving interface is a
matrix-only mechanism which promotes that cylinder mass to the canonical
packet while violating this regular Haar floor.

## Conjugate-product audit

The tempting word

```text
w=product_i t_i a_i t_i^(-1)
```

does not bypass this firewall.  The packet intertwiner's arbitrary
multiplicity unitary does cancel inside one conjugate on a selected type.
But `finite-graph-packet-compression-wandering-no-go`
shows that a representation-independent carrier return has only two normal
forms.  If every conjugate returns through an HNN edge relation, the stable
letters reduce and `w` belongs to a finite vertex packet.  If a stable letter
survives, then `q w q` lives on a nontrivial Hecke double coset, orthogonal to
the finite verifier `V_m` in the regular trace; residual finite quotients give
a fixed positive HS error.  Thus the multiplicity gauge is not the remaining
problem -- the incompatible pair is full carrier return versus ambient
wandering.

## Quantitative character-carrier audit

The former audit applied `character-carrier-wandering-floor` directly to the
native verifier compression. That theorem assumes a corner unitary
`V=QVQ`, `V^2=Q`, so it does not apply to `QV_mQ=(1-H_m)Q`. If a stronger
construction first produces a genuinely reducing character carrier, then
for every infinite-order candidate word it gives

```text
||Q w Q-V_m||_(2,regular)
 >= (1-1/sqrt(2))/sqrt(|K|).                           (FCW2)
```

The conditional proof has an exact dichotomy. If `w` fails to preserve the packet
character, a proper character-Hecke intersection loses at least half the
corner norm.  If it preserves the character, `w` reduces the corner, and
the reflection equation exposes the nonzero square-return word
`(w^2-1)Q`.  Hence every sufficiently canonical finite model has the same
positive floor up to profile error. The native uniform carrier reaches this
dichotomy only after the missing reduction/excursion-control step. Positive
packet density and coherent reflection aggregation alone do not supply it.

## D16/Hadamard audit

`fanizza-verifier-d16-charger-globalizes-ground-support` diagonalizes the
coherent reflection in the flag-`X` basis.  It is selector-central with
blocks `I` and `sum_j e_(jj)(1-2L_j)`, and the transverse D16 commutator has
energy exactly four times the average losing mass.  But the native signal
carrier uses the transverse flag-`Z` line and is not reducing.  Making the
commutator a global relator forces every losing projection to vanish as an
operator, while the recorded HALT theorem supplies only a positive-signal
ground vector.  Hence the D16 cell reads the verifier Hamiltonian but does
not perform the required support localization or wandering promotion.

## One-row and deleted-relator audit

The established two-letter dihedral swap has the correct analytic
private/shared row, but obtains it by declaring the corresponding
four-letter word to be a relator.  That makes the prospective Britton word
identity in the abstract group.  Deleting the relator does not repair this:
`deleting-one-gap-row-has-the-wrong-orientation` shows that the finite-game
gap forces the omitted row defect to stay macroscopically large on every
positive-mass Gram carrier when all retained rows are small.  The surviving
one-row compiler must infer vanishing from a genuinely mixed matrix-only
mechanism while keeping the four-letter word outside the relator closure.

## Relative-character audit of pulse and Schur carriers

The unnamed-carrier theorem does not make an unbalanced bridge word into a
return word.  `twist-invariant-carriers-force-relative-character-kernels`
gives the exact obstruction.  The projected Schur exit and the Thompson
first-hit cuts are functions only of the exactified packet/pulse letters.
They are therefore unchanged when a covariance/HNN bridge is multiplied by
an arbitrary scalar character.  Canonical microstates are also preserved.
Applying a claimed return before and after the twist gives

```text
|chi(w)-1| ||X||_2 <= 2 epsilon.
```

Thus no positive-density return can use a bridge with nonzero relative
abelianization class.  The one-sided pulse cells established in Cairn
genuinely transport the analytic exit into a summable first-hit site, but a
single unbalanced transporter cannot also be the wandering identity word on
that exit.  Any surviving promotion must use an exponent-balanced
cycle/commutator or make the carrier depend on the bridge multiplicity phase
itself.  The former returns to the existing localized-commutator and
regular-energy gates; the latter is absent from the current pulse/Schur
decoder.

## Exact-invisibility actuator audit

Even the strongest exact finite-dimensional actuator is insufficient.
`exact-fd-wandering-reflection-promotion-can-remain-sofic` starts from the
Slofstra--Vidick finitely presented sofic group with a nontrivial involution
`c` killed by every finite-dimensional representation.  In the free product
with `<t>`, the commutator `h=[t,c]` has infinite order but is still killed by
every exact finite-dimensional representation.  After direct-producting
with an already-wordized verifier base, `w=V_m h` is therefore exactly
`V_m` in every finite-dimensional representation and is wandering in the
abstract group.

Nevertheless the resulting group is sofic, and its canonical microstates
retain the full compression error

```text
||Q(w-V_m)Q||_2^2 -> 2 tau(Q).
```

Thus exact finite-dimensional representation theory can simultaneously
supply clauses 3 and 4 and the exact-model shadow of clause 1 without giving
`(FCW1)`.  The surviving two-cell must be payload-sensitive in the robust
normalized-HS sense: it must couple the actuator defect to the verifier
carrier with a dimension-independent modulus.  A sterile actor placed beside
the payload, even one whose marked word is invisible in every exact matrix
representation, is sharply refuted by this sofic wrapper.

## Common-gauge D16 phase-twist audit

There is a more payload-sensitive attempt.  Use the binary controller of
`finite-cocycle-select-forces-one-common-lcu-gauge` to place the identity and
one verifier reflection `r` in the two selector blocks with a shared right
gauge:

```text
c=diag(A,rA).
```

Hadamard rotation cancels `A`, and the commutator `g=[hch,z]` acts as two
copies of `r`.  On the `J=-1,r=-1` spectral carrier, `Jg` is therefore the
identity; a robust BCS losing-mass gap would give that carrier positive
density.  Unlike an uncoupled sterile actor, this construction genuinely
uses the verifier payload.

However `d16-common-gauge-select-collapses-charger-to-payload` proves the
exact group identity hidden in the block calculation.  Writing `x=hzh`, the
SELECT covariance is `cxc^(-1)=rx`, whence

```text
h[hch,z]h=cxc^(-1)x=r,
[hch,z]=r.
```

Thus the phase-twisted word is only `Jr`, an order-two clock, and its returned
carrier saturates rather than exceeds the canonical finite-clock threshold.
The common gauge has been removed by removing the wandering normal form.

This leaves a sharp requirement on a successful payload-sensitive two-cell:
the relative verifier block must be inferred only on a model-dependent
positive carrier (or by a genuinely finite-dimensional inequality).  If it
is imposed by the literal binary SELECT conjugacy relation, the proposed
wandering word reduces algebraically before any HS estimate is used.

## Verifier-controlled two-cycle audit

Feeding the already aggregated verifier reflection directly into the marked
two-cycle does reduce the whole losing projection to one payload, but it does
not supply the wandering return.  The stronger form of
`verifier-controlled-two-cycle-is-existentially-loss-blind` shows that the
two-cycle return holonomy is an arbitrary multiplicity unitary `A`.  Taking
`A` to be a sufficiently long cyclic shift keeps the zero compression exact
and makes every prescribed finite window of return moments vanish.  Hence
neither coherent clock aggregation nor canonical finite-profile tests turn
the two-cycle into `(FCW1)` or its unnamed fixed-carrier weakening.  A viable
promotion must couple the verifier loss to the holonomy itself with a
dimension-independent matrix-only inequality; a relation which only exchanges
the two flag atoms leaves precisely that variable unconstrained.

Nor can a finite common-orientation flag controller constrain that variable
in the required way.  `one-holonomy-word-controllers-are-free-or-torsion`
gives an exact dichotomy: its relators either have zero holonomy exponent, in
which case arbitrarily long cyclic-shift completions survive, or force one
bounded power of the holonomy to be trivial.  The latter makes a bounded power
of the wandering word return universally on the fixed source; the regular
finite-support argument then collapses the source or the wandering word.
Consequently a surviving controller must act noncommutatively on the
multiplicity algebra, or choose a carrier depending on that algebra.  Adding
more fixed packet words in the same tensor orientation cannot close `(FCW1)`.

The first apparent escape also has a firewall.  By
`tensor-separated-holonomy-controller-is-circular`, replacing the single
`A` by a noncommuting holonomy group `H` does nothing if `H` is an independent
multiplicity tensor factor: hyperlinear canonical microstates of `H` tensor
with every losing verifier model and preserve its losing density.  Choosing a
nonhyperlinear `H` imports the desired conclusion instead of deriving it.
Thus the live escape is narrower still: the multiplicity action must be
non-tensorially entangled with the BCS payload, or the authenticated carrier
must depend on that action.

The bare two-holonomy commutator does not achieve this entanglement.
`two-holonomy-weyl-controller-has-vanishing-boundary-defect` realizes any
fixed scalar Weyl phase by a clock and cyclic shift with normalized defect at
most `2/sqrt(d)`, supported on one clock line.  Root-of-unity phases even have
exact arbitrarily large models.  Selecting the phase-defect line makes the
carrier density `1/d`, while leaving it unselected makes its energy vanish.
An independent expander wrapper is covered by the tensor-separated firewall.
Thus an `A,B`-dependent carrier must be extensive for a reason tied to the
BCS payload itself; the spectral boundary of a fixed commutator is too thin.

Allowing an arbitrary nonlinear carrier chosen after observing the holonomy
still does not rescue any controller with long cyclic completions.
`long-cyclic-return-holonomy-annihilates-every-carrier` applies the Fejer
kernel inside the positive losing sector: if the return holonomy has
asymptotically vanishing fixed moments, every contraction on which it is
approximately the identity has vanishing mass.  No spectral, word, or
functorial assumption on that contraction is used.  Therefore the remaining
controller must exclude long cyclic holonomy with a dimension-independent
BCS-dependent relator cost.  “Choose the carrier as a function of `A`” is not
an additional escape hatch.
