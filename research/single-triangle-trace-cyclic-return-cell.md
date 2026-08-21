---
rg: 2
id: single-triangle-trace-cyclic-return-cell
kind: claim
title: Build one trace-cyclic proper-corner cell for the native Fanizza triangle
distinct_from:
  s3-active-packet-proper-corner-return: that places a three-atom allowed S3 sum into the recurrent carrier; this acts only on the one native Fanizza triangle chord after all tree incidences are normalized.
  schur-reynolds-one-overlap-actuator: that asks for one adjoint Reynolds overlap for every forbidden Schur packet; this asks for the fixed D8 holonomy projection of a single source-specific cycle.
---

OPEN.  Construct one finitely presented ordinary-group cell attached to the
last chord of the native Fanizza context triangle such that:

1. after fixed packet exactification **and using the prescribed native
   machine-word identities on the three separators**, the chord mismatch is
   the rational D8 group-algebra projection
   `H=(1-[R_F,R_G])/2`, or a fixed nonzero scalar multiple of it;
2. every finite-dimensional microstate decodes two block maps `X,Y` with the
   scalar trace estimates

   ```text
   |tr(YX)-tr(E)|+|tr(XY)-tr(E-H)| <= omega(def),      (STR1)
   ```

   where `omega(t)->0` and all carriers are the ones selected by the same
   triangle occurrence;
3. the exact gauge-covariant marked Fanizza representation, after countable
   amplification, extends across the cell by a one-sided Toeplitz/Hilbert-
   hotel realization; and
4. no relation turns `(STR1)` into a universal tracial identity in the group
   von Neumann algebra.

Finite-dimensional cyclicity gives `tr(YX)=tr(XY)`, hence

```text
tr(H) <= omega(def).                                   (STR2)
```

The exact canonical packet moment is `tr(H)=1/8`, so canonical matrix
microstates cannot satisfy vanishing defect.  Clause 3 keeps the mark
algebraically nonzero; clause 4 is the regular-representation firewall.

There is now a strictly weaker two-orientation alternative to clause 2.
By `two-oriented-trace-cyclic-returns-cancel-the-gauge`, it suffices to
decode a model-dependent projection `G<=H` and two cyclic returns

```text
E -> E-H+G,                  E -> E-G,                 (STR1')
```

with total scalar trace error `omega(def)`.  The two cyclic deficits are
`H-G` and `G`, so they add to `H` without any orientation or common-basis
selection.  For the D8 packet one may take the two complementary Pauli
halves `(TGR5)`.  This removes the stationary chord gauge from the scalar
endpoint; constructing the two finite-matrix-only return maps remains the
open group-word step.

Even the common hidden projection is unnecessary.
`trace-cyclic-triangle-balances-independent-return-gauges` allows the two
returns to use unrelated `G_0,G_1<=H`.  A third block pair on the remaining
triangle edge need only satisfy

```text
tr(BA) approx tr(G_0),              tr(AB) approx tr(G_1).  (STR1'')
```

Cyclicity balances `tr(G_0)` and `tr(G_1)`, and the three-edge ledger still
gives `tr(H)<=omega(def)`.  This is the native-triangle analogue of a
two-matching field balance: it asks for a same-occurrence **rank** coupling,
not operator alignment of the chord multiplicity gauges.  The balance edge
may be an ordinary tracially functorial incidence; only the two proper
returns must remain genuinely matrix-only.

The two proper returns cannot be extracted from the abstract triangle
tables or from separator rank matching.
`flat-fanizza-triangle-realizes-every-separator-distribution` constructs an
exact finite diagonal model for every rational distribution on
`(O_Q,O_P,Z_tilde)`, with all four context predicates satisfied and shared
occurrences literally equal.  It survives arbitrary equality clouds and an
independent positive D8 packet.  Therefore a two-matching/dimension-expander
repair must act on the noncommuting **native machine-word multiplicity**
(`P,X_tilde,U,Z_tilde,J` and the guarded recurrence), rather than merely
expand or balance the three separator marginals.

Moreover `dimension-expander-sampler-is-not-a-fixed-proper-return` shows
that any one finite such sampler has an exact amplified Weyl--D8 model and
cannot imply the two proper returns.  An all-depth sampler with uniform local
cost could instead close the separate occurrence/capacity route directly.
For this local actuator, dimension expansion helps only if the native
prescribed words already expose that uniform unbounded family; no such
native multiplicity-coordinate compiler is presently proved.

Because the native additive incidence graph has only one cycle, this cell is
source-specific and local.  It does not have to return an arbitrary BCS
atlas, synchronize a long computation, or provide a uniform family of
proper-corner gadgets.  What remains open is still genuine: ordinary group
words are invertible, so the one-sided maps must arise only after
finite-dimensional packet compression, not as literal group equations.

Two further exact audits sharply restrict that compression.

First, `central-character-regular-flow-defeats-finite-d8-return` proves that
selecting the negative central character of the D8 packet does not defeat
the regular stationary flow.  Every finite graph of finite packet groups
which preserves the common D8 center has an exact finite-dimensional
negative-character representation; on it `H` is the identity.  Thus a
single Bass--Serre/HNN incidence cell, even after central-type selection,
cannot satisfy `(STR1)`.

Second, `universal-block-return-violates-the-regular-firewall` proves that a
Julia unitary, Steinberg block linearization, or literal Toeplitz relation
cannot supply `(STR1)` as fixed group-algebra identities.  The left regular
finite trace would then give `tr(H)=0`, contradicting the faithful
trace-`1/8` D8 projection.  Consequently the missing two-cell must act on
the **finite chord multiplicity coordinates** and must not be derivable in
an arbitrary finite tracial von Neumann algebra.

After these audits, the minimal unresolved scalar is precise: on the
selected central-character stationary packet, the native prescribed-word
two-cell must force the chord multiplicity transport to lose exactly the
`H` carrier in finite matrices, while countably infinite multiplicity
absorbs that loss.  Neither packet restriction multiplicities nor a
universal block identity can be the source of this loss.

Nor can a fixed determinant or projective-index test provide the loss.
`fixed-d8-holonomy-has-no-determinant-density` fills the external
multiplicity by exact bounded Clifford blocks and confines every mismatch to
one bounded remainder.  Tensoring that remainder with the positive-density
D8 spin leaves normalized HS error `O(m^(-1/2))`.  Two independent return
orientations only replace the bounded block size by another fixed constant.
They become useful only if the native prescribed words make them act on a
growing family of multiplicity coordinates or prove the extensive
proper-corner loss in `(STR1)` itself.

The triangle alone supplies no charge.  It is classically flat, with all
eight separator assignments extendible.  Hence clause 1 must fail if the
separator signs are treated as free Boolean variables.  The prospective
holonomy is a semantic machine-word/corner effect, not a contextuality proof
on the abstract three-cycle.

The global-Pauli shortcut does not remove this target:
`fanizza-pauli-guard-switches-off-at-the-terminal-cell` proves that the C18
parity guard fails exactly on the terminal HALT block.  Thus the chord is a
genuine part of the native source and its one proper-corner return is again
the load-bearing local theorem.

The ordinary-word shadow of the native doubling relation also does not
remove it.  `fanizza-reflection-recurrence-has-s4-stationary-overlap`
constructs an exact `S_4` model in which

```text
Z_(n+1)=Z_n X_n Z_n X_n^(-1)
```

holds at every conjugate level, all carrier cuts have the same trace, and
the hidden overlap has trace exactly half of the carrier.  Thus the word
identity remembers symmetric difference, not orthogonal union.  The two
proper returns must charge the nonlinear C18 overlap itself.

Finally, `functorial-packet-return-firewall`
extends the regular firewall beyond literal block words.  Fixed finite-group
averaging, spectral exactification, polar decomposition, support cuts, and
conditional expectations are all available in the left regular finite von
Neumann algebra.  If they functorially produced either proper return, trace
cyclicity would kill the positive regular D8 cut.  The live actuator must
therefore contain an explicitly finite-matrix **integer multiplicity**
choice, forced by the prescribed C18 words, whose loss is proportional to
the active dimension.  This is now the minimal scalar not supplied by any
fixed packet or reflection recurrence.
