---
rg: 2
id: fanizza-matrix-coordinate-source-full-compression
kind: claim
title: Build a Fanizza cell whose finite microstates decode one source-full compression into the guarded smaller carrier
artifacts:
  - research/artifacts/fanizza-one-sided-compressed-rank-floor-2026-08-21.md
distinct_from:
  single-triangle-trace-cyclic-return-cell: that asks for two cyclic return products or its three-edge variants; this asks only for one source-Gram estimate into a strictly smaller guarded target.
  finite-window-decoder: that decodes three Leavitt products on a positive corner; this asks for one compressed ambient unitary tied to the native C18/D8 carrier.
  s3-active-packet-proper-corner-return: that places the S3 active isotypic sum and must manage all complementary exits; this is the minimal local source-fullness estimate on the single Fanizza triangle chord.
---

Construct one finitely presented native Fanizza triangle cell such that, for
every sufficiently accurate finite-dimensional microstate, fixed packet
exactification and a genuinely matrix-coordinate multiplicity rule produce
projections

```text
H<=E,       F=E-H,
```

and an ambient unitary word `U` such that

```text
tr(H)=1/8+o(1),
X=FUE,
||X^*X-E||_2 <= omega(def),       omega(t)->0.          (OCR8)
```

The exact amplified HALT representation extends this cell with `E,F`
infinite and `X` a proper isometry.  The inference producing `(OCR8)` is not
valid in arbitrary finite tracial representations of the presentation; it
must use finite integer multiplicities or an equivalent matrix-coordinate
selection.

## Attempts

`fanizza-compressed-unitary-has-guarded-rank-floor` shows that `(OCR8)` is
already semantically sufficient: its two displayed estimates contradict
each other by a fixed constant.  It also proves that a literal
group-algebra partial-isometry relation cannot supply `(OCR8)`, because the
canonical regular trace would kill `H`.  The open step is therefore not
another block identity or second cyclic product; it is a finite-coordinate
decoder authenticating source fullness for the selected C18 multiplicity
cut while preserving the one-sided infinite completion.

The smallest root/selector backend is now sharply fenced.
`local-steinberg-heisenberg-packets-are-coefficient-rank-blind` takes
idempotents `e_r in M_n(F_2)` of every nonzero rank.  The roots
`x_12(e_r),x_23(e_r),x_13(e_r)` always form the same D8 packet, and the
ambient regular representation restricts to the same regular D8
multiplicity profile.  Same-root additivity, the idempotency multiplication
triangle, and every fixed abstract selector-automorphism table internal to
the packet are identical while `r/n` ranges from `1/n` to `1`.  Thus mixed
Steinberg additivity plus one finite Heisenberg packet cannot authenticate
`(OCR8)`.

The surviving coefficient route must expose a larger rank/Morita chart and
prove characteristic-zero same-reservoir trace reflection, or activate an
extensive matrix-dependent family of coefficient atoms.  Root additivity
alone controls algebraic multiplication, not the complex adjoint Gram.

There is now also a sharp fence on the first alternative when the proposed
chart is fixed and semisimple.
`fixed-semisimple-trace-charts-cannot-authenticate-proper-fullness` computes
the reflected trace of a projection in
`A=direct_sum_j M_(d_j)(C)` from the irreducible multiplicities.  A rank is
independent of multiplicity exactly when its relative rank is the same in
every simple sector.  If `g<=E` has the same trace as `E` in every finite
representation, this criterion forces `g=E` inside the chart itself.

Hence a fixed two-idempotent overlap table, four-root square, or finite
shared-selector extension has only two outcomes: multiplicity escapes, or
an algebraic fullness identity inherited by the infinite model.  The same
calculation gives the sharp positive residue: a fixed faithful packet has a
dimension-free smallest nonzero projection trace `gamma_A`.  It would
suffice to authenticate the Gram deficiency `E-X^*X` as a projection in the
packet's algebra coordinate; trace below `gamma_A` would force it to vanish.
The packet relations do not distinguish that coordinate from the amplified
multiplicity commutant.  The surviving terminal is therefore
**algebra-factor localization of the Gram deficiency**, or else a growing
matrix-coordinate family / genuinely finite-only non-semisimple law.

The most economical proposed localization by a second fixed packet is now
ruled out exactly.  In
`two-fixed-packet-reynolds-actions-leave-a-gram-spectator`, two transverse
D8/selector packets may generate the whole fixed label factor
`M_4(C) tensor I_N`, but every projection `I_4 tensor Q_N` is fixed by all
their Reynolds tests and has arbitrary trace.  Packet averaging lands in a
commutant, not a bicommutant.  A second fixed semisimple packet cannot equal
the full `I_4 tensor M_N` multiplicity algebra at unbounded `N`.

Thus the localization gate specifically requires a **scalable** transverse
algebra, or one mixed word which changes under every non-scalar spectator
gauge.  A second bounded C18/D8 packet, even noncommuting and sharing the
same selected carrier, does not suffice.

The dual-prefix Pauli tower now gives a precise positive version of that
alternative.  `kazhdan-transitive-pauli-actor-localizes-one-mixed-word`
proves that if a uniformly gapped actor is transitive on the nonzero Weyl
words and approximately fixes the decoded Gram, then one prototype mixed
commutator controls the exact Pauli Reynolds square function.  The resulting
distance from the full Pauli commutant has a constant independent of the
depth `n`, rank `2^n`, dimension, and multiplicity.

The bare Leavitt branches do not contain this actor.  If the transport area
or inverse square-root actor gap grows with depth, arbitrary
defect-versus-dimension schedules prevent choosing a supercritical packet.
Thus the surviving one-word localization gate is specifically a
**uniformly gapped transitive actor for the dual-prefix Weyl tower**, not a
list of pointwise prefix commutators.
