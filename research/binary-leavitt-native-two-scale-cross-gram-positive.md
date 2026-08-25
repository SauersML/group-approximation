---
rg: 2
id: binary-leavitt-native-two-scale-cross-gram-positive
kind: claim
title: The two native binary scale transports have a fixed positive cross-Gram corner
distinct_from:
  opnorm-leavitt-coarse-fine-return-row: that asks for one operator-norm support row on one sparse carrier; this asks for one normalized-HS positive overlap between two positive-density transports.
  affine-leavitt-source-saturated-reynolds-checksum: that asks for a source-sized adjoint Reynolds overlap in an odd affine packet; this permits any fixed positive direct polar Gram overlap in the binary packet.
---

**NORMALIZED-HS SCALAR HOLONOMY CLAIM.**  On the positive-density active core
of a canonical-trace binary-Leavitt Steinberg microstate, exactify the fixed
depth-one and next-refinement Pauli packets and stabilize their two
scale-changing coefficient transports to contractions

```text
S_1,S_2 : P_source H -> P_target H.
```

Prove, with constants depending only on the fixed packet and ordinary
Steinberg word defects, that

```text
tau(S_1^*S_2S_2^*S_1) >= gamma tau(P_source)-o(1)      (NCG1)
```

for one fixed `gamma>0`, and that the two mixed source-Pauli commutators of
the relative polar gauge are `o(1)` on the resulting overlap corner.  The
source and target stabilizations must be the ones used by the selector rows
with ratios `1/2 -> 1/4` and `1/4 -> 1/8`; unrelated rectangular
completions do not count.

Full cross Gram is unnecessary.  By
`two-transport-cross-gram-has-a-fixed-mass-reducing-corner`, `(NCG1)` gives
a fixed positive approximately reducing source corner.  Fixed finite-packet
commutant exactification makes it reducing with dimension-free loss.  The
polar part identifies the two transport gauges on corresponding positive
subcorners, and
`two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge` puts the
relative unitary in the common multiplicity reservoir.  The two external
involutions then have the same positive spectral fraction on that subcorner,
so the affine rank obstruction supplies the fixed `1/3` row-defect floor
there.

A sufficient front end is strict target capacity.  If two incoming
contractions of total squared mass `M_tot` land in a common target `Q` with
`M_tot>(1+kappa)tau(Q)` for fixed `kappa>0`, then
`contraction-branch-capacity-forces-collision` gives `(NCG1)` quantitatively.
Thus the new route may be closed either by a direct overlap calculation or
by any native binary packet flag giving a strict capacity deficit.  Merely
meeting the doubled rectangular capacity is critical and gives no overlap.

There is now a second sufficient front end with no capacity surplus.  By
`root-valued-relative-transport-forces-cross-gram`, if the two stabilized
native transports are the restrictions `S_i=g_iP_source` of full group
unitaries and

```text
(g_1^(-1)g_2) z (g_1^(-1)g_2)^(-1)=x_42(a),    a!=0,   (NCG1a)
```

then `(NCG1)` holds with `gamma=1/4`.  Consequently the scalar estimate is
finished once this root-valued relative-word typing is authenticated for the
actual selector occurrences.  A relative identity for unrelated unitary
completions does not qualify.

Positive-density active-core reblocking does not make this inequality
strict.  `active-core-density-keeps-rectangular-capacity-critical`
places the exact nested Pauli rectangular model inside the whole active
carrier: label degree doubles, multiplicity halves, total carrier rank stays
constant, and the two child ranges remain orthogonal.  Fixed-depth rank
integrality is absorbed by amplification.  Therefore `(NCG1)` must come from
an object-erasing occurrence row or a genuine strict-capacity flag, not from
density or divisibility.

## Exact direct/composite audit

The most tempting fixed-depth certificate is algebraically correct but does
not prove `(NCG1)`.  With

```text
x_1=s_(00)t_0,       x_2=s_(000)t_(00),       x=s_(000)t_0,
```

one has exactly

```text
x_2 x_1=s_(000)(t_(00)s_(00))t_0=s_(000)t_0=x.        (NCG2)
```

Thus the direct prefix arrow and the two-step prefix arrow are the same
coefficient in the Leavitt algebra.  Cairn's
`mixed-steinberg-loops-admit-morita-rectangular-model` already checks the
corresponding Steinberg multiplication triangles.  In that model `(NCG2)`
is ordinary associativity of rectangular maps, but the depth-one source,
intermediate object, and depth-two target have different identity
projections.  After the Whitehead stabilizations, the two completed paths
can occupy different ordered carriers.  Hence `(NCG2)` gives full typed
self-Grams without the untyped positive cross Gram `(NCG1)`.

The stronger Whitehead/swap completion is also already refuted by
`whitehead-swap-copy-completion-retains-rectangular-escape`: it copies the
missing corner and exposes the full target Pauli factor, but exchanges label
dimension for spectator multiplicity.  Therefore the open scalar cannot be
deduced from more multiplication triangles, Hall--Witt reassociation,
branch swaps, or the direct/composite prefix equality alone.  It requires
one genuinely object-erasing mixed row, a strict target-capacity packet, or
a finite-coordinate polar choice whose loss is charged by an ordinary word
defect.

## Existing Pauli Gram floors do not instantiate `(NCG1)`

There are two established positive-overlap calculations nearby, but their
types do not match the two selector transports.

First, `pauli-canonical-return-gram-floor` uses

```text
A_0=EU:R_0H -> EH,             A_1=ERU:R_1H -> EH,
```

where `R_0R_1=0` and `tau(R_0)=tau(R_1)=tau(E)=1/8`.  Its maximal Gram
energy comes from the common **final** projection `E`; the two initial
projections are distinct orthogonal Pauli children.  Thus `A_0^*A_1` is an
arrow from `R_1H` to `R_0H`, not a relative endomorphism of the one prescribed
source packet carrying both selector gauges.  Identifying either child with
that source would be precisely an additional object-erasing return.

Second, `pauli-packet-incoming-mass-exceeds-corner-capacity` gives

```text
X_i=Q(comb^*B_i comb)Q:QH -> QH
```

and forces total ordered cross-Gram mass `5/32`.  These two maps do have one
source and target, but they are same-scale compressed raw/comb involutions,
not the depth-one and next-refinement coefficient transports used in the
`1/2 -> 1/4` and `1/4 -> 1/8` selector rows.  The exact finite Atlas packet
already pays this overlap while retaining the unlabelled relative
multiplicity freedom; `pauli-overlap-floor-is-subcritical-for-extension-authentication`
records that even its positive spectral corner does not authenticate a
labelled transport gauge.

Finally, `dyadic-pauli-payload-flags-supply-strict-target-capacity` supplies
a strict scalar capacity deficit only for a separately named BCS flag pair.
Its sharp regular-trace fence proves that functorially attaching the three
Leavitt rectangular rows to that pair is impossible.  The attachment is the
same occurrence-synchronization problem, not an available strict-capacity
front end for `(NCG1)`.

Consequently none of these three established Pauli results closes the live
claim.  A valid proof must still exhibit a word-visible row that couples the
two actual scale-changing occurrences, or calculate strict capacity for
their own prescribed common target.

Normal saturation now supplies a direct common ambient carrier, but not yet
the required mutual overlap.  In the uniform binary-Leavitt double
commutator the output commutes with both conjugators, so
`commuting-double-commutator-has-direct-mark-overlap` puts at least `1/4` of
every nonzero `x_42(a)` output root carrier, and every marked-index-disjoint
Weyl translate, directly inside the original marked carrier.  Two such
slices may nevertheless be disjoint while each occupies only `1/16` of the
marked mass.  Moreover, these root spectral slices are not yet the prescribed
selector transport Grams.  Thus the result removes the conjugate-selection
ambiguity on the disjoint root rectangle and provides a canonical ambient
corner for an occurrence decoder, but does not itself instantiate `(NCG1)`.

Equivalently, the remaining algebraic shortcut is now sharply testable: show
that the actual two stabilized selector transports satisfy `(NCG1a)`.
The direct/composite coefficient equality `(NCG2)` alone does not do this,
because its rectangular completions need not be restrictions of two full
unitaries on the marked source projection.  This is precisely the typing
loophole realized by the existing Morita model.

There is a broader finite-character version of the same test.
`binary-native-selector-atom-hecke-dichotomy` adjoins the commuting
nine-root packet to the marked root and cuts by one character atom.  If the
two actual selector contractions are restrictions `g_i e_chi` of their
fixed group words, then the cross-Gram is computed exactly by

```text
I=H intersect (g_1^(-1)g_2)H(g_1^(-1)g_2)^(-1).
```

Compatible transported characters give `(NCG1)` with
`gamma>=2^(-9)`; incompatible characters make the Gram exactly zero.  This
removes every multiplicity-reservoir ambiguity after occurrence typing, but
does not supply that typing or the relative-action calculation.  In
particular the proposed tridiagonal sign atom is invariant under reversal,
not under the adjacent-swap three-cycle, so its overlap cannot be assumed
without computing the actual relative selector action.

There is nevertheless now a fixed nonadaptive common carrier available for
an occurrence compiler.  `seventeen-root-star-has-marked-triple-overlap`
proves that the prescribed roots `x_42(q)` and `x_52(q)` have triple overlap
at least `(7/136)tau(P_z)` with the mark.  Weyl two-transitivity, rather than
coordinatewise pair selection, supplies this pair.  These are same-coefficient
root-position channels, so substituting their Weyl maps for the two native
unequal-scale coefficient transports would erase the selector semantics.
The remaining task is to install the actual two scale rows on this common
root carrier or authenticate `(NCG1a)` for their own relative word.

Moreover the prescribed intersection with `x_62(q)` remains positive.
`marked-root-star-carries-three-anchored-cells` uses it to put three
cross-commuting `q`-centered Heisenberg cells on one carrier.  Their arm
coefficients factor the two native scale arrows as

```text
s_(00)t_0=(s_(00)t_1)(s_1t_0),
s_(000)t_(00)=(s_(000)t_1)(s_1t_(00)).                 (NCG3)
```

Thus neither common positive carrier nor simultaneous finite packet syntax
is still missing for these anchored arms.  What `(NCG3)` does not yet prove
is that the separate root occurrences of its factors compose as the two
selector transport operators on that carrier; that is now the exact
same-occurrence row to authenticate.

Abstract trace cyclicity does not supply that coupling either.
`trace-cyclic-balance-does-not-bypass-native-two-scale-occurrence` shows that
a third balance pair can equate the two gauge ranks only after its cyclic
products have been authenticated as the two actual gauge projections on
equal normalized carriers.  That authentication is itself an object-erasing
native occurrence row; the typed Morita model continues to realize all
coefficient triangles while leaving it absent.  The two-oriented version
assumes an even stronger input, namely one literal hidden gauge projection
shared by both returns.

The adjacent-prefix braid identifies why a purely relational repair cannot
compare the unequal controlled label factors.  By
`unequal-label-ranks-forbid-relational-reservoir-conjugacy`, an exact
separated tensor relation which conjugates the reservoir factors would also
conjugate the `1/4` and `1/8` label involutions, which is impossible.

The attempted same-center closure is invalidated by
`same-center-whitehead-gram-is-not-native-selector-gram`.  Compressing the
two Whitehead words to their common reducing carrier makes both maps
unitaries, so their full Gram equals the carrier trace for the tautological
reason `S_m^*S_m=F`.  Their proved label actions are still the two
one-quarter adjacent swaps.  No word in that calculation authenticates the
separate one-eighth controlled selector or makes it inherit the second
reservoir gauge.  Consequently the common carrier and braid are real
progress, but they do not close `(NCG1)`.

## Norm scope

The claim itself is normalized-Hilbert--Schmidt and is meant to apply to
canonical-trace microstates.  Operator-norm packet exactification may be used
in the separate MF-radical lane, but it cannot serve as the occurrence
authentication here.  A valid route must supply its own HS estimate on the
actual selector occurrences.
