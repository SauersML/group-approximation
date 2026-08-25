---
rg: 2
id: binary-leavitt-native-two-scale-cross-gram-positive
kind: claim
title: The two native binary scale transports have a fixed positive cross-Gram corner
distinct_from:
  opnorm-leavitt-coarse-fine-return-row: that asks for one operator-norm support row on one sparse carrier; this asks for one normalized-HS positive overlap between two positive-density transports.
  affine-leavitt-source-saturated-reynolds-checksum: that asks for a source-sized adjoint Reynolds overlap in an odd affine packet; this permits any fixed positive direct polar Gram overlap in the binary packet.
---

**OPEN SCALAR HOLONOMY CLAIM.**  On the positive-density active core of a
binary-Leavitt Steinberg microstate, exactify the fixed depth-one and
next-refinement Pauli packets and stabilize their two scale-changing
coefficient transports to contractions

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

Abstract trace cyclicity does not supply that coupling either.
`trace-cyclic-balance-does-not-bypass-native-two-scale-occurrence` shows that
a third balance pair can equate the two gauge ranks only after its cyclic
products have been authenticated as the two actual gauge projections on
equal normalized carriers.  That authentication is itself an object-erasing
native occurrence row; the typed Morita model continues to realize all
coefficient triangles while leaving it absent.  The two-oriented version
assumes an even stronger input, namely one literal hidden gauge projection
shared by both returns.
