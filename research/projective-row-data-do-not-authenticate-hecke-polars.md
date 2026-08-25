---
rg: 2
id: projective-row-data-do-not-authenticate-hecke-polars
kind: claim
title: Projective native-row data do not authenticate the center-chain Hecke polars
invalidates:
  - hecke-square-covariance-authentication
artifacts:
  - research/projective-row-gauge-countermodel-proof.md
distinct_from:
  fixed-center-chain-hecke-occurrence-is-regularly-impossible: that uses the affine trace equations to rule out a fixed exact occurrence identification on the regular Hecke corner; this gives a finite-matrix Morita gauge which preserves every separately projective row datum while separating the native and Hecke transports.
  vanishing-loss-center-chain-authentication-hits-affine-firewall: that gives the contradiction after vanishing-loss authentication; this identifies an exact class of row relations which cannot supply that authentication.
  native-whitehead-corner-collapses-hecke-flags: that computes the literal two Whitehead words on the fixed Hecke support; this applies to any proposed row transport whose tested relations are even in that transport.
---

**ESTABLISHED PROJECTIVE-GAUGE FENCE.**  Let

```text
S:QH -> PH
```

be any one of the common-source center-chain Hecke maps, and let `W` be a
candidate native transport with the same source and range.  The following
data are all unchanged by adjoining a spectator involution `D` and replacing

```text
W  by  W tensor D:                                      (PNG1)
```

1. the source and range projections `W^*W` and `WW^*`;
2. every covariance `W R W^*=T` with the packet operators amplified by the
   identity;
3. every prescribed square `W^2=g`, provided `D^2=1`; and
4. every relation in which the total exponent of `W` is even after the
   packet letters have been removed.

Take `D` to be a balanced involution, `tr(D)=0`.  The Hecke map and every
allowed fixed packet-label relabeling amplify as `L S tensor 1`, whereas
the gauged native transport has the form `W tensor D`.  If the two maps have
common source mass `t`, then

```text
<W tensor D, L S tensor 1>_2=0,
||W tensor D-L S tensor 1||_2^2=2t.                    (PNG2)
```

The same construction may be performed independently for both native rows,
using the regular representation of `(C_2)^2` as the spectator.  Hence the
two polar-square identities, the two separate native selector covariances,
the correct source/target ranks, and the exact internal Hecke common-source
factorization can all hold while each proposed native transport stays a
fixed Hilbert--Schmidt distance from its Hecke map.  Amplification leaves
all normalized packet traces unchanged.

Consequently separately projective native-row data cannot prove
`center-chain-common-source-authenticates-native-covariances`, even with
zero relation defect.  A viable proof must use, for each native transport,
an **odd-parity occurrence anchor** tying that transport to an ungauged
packet word (or a mixed relation whose gauge parity has the same effect).
The identities `u_i^2=g_i` and the native conjugation rows do not provide
such an anchor.

This is a scoped language obstruction, not a refutation of the full native
authentication claim.  The full affine-Leavitt presentation may contain a
load-bearing mixed occurrence relation which breaks `(PNG1)`; proving a
dimension-free normalized-Hilbert--Schmidt estimate from that relation is
now the exact surviving leaf.

DERIVATION
projective-row-gauge-countermodel-proof
