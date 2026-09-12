---
rg: 2
id: one-state-protected-coefficient-leaves-relative-gh-gauge
kind: claim
title: One state-protected coefficient leaves the amplified relative Gowers--Hatami gauge, while one full-trace unitary coefficient fixes it
distinct_from:
  lin-state-dependent-gh-preserves-the-commutant: that gives exact A'-linearity and approximation in one density seminorm; this computes the residual multiplicity gauge seen by that seminorm and the stronger full-trace datum which would remove it.
  lin-canonical-dilation-twirls-unprotected-left-carriers: that shows Lin's explicit isometry Reynolds-twirls an unprotected left operator; this gives an exact amplified counterpacket even when one nonzero coefficient is protected state-dependently.
  one-cross-gram-moment-extracts-the-common-polar-gauge: that extracts a relative commutant unitary after a full cross-Gram mass hypothesis; this identifies the equivalent operator-level unitary coefficient and proves that a one-state substitute is insufficient.
  summed-reynolds-carrier-transports-only-tautologically: that produces a full-carrier extension of the tree-side polar unitary; this determines exactly what form of protection would synchronize its gauge with the P_13 exactification.
  common-gh-isometry-selects-the-two-overlap-cross-coefficient: that obtains the needed full-trace cross coefficient from one common normalized-HS exactification isometry; this counterpacket applies when only unrelated state-dependent protected intertwiners are supplied.
---

**ESTABLISHED.**  Let `sigma:G->U(L)` be any finite-dimensional exact
representation and amplify it as

```text
pi_m(g)=sigma(g) tensor I_m.                            (SPG1)
```

The multiplicity gauges `I_L tensor Q`, `Q in U(m)`, commute with the whole
packet.  Protecting one nonzero coefficient only in a state-dependent norm
does not remove this gauge, even if the state is faithful.

Indeed, on `C^m` put

```text
Q_m=diag(1,-1,...,-1),
rho_m=diag(1-(m-1)/m^3,1/m^3,...,1/m^3).                (SPG2)
```

Let the protected coefficient be the identity, and equip the label factor
with normalized trace and the multiplicity factor with density `rho_m`.
Then `rho_m` is faithful and

```text
||(I_L tensor Q_m)-I||_(2,rho_m)^2=4(m-1)/m^3 ->0,      (SPG3)
||(I_L tensor Q_m)-I||_(2,tr)^2=4(m-1)/m ->4.           (SPG4)
```

Both the original and regauged comparison maps are exact packet
intertwiners, and every local finite-group table is unchanged.  Thus an
amplified exact counterpacket survives one faithful-state protected
coefficient with vanishing state error and asymptotically maximal normalized
Hilbert--Schmidt gauge separation.  With the rank-one density
`rho=|e_1><e_1|`, the protected error is exactly zero.

There is a sharp positive converse at the operator level.  If `B` is a
unitary coefficient between the two multiplicity spaces and `Q_1,Q_2` are
their gauges, then

```text
||Q_2 B Q_1^*-B||_2
 =||Q_2-BQ_1B^*||_2.                                   (SPG5)
```

Consequently protection of one **full-support unitary coefficient in the
ambient normalized trace norm** fixes the relative multiplicity gauge with
constant one.  No amplified counterpacket survives exact operator pinning:
`Q_2 B Q_1^*=B` forces `Q_2=BQ_1B^*`.  A common diagonal gauge remains, as
it must, but it is only simultaneous conjugacy and carries no overlap
holonomy.

More generally, a density-seminorm estimate promotes to normalized-HS only
under a dimension-free domination

```text
rho >= (c/m) I_m,            c>0 independent of m,       (SPG6)
```

in which case `||X||_(2,tr)<=c^(-1/2)||X||_(2,rho)`.
Faithfulness without `(SPG6)` is useless, as `(SPG2)--(SPG4)` show.

For the Kac--Moody terminal, the Reynolds construction already extends its
corner polar coefficient to a full ambient unitary `tilde B_a`.  Therefore
one operator-level normalized-HS protection equation for `tilde B_a` would
indeed synchronize the two overlap gauges by `(SPG5)`.  Lin's theorem does
not supply that equation: it preserves operators in the exact opposite
algebra `A'`, while `tilde B_a` is obtained from a `P_0`-commuting polar
completion and need not commute with the `P_13` packet.  Its one-state norm
alone leaves the counterpacket `(SPG2)`.

The residual bridge is consequently exact and minimal: construct the
`P_13` finite-group exactification so that the full-trace coefficient
`Q_2 tilde B_a Q_1^*` remains close to `tilde B_a`, or prove a
dimension-free density domination which makes the state-dependent estimate
equivalent to that operator equation.  Merely asking for commutant
preservation or one faithful state does not suffice.
This state-dependent obstruction does not survive the stronger hypothesis
that both overlap comparisons come from the **same** normalized-HS
Gowers--Hatami isometry.  In that setting
`common-gh-isometry-selects-the-two-overlap-cross-coefficient` derives the
full-trace cross coefficient directly.  Its remaining obstruction is exact
simultaneous invariance, not multiplicity-gauge selection.
