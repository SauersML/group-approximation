---
rg: 2
id: positive-signed-actor-two-scale-profile-is-partial-and-gauged
kind: claim
title: Some positive signed actors have two endpoint scales but the root-free detector frontier does not
artifacts:
  - research/positive-signed-actor-two-scale-profile-proof.md
  - experiments/all_positive_detector_two_scale_profile_audit.py
distinct_from:
  exceptional-endpoint-detector-products-stay-at-depth-three: that closes products of the three final endpoint classes; this exhausts all positive nonidentity L0 conjugacy classes and both endpoint-cell orientations.
  five-return-legs-cover-hecke-detectors-not-source-gauge: that uses non-source-preserving Pauli probes to extract roots from twenty-eight of the thirty-one root-free classes; this tests whether the actor itself already has two fixed-source native-depth incidences.
  endpoint-detector-cell-retains-coboundary-gauge: that moves a depth-three root-free occurrence with endpoint Whiteheads; this finds a genuine fixed-Q two-depth occurrence outside the root-free frontier and identifies its remaining independent gauge.
  simultaneous-endpoint-prefix-whitehead-moves-source-before-locking-gauge: that supplies the natural ordinary word conjugating the two concrete g-star cells and computes its signed-source intersection; this stops before adding that mixed word.
---

**ESTABLISHED COMPLETE POSITIVE-ACTOR PROFILE AUDIT.**  For a positive
nonidentity `L_0` actor `g`, put

```text
C_Y(g)={m: some (r,k_m) entry of g is 1, r in {2,4}},
C_X(g)={m: some (k_m,r) entry of g^(-1) is 1, r in {2,4}},
(k_1,k_2,k_3)=(7,8,9).                               (PSA1)
```

The first profile records cells obtained from `[g,Y_m]` and the matching
endpoint `A_(r,m)`.  The second records the transposed cells obtained from
`[g,X_m]` and a matching endpoint `B_(r,m)`.

There are `511` positive nonidentity conjugacy classes in `L_0`.  Exactly
`184` have a representative with adjacent `C_Y` profile, and every such
profile uses depths `(2,3)`.  The other `327` classes have no adjacent
profile.  No class has any nonempty `C_X` profile.  More precisely, the
classwise `C_Y` profile-set counts are

```text
{3}:176,       {2,3}:152,       empty:63,
{2}:56,        {empty,{3}}:32,  {{2},{2,3}}:32,        (PSA2)
```

and all `511` inverse-row profile sets are empty.

There is a particularly small genuine fixed-source occurrence.  Let

```text
g_*=x_28(1)x_49(1) in L_0.                             (PSA3)
```

Both factors, and hence `g_*`, have positive signed character, so `g_*`
acts as the identity on `Q`.  Ordinary Steinberg collection gives

```text
[g_*,Y_2]=x_23(b_2),
[x_12(a_2),[g_*,Y_2]]=z,
[g_*,Y_3]=x_43(b_3),
[x_14(a_3),[g_*,Y_3]]=z.                              (PSA4)
```

Thus a two-scale fixed-`Q` actor occurrence genuinely exists.  It is not a
universal detector compiler.  Among the `31` positive root-free conjugacy
classes singled out by the signed detector audit, `23` have only profile
`{3}` and `8` have empty profile; all `31` have empty inverse-row profile.
In particular none of the `28` root-free classes repaired by external Pauli
probes, nor the final three endpoint classes, has an adjacent actor profile
before the source is moved.

The occurrence `(PSA4)` also does not by itself compare native gauges.
Its two cells split through the commuting positive factors `x_28(1)` and
`x_49(1)` and land at different endpoint charts.  In the scoped occurrence
table one may dress `Y_2,Y_3` by two independent commuting multiplicity
involutions.  These spectators cancel inside `[g_*,Y_m]`, so every identity
in `(PSA4)` remains exact, while the two full edges retain independent
gauges.  No source/range Gram or ordinary return word in `(PSA4)` identifies
their targets.

Consequently the newly found cell is useful occurrence data but does not
close the arbitrary-profile cross-Gram claim.  The paying detector may lie
in any of the `327` nonadjacent classes, and the entire hard root-free
frontier lies there.  A successful continuation must still type a moving
probe or add a fixed-frame target relation.  No Property `(T)`, canonical
trace, literature input, local computation, or Lean compilation is used.

The shortest natural target relation is now known and confirms this exact
boundary.  `simultaneous-endpoint-prefix-whitehead-moves-source-before-locking-gauge`
multiplies the endpoint `(2,4)` partial Whitehead by the native `(8,9)`
prefix Whitehead.  The resulting involution fixes `g_*` and conjugates the
whole depth-two cell to the depth-three cell.  It also moves `Q`: its signed
intersection has order only `16`, with a canonical overlap `tau(Q)/512`,
and an exact two-character profile makes the two source charts orthogonal.
Thus the global cell conjugacy does not remove the independent gauges on
their restrictions to the original `Q`.

DERIVATION
positive-signed-actor-two-scale-profile-proof
