---
rg: 2
id: free-s3-atom-has-unit-opnorm-leakage
kind: claim
title: A free marked S3 type has unit operator-norm return leakage
artifacts:
  - research/free-s3-atom-opnorm-leakage-proof.md
  - experiments/free_s3_atom_opnorm_leakage_audit.py
distinct_from:
  arbitrary-profile-selector-type-menu-dichotomy: that classifies cross-Gram mass orbitwise for arbitrary trace profiles and exhibits the free marked orbit; this proves that on that orbit every nonzero character subcarrier has operator-norm return leakage exactly one.
  active-core-density-keeps-rectangular-capacity-critical: that gives zero cross Gram from orthogonal rectangular branch ranges at arbitrary positive density; this uses the actual free marked normalizer type and shows that even coordinate-dependent nonzero spectral cuts cannot improve the return.
  opnorm-leavitt-coarse-fine-return-row: that asks the full binary-Leavitt presentation to force one return row with leakage tending to zero; this fences derivations using only active-core reblocking and the authenticated nonidentity S3 normalizer menu.
  order-seven-anchor-stops-at-whitehead-compression-leakage: that gives an HS telescope after a moving carrier has small boundary at every needed stage; this shows an exact marked type where the first nonidentity atom return has operator-norm boundary one on every nonzero subcut.
---

**ESTABLISHED ARBITRARY-PROFILE OPNORM FENCE.**  Let

```text
H=<z> times (C_2)^9
```

be the marked character packet and let the simultaneous row/column `S_3`
action be the authenticated same-center prefix action.  Use the marked
character `chi_*` with

```text
chi_*(z)=-1, chi_*(C_32)=-1,
chi_*(C_ij)=+1 for (i,j)!=(3,2).                      (FSL1)
```

Its `S_3` orbit is free.  In the orbit representation on `l^2(S_3)`, the
central mark is therefore `-I`, so the active spectral projection is the
whole six-dimensional carrier.  If `e=e_(chi_*)` is its coordinate
character projection and `u` is any nonidentity element of the native
`S_3` normalizer menu, then

```text
e u e=0,                 ||(1-e)u e||_op=1.           (FSL2)
```

More strongly, after arbitrary multiplicity amplification, every nonzero
projection `0!=P<=e` satisfies

```text
||(1-e)uP||_op=1.                                     (FSL3)
```

Indeed `u e u^*` is an atom orthogonal to `e`, so `uP` lies wholly in
`1-e`; the restriction of `u` to `P` is an isometry.  Thus a
coordinate-dependent nonzero subcut cannot turn this zero cross Gram into
an operator-norm return.  The obstruction is not dilution: the marked
active core already has density one, and common amplification preserves
`(FSL2)--(FSL3)`.

Consequently active-core reblocking, fixed-packet operator-norm
exactification, and the entire authenticated nonidentity adjacent-swap/
three-cycle menu do not force a nonzero source-return carrier.  Any proof of
`binary-leavitt-arbitrary-profile-native-cross-gram` or
`opnorm-leavitt-coarse-fine-return-row` must either

1. authenticate an identity-action relative occurrence on this marked type;
2. add a full-presentation relation which excludes or pays the free orbit;
   or
3. use a root-valued relative occurrence outside the `S_3` atom-return
   mechanism.

This is a countermodel to the finite normalizer action table, not to extra
binary-Leavitt relations not represented by that table.  No Property T,
canonical trace, literature input, local computation, or Lean compilation
is used.

## Full-root payment audit

Completing the signs by dual Heisenberg roots would pay this free orbit, but
only if the duals belong to the **same occurrence packet**.  If nine
involutions `D_ij` satisfied

```text
[C_ij,D_kl]=z^(delta_(i,k)delta_(j,l))
```

and the relative `S_3` actors simultaneously permuted both the `C` and `D`
rows, the `D_ij` would flip the nine sign coordinates transitively.  Every
marked character atom would then have the same rank in an arbitrary finite
matrix profile.  A transposition has one fixed coordinate and four
two-cycles on the nine ordered pairs, hence fixes `2^5=32` of the `2^9`
characters.  Its fixed-atom return carrier would have rank exactly
`rank(P_z)/16`, with zero operator-norm leakage.  Thus the abstract free
orbit cannot survive as the entire active profile after such a same-packet
dual completion.

This observation does not add a new live relation.  The stronger literal
three-pair version is already
`middle-index-marked-heisenberg-packet-is-whitehead-equivariant`: its actual
prefix duals are normalized by the actual Whiteheads and give a common
fixed atom of mass `rank(P_z)/8`.  The auxiliary nine-pair frame of
`nine-pair-marked-heisenberg-regularization-is-selector-spectator` commutes
with the native selector occurrences and therefore leaves their reservoir
overlap unchanged.

Most importantly, the unequal center-chain selector occurrences do not
normalize the literal three-pair frame.  By
`middle-index-heisenberg-packet-is-not-center-chain-invariant` they eject
the nonzero roots

```text
[A_m,Y_m]=x_(r_m,3)(q),       [X_m,B_m]=x_(1,s_m)(q).
```

Demanding same-frame normalization would force these coefficients, hence
`q`, to vanish.  Closing the ejected roots instead gives the finite,
scale-neutral packet of
`middle-index-order-seven-orbit-cut-is-native-scale-neutral`.  Therefore
the precise unresolved full-presentation datum is not the existence of
dual roots or their prefix-Whitehead covariance; it is a new mixed
occurrence that couples the unequal selector source while returning a
positive part of this dual frame.  The known literal duals either remain a
spectator or are ejected.

DERIVATION
free-s3-atom-opnorm-leakage-proof
