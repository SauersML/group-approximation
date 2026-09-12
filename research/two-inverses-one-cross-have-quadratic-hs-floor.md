---
rg: 2
id: two-inverses-one-cross-have-quadratic-hs-floor
kind: claim
title: Two inverse rows and one crossed-zero row have a quadratic same-corner HS floor
distinct_from:
  approximate-relative-leavitt-cell-kills-active-trace: that uses two diagonal inverse rows and the binary range-sum row and obtains a linear trace bound; this replaces the range sum by one crossed-zero row and obtains a quadratic bound.
  outer-root-leavitt-table: that authenticates the coefficient products as group roots but does not decode their coefficient maps on one finite matrix corner; this is the post-decoding finite-matrix inequality.
  mixed-steinberg-loops-admit-morita-rectangular-model: that realizes these three rows exactly with source and target as different objects; this assumes one common finite projection and thereby pinpoints the missing object-erasing decoder.
  partial-whitehead-cell-has-marked-finite-model: that shows one inverse pair has a marked scalar specialization; this proves that adding a second inverse pair and one crossed-zero row is the support-minimal finite-algebra obstruction.
---

**ESTABLISHED.**  Let `(M,tau)` be a finite tracial von Neumann algebra,
let `P in M` be a projection, and let

```text
s_0,t_0,s_1,t_1 in PMP
```

be contractions.  Put

```text
q=tau(P),
epsilon_i=||t_i s_i-P||_2       (i=0,1),
eta=||t_0s_1||_2,
E=epsilon_0+epsilon_1.                              (TIC1)
```

Then

```text
q <= eta^2+2 sqrt(q) E,                              (TIC2)
sqrt(q) <= E+sqrt(E^2+eta^2) <=2E+eta,               (TIC3)
q <=(2epsilon_0+2epsilon_1+eta)^2.                   (TIC4)
```

Thus two approximate diagonal inverse relations and **one** crossed-zero
relation kill their common carrier with a dimension-independent quadratic
normalized-HS estimate.  If all three defects are at most `delta`, then

```text
tau(P)<=25 delta^2.                                  (TIC5)
```

The exact coefficient obstruction is support-minimal.  No nonzero
finite-dimensional unital algebra can contain four elements satisfying

```text
t_0s_0=1,          t_1s_1=1,          t_0s_1=0.       (TIC6)
```

Indeed finite-dimensional algebras are directly finite, so the first row
makes `t_0` invertible; the crossed row then gives `s_1=0`, contradicting
the second row.  Deleting any one of the three rows admits a one-dimensional
model with active unit `1`: set the missing branch to zero if an inverse row
was deleted, and set all four coefficients to `1` if the crossed row was
deleted.

This sharpens the affine-Leavitt endpoint.  After a matrix-coordinate decoder
places `s_i,t_i` on the same marked corner, neither the range-sum relation nor
both crossed-zero relations are needed: `(TIC4)` already collapses that
corner.  Conversely these three coefficient identities are all well typed in
the rectangular Morita model (`s_i:E->E direct_sum E`, `t_i:E direct_sum E->E`),
so their ordinary Steinberg root rows alone cannot imply the common-corner
hypothesis.  The remaining group theorem is exactly an object-erasing,
payload-coupled decoder for this three-row cell.

The common-corner hypothesis can now be weakened sharply.
`rectangular-three-row-cell-forces-double-target-capacity` proves that for
rectangular coefficients `s_i:E->F`, `t_i:F->E`, the same three rows force
`tau(F)>=2tau(E)`, robustly with an explicit normalized-HS ledger.  Hence the
missing decoder need not prove `F=E`: any fixed conditional target-capacity
deficit below `2tau(E)` suffices.  The exact Morita countermodel is the sharp
equality case `tau(F)=2tau(E)`.

DERIVATION
two-inverses-one-cross-hs-proof
