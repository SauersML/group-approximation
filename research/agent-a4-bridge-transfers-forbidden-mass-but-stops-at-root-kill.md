---
rg: 2
id: agent-a4-bridge-transfers-forbidden-mass-but-stops-at-root-kill
kind: claim
title: An A4 bridge transfers forbidden Reynolds mass to two payload roots but does not robustify their finite-dimensional invisibility
distinct_from:
  agent-aggregate-escape-a4-bridge-lands-at-bcl-root-gate: That replaces literal identification of the two A4 generators by conditional finite Fourier corners so the intended perfect coefficient model remains available; this audits the stronger literal C3-amalgam proposal and separates abstract Bass--Serre survival from extension of that model.
  bcs-atom-detects-its-e5-central-root: That asks one Steinberg coefficient model to identify a BCS atom with its own root spectral carrier; this uses an external finite triangle group to force root displacement, but still cannot kill the displaced root in normalized-HS microstates.
  agent-free-compressor-full-corner-root-is-fd-invisible: That kills a BCL payload root in every exact finite-dimensional representation; this converts BCS forbidden mass into displacement of such roots and proves that the remaining implication is exactly the asymptotic upgrade `(FCI3)`.
  agent-first-hit-cross-holonomy-does-not-reflect-named-corner: That allows an inverse projective phase to live on an independent factor; the A4 triangle has no scalar inverse-phase escape, but its root spectral carrier still need not be a BCL coefficient-module corner.
---

For one forbidden Reynolds subgroup `H_i`, choose `h_i in H_i` and put
`g_i=h_iJ`.  Assuming `g_i` has order exactly two, attach

```text
A4_i=<z_(i,1),z_(i,2) |
       z_(i,1)^3=z_(i,2)^3=(z_(i,1)z_(i,2))^2=1>
```

by identifying

```text
z_(i,1)z_(i,2)=g_i.                                  (A4B1)
```

The triangle presentation is `A4`, and the attachment is the ordinary
amalgam over `<g_i> congruent C2`.  Hence it embeds the old group whenever
`<g_i>` is an injected `C2`.

Let

```text
E_i=e_(H_i) Q_-.
```

In an exact unitary representation, `h_i E_i=E_i` and `JE_i=-E_i`, so
`g_iE_i=-E_i`.  From `(A4B1)` and the triangle inequality,

```text
2 sqrt(tau(E_i))
 <=||(z_(i,1)-1)E_i||_2+||(z_(i,2)-1)E_i||_2.
```

Therefore

```text
||z_(i,1)-1||_2^2+||z_(i,2)-1||_2^2
 >=2 tau(E_i).                                       (A4B2)
```

Fixed finite-group correction gives the robust version with an
`O(sqrt(E_pres))` loss.  Summing `(A4B2)` over the finite forbidden menu and
using the robust BCS gap gives

```text
sum_(i,k)||z_(i,k)-1||_2^2
 >=c_B tau(Q_-)-C_B sqrt(E_pres)                      (A4B3)
```

for fixed `c_B>0`.  Thus the proposed bridge genuinely solves the
payload-to-root **displacement** direction; no simultaneous selection or
first-hit transport is needed.

Now amalgamate each `<z_(i,k)> congruent C3` with a BCL Steinberg copy by
identifying it with the payload root `x_12(P_f)`.  In every exact
finite-dimensional representation the BCL theorem kills every such root,
so `(A4B1)` kills `g_i`, and hence `E_i=0`.  Across the complete forbidden
menu the exact finite-dimensional endpoint kills the negative BCS carrier.

This does not prove the corresponding normalized-HS statement.  The BCL
root is already an exact finite cyclic subgroup, and its nontrivial spectral
projection already has density comparable to `||x_12(P_f)-1||_2^2` by
`(BCK2)`.  The A4 bridge adds only the lower bound `(A4B3)`.  It supplies no
coefficient action on that spectral projection and no identification of it
with the named `(BCL0)` corner.  Consequently the full selected
simple-block Fourier hull and the HNN Reynolds mismatch still require
`hs-steinberg-bcs-corner-kernel-is-linear-sofic` (or an equivalent native
normalized-HS root-kill estimate).  Exact finite-dimensional invisibility
cannot be passed through a matrix ultraproduct without precisely that
theorem.

There are also two exact-completeness conditions which must not be hidden:

1. the cyclic maps used in the amalgams must be injective: `g_i!=1` and the
   BCL payload root must have order exactly three in the abstract BCL group;
2. the designated perfect BCS **coefficient** model does not extend across
   the literal payload-root amalgam: in that model the conditional BCL
   idempotent is zero, hence its root is `1`, whereas an injected A4
   generator has order three.  Bass--Serre survival of the old abstract
   group is weaker and does not repair this representation-level failure.

Thus the A4 bridge is a valid and useful reduction, but its beautiful
cascade ends at the already isolated implication

```text
vanishing BCL relator defect
   => ||x_12(P_f)-1||_(2,d) -> 0.                     (A4B4)
```

Proving `(A4B4)` for the finitely many copies would finish the abstract
amalgam bridge once cyclic injectivity is known.  To retain the intended
perfect coefficient model one must instead use the conditional Fourier
corner construction in
`agent-aggregate-escape-a4-bridge-lands-at-bcl-root-gate`; neither version
proves `(A4B4)`.
