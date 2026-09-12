---
rg: 2
id: agent-a4-bridge-mass-transfer-and-trace-gluing
kind: route
title: Compute the A4 displacement inequality and separate abstract from coefficient-model completeness
target: agent-a4-bridge-transfers-forbidden-mass-but-stops-at-root-kill
requires:
  - non-ce-bcs-has-robust-approximate-energy-gap
  - agent-free-compressor-full-corner-root-is-fd-invisible
  - agent-packet-root-finite-detectors-are-normal-quotient-selectors
  - agent-packet-root-bridge-is-perfect-kernel-separation
---

The exact estimate is the displayed two-term telescoping identity

```text
(z_1z_2-1)E=z_1(z_2-1)E+(z_1-1)E.
```

On the forbidden carrier the left side is `-2E`.  Cauchy--Schwarz gives
`(A4B2)`.  For an approximate presentation, first correct the fixed finite
subgroups `H_i`, `<J>`, and `A4_i`; telescoping the corrections and the one
bridge relator changes the inequality by a presentation-dependent
`O(sqrt(E_pres))`.  There are finitely many types, so summing and applying
the BCS gap gives `(A4B3)` with dimension-free constants.

For group-theoretic perfect completeness, Bass--Serre normal form embeds
both factors in

```text
G_base *_(<g_i>=C2) A4_i
```

and then embeds `A4_i` and each BCL copy in the subsequent `C3` amalgams,
provided every displayed cyclic map is injective.  Hence the old mark `J`
survives abstractly without extending a preselected representation.

For a **pure independent cyclic amalgam**, a tracial extension can be
arranged after harmless dilution, conditional on cyclic injectivity.  Mix
the perfect base trace with a `J=+1` character until every

```text
t_i=tau(g_i)
```

lies in `[-1/3,1]`; the negative-sign mass remains positive and the forbidden
projections remain zero.  The convex combination of the trivial and
three-dimensional irreducible normalized characters of `A4`, with trivial
weight

```text
a_i=(3t_i+1)/4,
```

has value `t_i` on the double transposition and value `a_i` on both powers
of the selected `3`-cycle.  On a BCL copy, mix its trivial character with
weight `a_i` and its canonical group trace with weight `1-a_i`; if the
payload root is a nontrivial order-three element, this has the same trace on
`C3`.  Reduced tracial amalgamated free products over the finite-dimensional
algebras `L(C2)` and `L(C3)` then extend the traces successively.

This observation does **not** extend the intended conditional BCL
coefficient model.  It uses an independent BCL canonical trace with a
nontrivial root.  When the BCL idempotent is literally the selected
forbidden/bridge corner, perfect completeness sets that idempotent to zero
and therefore sends the root to `1`; it cannot match an injected A4
`3`-cycle.  Thus the trace construction proves only that abstract cyclic
amalgamation is not intrinsically inconsistent.  The payload-sensitive
compiler must instead use the conditional Fourier corner of
`agent-aggregate-escape-a4-bridge-lands-at-bcl-root-gate`.

Finally, attaching the complete finite Fourier-character hull does not alter
the analytic conclusion.  It gives more fixed finite subgroup windows, but
`orthogonal-steinberg-root-spectral-support-is-not-additive` shows that their
root supports need not be additive physical coefficient corners.  The A4
estimate begins exactly where `(BCK2)` begins and therefore cannot bypass
the common-source coefficient decoder.  This proves the claim.
