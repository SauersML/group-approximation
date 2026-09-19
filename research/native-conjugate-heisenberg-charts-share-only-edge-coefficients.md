---
rg: 2
id: native-conjugate-heisenberg-charts-share-only-edge-coefficients
kind: claim
title: Distinct native conjugates of the Heisenberg packet share only edge-supported coefficients
distinct_from:
  root-block-piecewise-transport-cannot-host-nonce-bcs: that confines every context to one fixed finite root algebra; this permits different conjugate packet charts and computes their exact overlap inside the affine-Leavitt amalgam.
  packet-retraction-evaluates-hecke-collision-atlas: that assumes an ambient retraction to the packet; the affine-Leavitt Heisenberg amalgam has no such retraction in the selected type, and this instead uses reduced-word support.
  affine-leavitt-source-saturated-reynolds-checksum: that seeks a normalized-HS Reynolds return from the full Leavitt coefficient system; this is an exact algebraic obstruction before any Reynolds operator or microstate is introduced.
---

Write the selected odd corner as in `(OHM1)`:

```text
P=A *_D M,
A=C[Gamma_A],       D=C[<w>],       M=M_p(C).           (NCH1)
```

Use the concrete realization inherited from the group amalgam, so `M` is
`e_chi C[H_p]e_chi`.  Let `a` be a group element of `Gamma_A` with
`a notin <w>`.  If

```text
x,y in M,                a x a^(-1)=y in P,             (NCH2)
```

then

```text
x in D,                 y in D.                         (NCH3)
```

Equivalently, a coefficient outside the cyclic edge algebra cannot belong
both to the base Heisenberg packet chart and to a distinct chart conjugated
through the native vertex.  More generally, after translating two charts,
the same conclusion applies whenever their relative transporter is a
native-vertex word outside the edge group.

Thus a signed-Hecke atlas cannot be obtained by placing each finite context
PVM in a literal conjugate of the one `M_p` Heisenberg block and identifying
non-edge marginals between those charts.  Such an equality either keeps the
charts in the same edge coset or forces the shared marginal into `D`.
The load-bearing atlas must use genuinely multi-piece Hecke projections with
alternating support across the two vertex algebras (or a different
non-Bass--Serre operation).  The odd character selector and literal packet
conjugation alone do not supply global BCS holonomy.

This does not exclude an atlas whose relevant projections themselves have
alternating reduced-word support.  It identifies that multi-piece support,
not another finite packet conjugate, as the minimal exact construction left
inside `(NCH1)`.
