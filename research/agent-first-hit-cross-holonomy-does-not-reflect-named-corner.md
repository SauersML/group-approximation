---
rg: 2
id: agent-first-hit-cross-holonomy-does-not-reflect-named-corner
kind: claim
title: Cross-intertwiner phase matching does not reflect a BCS atom into the named free-compressor corner
distinct_from:
  agent-free-compressor-one-row-product-ring-no-go: that separates a payload root from a free-kernel diagonal inside exact Steinberg representations; this separates the original forbidden BCS sector from the entire root/free-compressor factor after adding the proposed cross-holonomy two-cell.
  bcs-atom-detects-its-e5-central-root: that asks directly for positive overlap of the BCS atom with the nontrivial root spectrum; this proves that a finite projective phase comparison cannot supply that overlap.
  agent-first-hit-one-schur-two-cell-is-regular-absorbed: that treats one predicate cell by itself; this includes a root packet and the wordized named-corner rows `P(x_i-b_i)=0` and shows why their multiplicity gauges do not synchronize.
  agent-free-compressor-minimal-nonretractive-corner: that proves the exact coefficient-module consequence after the physical corner is known; this shows that cross holonomy does not authenticate that coefficient-module corner in an abstract unitary representation.
---

**ESTABLISHED.**  Couple the forbidden Schur predicate packet to a finite
root/free-compressor packet using two stable-letter intertwiners.  Suppose the
closed two-cell compares their projective commutator phases and is intended to
force

```text
forbidden BCS type  ==>  nontrivial named root type.   (CHR1)
```

Also impose the rank-five root words encoding the coefficient rows

```text
P(x_i-b_i)=0                                           (CHR2)
```

and any finite list of root-internal Steinberg and free-HNN covariance rows.
If `(CHR2)` is imposed only through its ordinary Steinberg root wordization,
then the resulting relations do not imply `(CHR1)`.

Indeed, on a joint packet type the two stable letters have the form

```text
U=U_BCS tensor U_root tensor S,
V=V_BCS tensor V_root tensor T.                        (CHR3)
```

Let the packet commutator phases be

```text
U_BCS V_BCS=zeta_BCS V_BCS U_BCS,
U_root V_root=zeta_root V_root U_root.                 (CHR4)
```

The two-cell `UV=VU` imposes only

```text
S T=(zeta_BCS zeta_root)^(-1) T S.                    (CHR5)
```

It does not impose `zeta_BCS zeta_root=1`.  Every finite phase in `(CHR5)`
has a finite Weyl multiplicity representation after a fixed amplification.

For the binary Schur cell there is an explicit defect-zero enemy.  Choose a
forbidden BCS simple, so `zeta_BCS=-1`; represent the entire Steinberg/root
factor trivially, so `zeta_root=1` and every root word in `(CHR2)` and every
root-internal relation is the identity; and take `S,T` to be one Pauli
anticommuting pair.  Then `(CHR5)` holds exactly.  The free compressor and its
HNN letter may be put in an independent finite-dimensional representation
(in particular the trivial one whenever only existence of a bad marked model
is needed).  The BCS packet still has

```text
J=-I,
forbidden mass>0,
named root carrier=0,                                  (CHR6)
```

while all cross-holonomy and wordized corner rows have zero defect.

The named-corner coefficient theorem is not contradicted.  In an honest
coefficient module, `(CHR2)` says that `x_i` and `b_i` agree on `PH`, and the
stable HNN corner then has the finite packet rank contradiction of
`agent-free-compressor-minimal-nonretractive-corner`.  In an abstract unitary
representation with trivial roots, `(CHR2)` merely says that one already
trivial root word is trivial.  It supplies no physical Hilbert projection
`PH` and no equality of multiplicity operators.

Consequently the cross two-cell cannot replace either
`bcs-atom-detects-its-e5-central-root` or the density-compatible decoder in
`hs-steinberg-bcs-corner-kernel-is-linear-sofic`.  If those decoders are
assumed, the named-corner rows alone already kill the selected carrier and
the projective two-cell is redundant.  Using the two-cell to prove the
decoder is circular because `(CHR5)` leaves precisely the multiplicity gauge
which the decoder must eliminate.

DERIVATION
agent-first-hit-cross-holonomy-does-not-reflect-named-corner via agent-first-hit-cross-holonomy-split-model-proof

