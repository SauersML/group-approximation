---
rg: 2
id: universal-block-return-violates-the-regular-firewall
kind: claim
title: A fixed group-algebra block linearization cannot be the trace-cyclic return cell
distinct_from:
  regular-trace-blocks-exact-local-predicate-return: that treats forbidden Boolean atoms and arbitrary exact tracial payments; this directly audits the two cyclic products required by the single-triangle actuator, including matrix block and Steinberg linearizations.
  trace-cyclic-rank-mismatch-checksum: that proves the desired finite-matrix scalar checksum once two returned products are decoded; this proves that those products cannot be fixed universal group-algebra identities.
  single-triangle-trace-cyclic-return-cell: that permits a genuinely finite-dimensional-only decoder; this rules out the tempting functorial implementations but does not rule out such a decoder.
---

Let `Gamma` be a group and let `E,H,X,Y` be fixed matrices over
`C[Gamma]`, with `E,H,E-H` projections in the left regular representation
and `0!=H<=E`.  There cannot be universal identities

```text
YX=E,                    XY=E-H                         (UBR1)
```

in every unitary representation of `Gamma`.  More generally, there cannot
be a tracially functorial estimate

```text
|tau(YX)-tau(E)|+|tau(XY)-tau(E-H)| <= omega(def),     (UBR2)
```

with `omega(0)=0`, valid for every finite tracial representation of the
presentation, including matrix amplifications.

Indeed, apply `(UBR1)` or `(UBR2)` at zero defect in
`M_n(L(Gamma))`.  Cyclicity gives

```text
tau(YX)=tau(XY),
```

and hence `tau(H)=0`.  Faithfulness of the canonical trace on the positive
projection `H` gives `H=0`, a contradiction.

Therefore none of the following can close the single-triangle actuator by
itself:

- a Julia/block-unitary dilation whose block equations are consequences of
  the group relators;
- a Steinberg matrix linearization which yields the two products as fixed
  group-algebra identities;
- a literal Toeplitz/Cuntz proper-corner relation; or
- fixed finite-packet exactification followed only by operations valid in
  arbitrary finite tracial von Neumann algebras.

The exact HALT Hilbert-hotel representation is consistent only if the return
estimate is obtained by a step that is unavailable in `L(Gamma)`.  Thus at
least one load-bearing inference must use finite matrix coordinates: integer
multiplicity, finite rank, determinant on an extensive family of bounded
blocks, or an equivalent non-tracial-functorial compactness failure.  A
fixed block linearization does not provide that inference; it merely hides
the regular-representation contradiction in notation.

