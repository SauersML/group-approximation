---
rg: 2
id: mf-vs-tracial-radical-strict-gap
kind: claim
title: The MF radical is strictly smaller than the universal tracial-shadow radical
distinct_from:
  hs-invisibility-inflation-no-go: That claim shows normalized-HS invisibility of a whole group is compatible with faithfulness; this one exhibits a single explicit element that is universally tracially invisible yet detected by a faithful corona representation, separating the two radicals of one group.
  corona-hs-radical-is-finite-residual: That claim computes the tracial-shadow set of one specific non-MF group; this one shows the inclusion Rad_MF <= tracial shadow is strict on an MF group with compression data.
  universal-mf-quotient: That claim constructs the universal MF quotient of every countable group; this one separates the MF radical from the tracial-shadow radical on a specific group, so the two reflection functors differ.
artifacts:
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
---

Let `R_{infty->2}(G)` be the universal tracial shadow: elements killed in
the normalized-HS ultraproduct of every operator-norm almost
representation of `G`.  Always `Rad_MF(G) <= R_{infty->2}(G)`.  The
inclusion is STRICT in general: for `H` residually finite with a strict
one-sided compression `t L t^{-1} < L` of a finitely generated Kazhdan
subgroup `L`, the wreath product `W_Z = Z^(H/tLt^{-1}) semidirect H`
satisfies

```text
Rad_MF(W_Z) < R_{infty->2}(W_Z),
```

with strictness witnessed by the explicit compression commutator
`[g, c]`, `g in L \ tLt^{-1}`, `c` the root lamp.

**Consequences.**  Universal tracial invisibility is genuinely weaker than
MF invisibility: some mechanism bridging the operator-norm/normalized-HS
gap (a corner, or the normal-(T) hypothesis of the abstract invisibility
theorem, or a self-normalized scale) is mathematically necessary, not an
artifact of the current proofs.  This is the sharp no-go behind
`hs-invisibility-inflation-no-go`, now witnessed inside a single group by
a single element.

This strict gap is the non-circularity control for
`single-shadow-word-saturation-compiler`: its input can occur in an MF group,
and only saturation plus the Kazhdan detector turns it into MF failure.
