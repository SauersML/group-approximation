---
rg: 2
id: qutrit-line-hnn-router-cannot-carry-heisenberg-shift
kind: claim
title: The full-source line router cannot also transport the native Heisenberg shift
artifacts:
  - research/qutrit-line-hnn-heisenberg-commutator-proof.md
distinct_from:
  qutrit-line-hnn-router-has-full-source-but-coincident-range: that constructs the full-source phase polars and leaves their coincident target occurrences to be distinguished; this excludes the shortest ordinary-word attempt to distinguish them.
  qutrit-jacobson-central-line-twist-is-similarity-impossible: that rules out the line twist inside the Jacobson matrix host by permutation rank; this works in any overgroup and uses the Heisenberg commutator after the external line twist has been adjoined.
---

Let `K=<j,x,z>` be the order-twenty-seven qutrit Heisenberg subgroup,
with

```text
[x,z]=j,        j central in K.
```

Suppose an overgroup contains a line-router element `U` satisfying

```text
U^(-1) z U=j^(-1).                                     (QHC1)
```

Then

```text
U^(-1)xU notin C_G(j).                                  (QHC2)
```

In particular, `U^(-1)xU` cannot be prescribed to be any element of the
finite qutrit packet, because that packet centralizes `j`. More generally,
it cannot be prescribed to any actor in a chosen target subgroup which
centralizes `j`.

Thus the native phase shifter `x` cannot be carried across the HNN edge
as a finite-packet label. Imposing such a relation collapses `j` to the
identity and annihilates the marked central-character projection `q`.
The shortest apparent closure which would compare the coincident polar
ranges `W_0,W_1` is therefore algebraically incompatible with retaining the
qutrit cell.

A surviving joint relation must send the conjugate of `x` to an element
which genuinely fails to commute with `j`. In the present Leavitt/Jacobson
lane that means a second noncentral infinite occurrence, not a finite
Clifford or qutrit-head attachment.
