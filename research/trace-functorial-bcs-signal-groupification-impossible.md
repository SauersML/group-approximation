---
rg: 2
id: trace-functorial-bcs-signal-groupification-impossible
kind: claim
title: The self-referential BCS signal cannot be groupified by any trace-functorial exact decoder
distinct_from:
  finite-selector-gadget-induction-barrier: that uses induction of characters to rule out deleting nonlinear selector sectors with a finite group; this uses the regular trace of every discrete group to rule out any exact decoder preserving the marked signal on all tracial representations.
  multiplicity-surplus-is-blind-to-the-non-ce-input: that refutes a compiler which remembers only a scalar forbidden-mass gap; this refutes a compiler which is too functorial and therefore also decodes the regular representation.
---

Let `(B_*,D)` satisfy `(SBS1)--(SBS2)`. There do not exist a group `Gamma`, a
nonidentity word `w in Gamma`, a constant `c>0`, and a construction assigning
to every tracial state `tau` on `C^*(Gamma)` a perfect strategy `S_tau` for
`B_*` such that

```text
phi_(S_tau)(D) >= c tau((w-1)^*(w-1)).                            (TFG)
```

In particular, a successful version of
`hs-groupify-self-referential-bcs-signal` cannot arise from an exact
star-algebra homomorphism or any decoder continuous and functorial for all
tracial representations. It must use a genuinely finite-dimensional feature
such as integral packet multiplicity, rank, determinant, or a quantitative
rounding theorem unavailable in the regular representation.
