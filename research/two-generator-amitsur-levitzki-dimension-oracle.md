---
rg: 2
id: two-generator-amitsur-levitzki-dimension-oracle
kind: claim
title: Two free-algebra letters enumerate a nonzero polynomial killed by every finite matrix size
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
distinct_from:
  finite-trace-profile-net-is-dimension-free: that replaces all matrix dimensions by a compact space of bounded moments; this detects each actual dimension by a dimension-indexed polynomial identity.
  finite-selector-gadget-induction-barrier: that concerns finite-group representation sectors; this is a countable free-algebra construction and asserts no finite presentability.
---

In `C<x,y>`, let

```text
u_j = x y^j x,
p_n = s_(2n)(u_1,...,u_(2n)),
```

where `s_m` is the alternating standard polynomial.  Then

```text
p_n != 0 in C<x,y> for every n>=1,                                (ALO1)

rho(p_d)=0 for every homomorphism rho:C<x,y> -> M_d(C).            (ALO2)
```

Consequently the countably presented unital algebra obtained by adjoining
two-sided inverses `q_n` for every `p_n` is nonzero but has no unital
finite-dimensional representation.

This is an exact dimension oracle: the program enumerates the same sequence in
every environment, while a `d`-dimensional environment triggers the `d`th
zero.  It is deliberately not called a finitely presented group obstruction.
The conversion from the countable associative-algebra relations to finitely
many unitary group relations with constant normalized-HS soundness is open.

Amitsur--Levitzki states that `M_d(C)` satisfies the standard identity of
degree `2d`.
