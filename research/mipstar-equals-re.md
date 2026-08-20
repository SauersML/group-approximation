---
rg: 2
id: mipstar-equals-re
kind: claim
title: Entangled-prover interactive proofs decide exactly the recursively enumerable languages
artifacts:
  - research/artifacts/mipstar-re-ingestion-2026-08-20.md
distinct_from:
  mipstar-bcs-tracial-nonru-exists: that is the Paddock-Slofstra consequence, a finite BCS with a tracial but no R^U model; this is the complexity theorem it is derived from, and it mentions no algebra.
  zpc-irs-value-computable-upper-hierarchy: that is a computable decreasing hierarchy of upper bounds on the ZPC-IRS value; this is the undecidability statement that makes such hierarchies unable to converge to the entangled value.
  perfect-zpc-irs-quantum-gap-game: that is a finite tailored game separation obtained by combining TailoredMIP*=RE with a computable hierarchy; this is the underlying complexity characterization.
---

**Established by citation.**  Ji, Natarajan, Vidick, Wright and Yuen,
`MIP* = RE` (arXiv:2001.04383).  Their Corollary 12.10:

```text
MIP* = RE.
```

More precisely (their Theorem 12.9) there is a polynomial-time computable map
from Turing machines `M` to two-player one-round nonlocal games `G_M` such that

- if `M` halts on the empty input then `val*(G_M) = 1`, and moreover the value
  is attained by a finite-dimensional projective, consistent and commuting
  strategy;
- if `M` does not halt then `val*(G_M) <= 1/2`.

Consequently, for every `0 < eps < 1` it is undecidable to determine whether a
given nonlocal game has entangled value `1` or at most `1 - eps`, promised one
is the case.

**The consequences this repository actually uses.**  Undecidability of the
entangled value forces `C_qa != C_qc`, a negative answer to Tsirelson's problem,
and hence -- through Fritz and Junge et al., promoted to an equivalence by
Ozawa -- the failure of Connes' Embedding Conjecture.  Every node in this graph
that begins "by `MIP*=RE`" is consuming this theorem, including
`mipstar-bcs-tracial-nonru-exists`, `perfect-zpc-irs-quantum-gap-game` and
`non-ce-bcs-has-finite-dimensional-forbidden-mass-gap`.

**What it does not give, in the authors' own words.**  Their Section 1.3 lists
as an open question whether the counterexample "can eventually lead to a
construction of a group that is not sofic, or even not hyperlinear".  That
question is the goal `non-hyperlinear-group` of this program.  So the theorem
supplies a non-Connes-embeddable tracial von Neumann algebra but explicitly not
a group, and the gap between the two is exactly what this graph is trying to
close.
