---
rg: 2
id: bcv-halt-completeness-has-computable-readable-factor-bound
kind: claim
title: BCV HALT completeness has a computable readable-factor bound independent of halting time
refuted_by:
  - bcv-no-computable-perfect-halt-readable-bound
distinct_from:
  bcv-halt-readable-finite-orbit-does-not-transfer-to-gap-irs: that proves each individual HALT strategy has some finite readable orbit after its halting time is known; this asks for one total computable bound from the machine description alone.
  bounded-readable-factor-zirs-computable-upper-hierarchy: that proves effective compactness once an integer atom bound is supplied; this asks the BCV completeness construction to supply that bound uniformly.
  perfect-gap-zpc-has-finite-readable-translate-algebra: that asks directly for a specially chosen NONHALT gap witness with some finite factor; this was a proposed HALT-side premise for a restricted diagonalization.
---

**REFUTED.** There is no total computable function `B` on encodings of
Turing machines such that, whenever `M` halts, the Bowen--Chapman--Vidick
tailored game `G_M` has some perfect finite-dimensional ZPC strategy with

```text
dim D_infinity <= B(M).                                  (BHB1)
```

The obstruction is not limited to BCV's chosen completeness strategy.
At every pre-halting fixed-point level, the exact inverse of the complete
Compression wrapper forces a fresh Pauli packet while retaining the decoded
tail readable algebra. Lemma 2.59 also preserves the sampler graph and
answer lengths at every level; that graph is the tensor of a detyped
sampler and is bipartite away from its common zero-answer anchor. Hence the
double-cover decoder descends at every recursive handoff.

If `T_0=C`, `T_(j+1)=2^(T_j)`, and
`h=min{j:T_j>=N}` for halt time `N`, every perfect strategy satisfies

```text
dim D_infinity
  >= product_(0<=j<h) 2^(2^(lambda(M) T_j))
  >= 2^h.
```

A proposed computable `B(M)` would let one simulate `M` only to the
computable level
`T_(floor(log_2(max(1,B(M))))+1)`; failure to halt by then would certify
nonhalting, deciding HALT.

The theorem and full sampler-support proof are
`bcv-no-computable-perfect-halt-readable-bound` and
`bcv-arbitrary-perfect-halt-readable-diagonal-proof`. This refutation
closes that conditional route to a finite-readable NONHALT gap. It does not
supply such a gap by another method and does not settle existence of a
nonhyperlinear group.
