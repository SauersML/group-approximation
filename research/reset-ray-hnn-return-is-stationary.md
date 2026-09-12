---
rg: 2
id: reset-ray-hnn-return-is-stationary
kind: claim
title: HNN transport of the balanced Schur child ray is exactly stationary
distinct_from:
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that gives the general type-preservation obstruction; this computes the precise reset ray and the missing surplus for the proposed violation atlas.
  branch-flip-pauli-extraction-cancels-schur-surplus: that loses the surplus by adjoining the flip; this loses it by returning the balanced child chart through a type-preserving HNN edge.
---

Use the notation of `symmetrized-reset-collapses-schur-flow-to-one-ray` and
assume `K_1>0`.  On the scalar ray with parameter `n`, the full-packet and
`Q`-child total multiplicities are

```text
m_B=(2K_1+4K_0)n,
m_Q=4(K_0+K_1)n,
m_Q-m_B=2K_1 n>0.                                      (RHS1)
```

Every one of the `2^(k+1)` genuine child types has multiplicity `2n`.
An HNN edge transporting the complete corrected child chart to the next
balanced reset preserves each of those multiplicities.  Hence its next scalar
parameter is exactly

```text
n_(next)=n.                                             (RHS2)
```

The next full-packet total is again `m_B`, not the previous `m_Q`.  Therefore
a pure reset-plus-HNN loop cannot satisfy the zero-error return inequality

```text
a_(next)>=c=m_Q
```

on a nonzero ray.  Its deficit is exactly the Schur surplus `2K_1n`.

Thus corrected-center balance and HNN transport solve selector renewal but do
not solve multiplicity return.  Any viable version of
`reset-schur-bcs-branching-atlas` must add a genuinely non-type-preserving
operation—a proper corner, one-sided compressor, or projective channel—between
the returned child chart and the next full-packet scale.  Calling the HNN edge
itself a return would repeat the stationary-flow error.

