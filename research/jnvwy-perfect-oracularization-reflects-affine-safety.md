---
rg: 2
id: jnvwy-perfect-oracularization-reflects-affine-safety
kind: claim
title: Perfect JNVWY oracularization reflects affine safety back to the original verifier
distinct_from:
  jnvwy-perfect-answer-reduction-reflects-affine-safety: that coarse-grains exact low-degree proof atoms to oracle answer pairs; this forgets the oracle joint refinement and returns to the two original question measurements.
  jnvwy-low-degree-pcp-reflects-affine-unsafety: that follows one chosen honest support forward through oracularization and answer reduction; this works backward from every affine-safe perfect oracularized model.
---

**ESTABLISHED.**  Let `V` be a JNVWY normal-form verifier and `V^ora` its
typed oracularization from Section 9 of arXiv:2001.04383v3.  In the
tensor-product, commuting-operator, or faithful-tracial model,

```text
V^ora has a perfect model with every positive answer support affine-safe
    =>
V has a perfect model with every positive answer support affine-safe.  (OAR1)
```

The source measurements are the two marginals of the oracle PVM.  Perfect
oracle--isolated consistency makes these marginal identities exact, so the
oracle atom at `(a,b)` is their product and has exactly the same positive
trace support as the reconstructed source answer pair.  An odd rejected xor
of source pairs would therefore give, on the oracle self-loop, an odd xor of
positive diagonal oracle answers rejected by the oracle game check.  This
contradicts affine safety.  The proof is
`jnvwy-oracle-marginals-reflect-odd-xor-support-proof`.
