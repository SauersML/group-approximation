---
rg: 2
id: jnvwy-perfect-answer-reduction-reflects-affine-safety
kind: claim
title: Perfect JNVWY answer reduction reflects affine safety back to the source verifier
distinct_from:
  jnvwy-low-degree-pcp-reflects-affine-unsafety: that propagates an unsafe list through every honest choice of completeness proofs; this runs backward from an arbitrary perfect answer-reduced model and does not assume honest or canonical proof tables.
  jnvwy-perfect-answer-reduction-exactly-reflects-source-atoms: that decodes a perfect source model but does not by itself preserve odd sums; this adds the source-specific Booleanity needed for exact odd-additivity.
  jnvwy-positive-perfect-proof-atoms-have-boolean-input-cubes: that proves atomwise Booleanity; this applies it to every odd list of positive atoms and obtains support reflection.
---

**ESTABLISHED.**  For the literal JNVWY v3 answer reduction, let `V_AR` be
the answer-reduced verifier and `V` its source verifier.  In the
tensor-product, commuting-operator, or faithful-tracial model,

```text
V_AR has a perfect model with every positive answer support affine-safe
    =>
V has a perfect model with every positive answer support affine-safe.  (PAR1)
```

The source model is the exact atomwise coarse-graining from
`jnvwy-perfect-answer-reduction-exactly-reflects-source-atoms`.  The new
content is that this coarse-graining reflects odd-xor acceptance, even for
noncanonical proof-table atoms.  The proof is
`jnvwy-boolean-proof-atoms-reflect-odd-xor-support-proof`.
