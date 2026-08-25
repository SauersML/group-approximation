---
rg: 2
id: jnvwy-positive-perfect-proof-atoms-have-boolean-input-cubes
kind: claim
title: Every positive perfect JNVWY proof atom is Boolean on its two source-answer cubes
distinct_from:
  jnvwy-perfect-answer-reduction-exactly-reflects-source-atoms: that extracts exact low-degree proof atoms and decodes each one to an accepted source pair; this proves the additional source-specific Booleanity which makes that decoding odd-additive.
  jnvwy-exact-proof-atom-decoder-is-not-affine: that correctly observes that the abstract decoding map is nonadditive on arbitrary low-degree polynomials, but leaves this Booleanity alternative open; the explicit padded succinct-decider clauses close it on every everywhere-accepted proof atom.
  jnvwy-low-degree-pcp-reflects-affine-unsafety: that follows honest canonical source encodings forward; this applies to arbitrary positive proof atoms in an arbitrary perfect answer-reduced model.
---

**ESTABLISHED.**  In the exact proof-table decomposition of any perfect
tensor-product, commuting-operator, or faithful-tracial strategy for the
JNVWY answer-reduced verifier, let

```text
Pi=(g_1,...,g_5,c_0,...,c_m')                          (PBC1)
```

be a nonzero global atom over one source oracle question-pair.  Then

```text
g_1(y),g_2(y) in {0,1}  for every y in {0,1}^m.       (PBC2)
```

Thus the Boolean decoding of JNVWY Section 3.3 is just restriction on every
positive perfect atom:

```text
Dec(g_i)=g_i|_{ {0,1}^m },  i=1,2.                    (PBC3)
```

In particular it is odd-additive on positive atoms whenever their proof
tables are added over the characteristic-two field.

The proof is specific to the literal `PaddedSuccinctDecider` used in JNVWY,
not to an arbitrary decoupled PCP.  It is given in
`jnvwy-padded-succinct-clauses-force-proof-atom-booleanity-proof`.
