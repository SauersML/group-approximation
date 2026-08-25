---
rg: 2
id: dfnqxy-halt-completeness-support-is-not-canonically-specified
kind: claim
title: The published DFNQXY HALT completeness support is not a canonically specified object
distinct_from:
  jnvwy-low-degree-pcp-reflects-affine-unsafety: that proves a universal support implication through the two early answer reductions; this audits the quantifier and witness choices at the source of that implication.
  dfnqxy-answer-reduction-does-not-preserve-affine-safe-support: that gives a different verifier for which the final transformation has an unsafe honest support; this says the cited HALT theorem itself does not select one support whose safety can be inspected.
  dfnqxy-pcpp-contract-allows-nonlinear-proof-views: that changes an admissible PCPP to prove the abstract contract is insufficient; this reads the existential choices left open in the actual primary constructions.
---

**ESTABLISHED SOURCE AUDIT.**  The phrase "the positive support of the
published honest HALT strategy immediately before the final Hadamard-PCPP
reduction" does not denote a uniquely specified finite object in the
primary construction.

DFNQXY Theorem 6.10 starts with the existential statement that there is an
`MIP* [poly,poly]` protocol `V` for an arbitrary language in `RE`; it does
not select a particular verifier from the JNVWY construction.  It then
applies Theorem 6.2 twice.  The completeness clause of Theorem 6.2 states
only that a value-one strategy exists.  Its proof delegates the
completeness construction to the low-degree answer reduction of JNVWY and
Natarajan--Zhang and does not fix a joint section of the proof witnesses
over all positive source outcomes.

Even after one elects to instantiate `V` by the explicit JNVWY HALT
verifier, no canonical support is selected.  JNVWY Theorem 12.6 obtains the
finite-dimensional HALT strategy by the downward existential induction in
Claim 12.7: a value-one strategy at level `2^n` implies existence of one at
level `n`.  Inside the answer-reduction completeness proof, JNVWY Theorem
10.25 chooses satisfying strings `u_3,u_4,u_5` and certificate polynomials
`c_1,...,c_m'` by existence, and Section 10.6 classically postprocesses each
measured source outcome using such a proof.  Neither theorem specifies a
single simultaneous rule for these choices throughout the recursive HALT
strategy.

Therefore the primary papers establish

```text
HALT => there exists a value-one finite-dimensional strategy,            (HCS1)
```

but they do not establish either of the support-refined statements

```text
HALT => there exists such a strategy with affine-safe supports,           (HCS2)
HALT => every completeness strategy produced by the reductions is safe.  (HCS3)
```

Nor do they provide enough chosen witness data to falsify `(HCS2)` by a
finite support enumeration.  This is a quantifier gap, not merely missing
notation.  To close the Culf--Mastel/Fano-cap seam one must now do one of
the following:

1. specify a coherent chain of HALT completeness strategies and PCP proof
   sections and prove its local supports affine-safe;
2. prove the stronger universal statement `(HCS3)`; or
3. prove that every possible chain has an affine-unsafe support.

By `jnvwy-low-degree-pcp-reflects-affine-unsafety` and
`hadamard-pcpp-reflects-affine-unsafety`, a source violation found under
option 3 survives every published answer-reduction layer.  The present
audit does not claim such a violation or a safe section; it prevents an
existence-only completeness theorem from being cited as either one.
