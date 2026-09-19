---
rg: 2
id: culf-mastel-rstar-has-no-private-tail-form
kind: claim
title: The fixed hard R-star family has no occurrence-private-tail normal form
distinct_from:
  culf-mastel-rstar-reduction-is-support-blind: that audits what the published classical homomorphisms preserve about support; this isolates and refutes the stronger occurrence-level freshness premise needed by the fiberwise selector.
  rstar-private-tail-instances-are-trivial: that is the general syntax theorem; this applies it to the fixed Culf--Mastel perfect-gap family.
  culf-mastel-rstar-halt-model-has-fano-cap-support: that remains an existence question for another perfect representation of the actual shared-variable instance; this only closes one proposed proof.
---

**ESTABLISHED FRESHNESS AUDIT.**  The fixed hard `R_*` family supplied by
Culf--Mastel cannot have the property that every final `R_*` occurrence has
one inherited/shared coordinate and three coordinates private to that
occurrence.  Such an instance would be classically satisfiable by
`rstar-private-tail-instances-are-trivial`, including on every nonhalting
input, contradicting the established constant soundness gap.

The paper's actual privacy statement is weaker.  Corollary 6.7 assumes

```text
W_i intersect W_j = V_i intersect V_j,                 (PTA1)
```

so the auxiliary variables introduced for different **source contexts** are
private from one another.  The relation `D_i` is then the Boolean form of a
whole `CSP(R_*)` gadget.  Its auxiliary variables may be reused among
several target occurrences inside that gadget, and a target occurrence may
contain several inherited or otherwise shared variables.  Theorem 6.8 and
the later subdivision steps state no one-shared-three-private normal form.

Therefore the fiberwise selector is a valid lemma for the hypothetical
syntax, but it cannot be performed independently on all target contexts in
the published hard family: replacing a reused auxiliary observable in one
occurrence also changes every other occurrence containing it.

Primary source: Culf--Mastel, *RE-completeness of entangled constraint
satisfaction problems*, arXiv:2410.21223v2, Corollary 6.7 and Theorem 6.8.
