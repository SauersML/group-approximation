---
rg: 2
id: hyperbolic-compression-centralizer-rigidity-proof
kind: route
title: Reverse the inclusion onto the centralizer, then apply the finite-compression lemma
target: hyperbolic-compression-centralizer-rigidity
requires:
  - hyperbolic-nonelementary-centralizer-finite
  - finite-infranormal-subgroup-is-normal
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Centralizing reverses inclusions.  From `tΓt^(-1) <= Γ`,

```text
C_G(Γ) <= C_G(t Γ t^(-1)) = t C_G(Γ) t^(-1),
```

the equality being conjugation of centralizers.  Rewriting,

```text
t^(-1) C_G(Γ) t <= C_G(Γ),
```

so `t^(-1)` lies in the compression semigroup `P_K` of `K = C_G(Γ)`.

By `hyperbolic-nonelementary-centralizer-finite`, `K` is finite.  By
`finite-infranormal-subgroup-is-normal`, `P_K = N_G(K)` — a compressor of a
finite subgroup normalizes it, since conjugation preserves cardinality and
turns the inclusion into equality.  Hence `t^(-1)`, and therefore `t`,
normalizes `K`, which is the asserted equality.

For the commutator statement: `c ∈ C_G(Γ)` gives
`d = tct^(-1) ∈ tC_G(Γ)t^(-1) = C_G(Γ)`, so `d` commutes with every `a ∈ Γ`;
then `a d a^(-1) = d` and the iterated commutator is `[d,d] = 1`.

**Where the two halves come from.**  The finiteness is hyperbolic geometry and
is new to this graph.  The normalization is the lemma this corpus already
proved for the Kun--Thom compression semigroup on 2026-08-14, applied to a
different finite subgroup.  The external attempt this node ingests proves the
combined statement directly by a cardinality argument; that argument is
literally the second half, so the route reuses the existing node rather than
restating it.
