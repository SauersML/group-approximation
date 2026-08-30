---
rg: 2
id: stw22-c-space-screening-from-local-lifts
kind: claim
title: Property C turns local weighted lifts into fibre-gap trace vanishing
distinct_from:
  stw22-finite-dimensional-colouring-from-local-lifts: that theorem pays one fixed d+1 colour cost; the present theorem replaces finite dimension by a sequence of disjoint refinements and makes the reciprocal replication costs summable.
  stw22-zero-dimensional-trivial-field-trace-continuity: that theorem selects one global weighted embedding into each corner; the present theorem needs only local weighted lifts and Haver's selective screenability.
  stw22-norm-fibre-gap-is-the-trace-obstruction: that theorem identifies the operator-algebraic obstruction; the present theorem supplies a broad topological sufficient condition which eliminates it for trivial factor fields.
artifacts:
  - research/artifacts/stw22-c-space-selective-screening-audit-2026-08-30.md
  - research/artifacts/stw22-c-space-open-graph-audit-2026-08-30.md
---

Let `X` be a compact metrizable `C`-space in the sense of Haver: for every
sequence `(U_n)` of open covers of `X`, there are pairwise disjoint families
`V_n` of open sets, with `V_n` refining `U_n`, such that

```text
union_n V_n
```

covers `X`.  Let `U` be an infinite-dimensional UHF algebra with unique
trace, and let `M` be the uniform tracial completion of
`C(X) tensor U`.  Assume `(LWCL)` from
`stw22-finite-dimensional-colouring-from-local-lifts` for closed subspaces
of `X`.

Then every fibre gap `K_x/J_x` has no nonzero bounded positive trace.
Consequently every tracial state on `M` is uniquely

```text
a |-> integral_X tau(a(t)) dmu(t)
```

for a probability measure `mu` on `X`, and is continuous for the uniform
`2`-norm.

Property `C` is used with a rapidly increasing sequence of replication
counts `(m_n)` satisfying

```text
sum_n 1/m_n < epsilon.                                  (CSP)
```

The `n`-th disjoint family carries `m_n` local weighted copies of its part
of a spectral cut.  If `g_n` is the corresponding central partition, then
every bounded positive trace `sigma` on the gap satisfies

```text
m_n sigma(g_n c) <= ||sigma||.
```

Only finitely many families are needed in a germ neighbourhood of `x`, so

```text
sigma(c) <= ||sigma|| sum_n 1/m_n < epsilon||sigma||.
```

Arbitrariness of `epsilon` kills the trace.

Conditional on `(LWCL)`, this strictly extends the finite-covering-
dimensional gluing method at the topological level: compact metrizable
finite-dimensional spaces are `C`-spaces, as are standard strongly
countable-dimensional compacta, while property `C` also admits
infinite-dimensional examples.  No unconditional positive-dimensional
claim and no converse are asserted.  For this proof architecture the
relevant topological invariant is selective screenability of a sequence of
local weighted-lift covers, rather than a finite numerical dimension bound.

The all-degree purification theorem does not remove `(LWCL)` on a general
`C`-space.  Indeed, let

```text
F(a)={w in eR:w^*w=a}.
```

This multifunction has nonempty closed values in a common complete metric
space, is lower semicontinuous, is uniformly equi-`LC^k` for every finite
`k`, and every fibre is `k`-connected in every finite degree.  But the
available Uspenskij C-space theorem requires lower local constancy/open
graph.  For a pullback `Phi(x)=F(a(x))` and `w in Phi(x_0)`,

```text
{x:w in Phi(x)}={x:a(x)=a(x_0)}.
```

Thus lower local constancy fails wherever the weight field is not locally
constant; exact purification has a closed graph, not an open one.  Gutev,
[*Selections and Higher Separation Axioms*](https://arxiv.org/abs/1805.07638),
Theorem 6.5 and Questions 21--22, records this as precisely the open
selection boundary even for strongly countable-dimensional spaces and
then for paracompact `C`-spaces.  Consequently the conditional screening
statement above is the rigorous extension beyond finite dimension supplied
by this method; all-degree connectivity alone does not make it
unconditional.  The unconditional finite-dimensional theorem is
`stw22-finite-dimensional-trivial-field-traces`.  No failure of selection
for this special purification map is asserted.
