# STW XXII: property C and summable selective screening

## Why finite dimension is stronger than necessary

The finite-dimensional proof uses a fixed `d+1` colour bound and obtains

```text
m sigma(c) <= (d+1)||sigma||.
```

Only the ratio between colour cost and replication count matters.  A
uniform finite colour bound is therefore unnecessary.

## Conditional property C replacement

Choose replication counts `m_n` so quickly increasing that
`sum 1/m_n` is arbitrarily small.  Assuming exact parametrized local
weighted lifting, the `2`-norm vanishing of a spectral cut at the fibre
point supplies, on a shrinking neighbourhood, local weighted lifts into
`m_n` orthogonal corners.  Haver's property `C` screens the
resulting sequence of covers into disjoint families.  Compactness leaves
only finitely many families in a germ neighbourhood.

The contribution of family `n` to a bounded trace is at most
`||sigma||/m_n`.  Summing and then making `sum 1/m_n` arbitrarily small
forces the trace to vanish.

## Topological boundary of the method

Conditional on local weighted corner lifting, the proof applies to compact
metrizable `C`-spaces, including all finite-dimensional and standard
strongly countable-dimensional compacta, and therefore reaches genuine
infinite-dimensional bases.  Its precise topological input is selective
screenability for the sequence of local weighted-lift covers.  The local
parametrized lifting hypothesis is independent analytic input and is not
deduced from sequential lower lifting.

Strongly infinite-dimensional compacta can fail property `C`; on such a
base this screening step may be unavailable.  Failure of property `C` is
only an obstruction to this proof architecture.  It does not produce a
bounded trace on a fibre gap, and no converse to the theorem is claimed.

## Status after the all-degree purification theorem

Uniform sphere fillings in every finite degree do not by themselves prove
the local weighted lifts assumed above.  Uspenskij's exact selection
theorem for C-spaces requires a lower locally constant/aspherical
multifunction.  For exact purification, a fixed `w` belongs to the fibre at
`x` exactly when `a(x)=w^*w`; hence singleton compact subsets of a fibre do
not persist when the weight varies.  The map is lower semicontinuous but
not lower locally constant.

Gutev, *Selections and Higher Separation Axioms*, Questions 21--22,
identifies selection from lower semicontinuity plus uniformly
equi-`LC^omega`, `C^omega` values as open already over strongly
countable-dimensional spaces and then over C-spaces.  Thus this node stays
conditional.  The exact theorem boundary is audited in
`research/artifacts/stw22-c-space-open-graph-audit-2026-08-30.md`; the
finite-covering-dimensional result is now unconditional in
`stw22-finite-dimensional-trivial-field-traces`.
